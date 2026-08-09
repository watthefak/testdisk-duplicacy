/*
    File: file_dupl.c

    Based on PhotoRec module template by Christophe GRENIER
    Made using garbage AI output and large amounts of electricity
*/

/*
   Recovers Duplicacy backup chunk files.

   File layout:
     HEADER = PRE_HEADER(9 bytes "duplicacy") + PADDING(6 random bytes) + MAGIC(8 bytes)
     ... file data ...
     FOOTER = MAGIC(8 bytes) + 2 random bytes

   Strategy:
     - header_check_dupl() matches the fixed PRE_HEADER at offset 0 and the
       fixed MAGIC at offset 15 (skipping the 6 random padding bytes between
       them, which are never compared).
     - data_check_dupl() is PhotoRec's standard mechanism for formats whose
       length isn't known from the header: it's called repeatedly as more of
       the file is read, with `buffer` centered on the current file_size
       position.

       MAGIC is NOT unique to the footer -- it also appears inside every
       header (PRE_HEADER + PADDING + MAGIC), so "first MAGIC found" is not
       by itself enough to identify a footer: it could equally be the start
       of the *next* recoverable file's header. PRE_HEADER, however, is
       unique and only ever occurs at a file's start (given).

       Because PRE_HEADER always precedes its own file's MAGIC by exactly
       PADDING_LEN bytes, a single left-to-right scan resolves the
       ambiguity with no backward lookback: whichever of the two patterns
       is encountered FIRST tells us which case we're in.
         - PRE_HEADER found first  => this is unambiguously the start of
           the next file's header (its own MAGIC, 15 bytes further in,
           doesn't need to be located at all). The current file has no
           footer within the scanned data; it ends here, bounded by the
           next header -- the same fallback PhotoRec normally uses when a
           format's true end can't be determined.
         - MAGIC found first (i.e. no PRE_HEADER occurred any earlier in
           the scan) => this MAGIC cannot belong to some other file's
           header, because if it did, that file's PRE_HEADER would
           necessarily have appeared earlier in this same left-to-right
           scan and would have been matched first. It is therefore the
           genuine footer.
       Both patterns are checked against what should be high-entropy
       (compressed/encrypted) chunk data, so incidental false matches
       inside real file content are effectively impossible.
     - file_check_size_max is the stock PhotoRec helper that truncates the
       recovered file to file_recovery->calculated_file_size once data_check
       returns DC_STOP.

   Buffer-boundary safety net:
     Each data_check_dupl() call only sees one finite `buffer` window; a
     position within ~8 bytes of that buffer's tail can't be verified
     within the same call (not enough trailing bytes present to compare
     the full 8/9-byte pattern). If a later call's window has already
     advanced past that absolute position by the time more data arrives,
     it would never get a complete check -- a real, if narrow, risk on a
     tool built to search across many gigabytes.

     To close this, the last DUPL_CARRY_LEN (32) bytes examined by each
     call are cached (dupl_carry[]) together with their absolute file
     offset (dupl_carry_abs_start). The next call first re-checks any
     match that starts within that cached tail and extends into the new
     buffer ("seam check"), using the recorded absolute offsets --  not
     assumptions about how the engine slides its window -- to place any
     match found there. If the new window doesn't actually reach back
     far enough to be contiguous with the cached tail (which would mean
     an honest gap in what any buffer ever presented), the seam check is
     simply skipped rather than risk splicing unrelated bytes together.
     The carry is per-file (keyed to the file_recovery pointer) and is
     cleared whenever a different file starts being tracked or once a
     match has been resolved.
*/

#if !defined(SINGLE_FORMAT) || defined(SINGLE_FORMAT_dupl)
#ifdef HAVE_CONFIG_H
#include <config.h>
#endif
#ifdef HAVE_STRING_H
#include <string.h>
#endif
#include <stdio.h>
#include "types.h"
#include "filegen.h"
#include "common.h"
#include "log.h"

/*@ requires valid_register_header_check(file_stat); */
static void register_header_check_dupl(file_stat_t *file_stat);

const file_hint_t file_hint_dupl= {
  .extension="dupl",
  .description="Duplicacy backup chunk",
  .max_filesize=600*1024*1024,   /* per spec: files can be up to 600MB */
  .recover=1,
  .enable_by_default=1,
  .register_header_check=&register_header_check_dupl
};

static const unsigned char dupl_pre_header[9] =
  { 'd','u','p','l','i','c','a','c','y' };

static const unsigned char dupl_magic[8] =
  { 0x00,0x00,0x00,0x00,0x63,0x00,0x01,0x00 };

#define DUPL_PADDING_LEN 6
#define DUPL_HEADER_LEN  (sizeof(dupl_pre_header) + DUPL_PADDING_LEN + sizeof(dupl_magic)) /* 23 */
#define DUPL_FOOTER_LEN  (sizeof(dupl_magic) + 2)                                          /* 10 */

#define DUPL_CARRY_LEN 32

/* Per-file carry state. Single-threaded assumption: PhotoRec's core scan
   loop calls data_check for one actively-tracked file at a time, so this
   is safe as ordinary static state, keyed to the owning file_recovery_t
   so a new/different file never sees a stale carry. */
static unsigned char          dupl_carry[DUPL_CARRY_LEN];
static unsigned int           dupl_carry_len = 0;
static uint64_t               dupl_carry_abs_start = 0;
static const file_recovery_t *dupl_carry_owner = NULL;

/*@
  @ requires file_recovery->data_check==&data_check_dupl;
  @ requires valid_data_check_param(buffer, buffer_size, file_recovery);
  @ terminates \true;
  @ ensures  valid_data_check_result(\result, file_recovery);
  @ assigns  file_recovery->calculated_file_size;
  @*/
static data_check_t data_check_dupl(const unsigned char *buffer, const unsigned int buffer_size, file_recovery_t *file_recovery)
{
  /* buffer[0 .. buffer_size) corresponds to absolute file offsets
     [window_start, window_start + buffer_size), where window_start is
     file_recovery->file_size - buffer_size/2 (PhotoRec keeps the buffer
     centered on the current read position). */
  const uint64_t window_start =
    (file_recovery->file_size > buffer_size/2)
      ? file_recovery->file_size - buffer_size/2
      : 0;

  if(dupl_carry_owner != file_recovery)
  {
    /* First call for this file (or a different file reusing this static
       state): nothing carried over from an unrelated recovery. */
    dupl_carry_len = 0;
    dupl_carry_owner = file_recovery;
  }

  /* Seam check: resolve any match that starts in the cached tail of the
     previous call and would extend into this call's buffer. Only trusted
     when the cached tail actually reaches (or overlaps) this call's
     window start -- i.e. no unseen gap between what the two calls'
     buffers ever covered. */
  if(dupl_carry_len > 0 && dupl_carry_abs_start + dupl_carry_len >= window_start)
  {
    unsigned char seam[DUPL_CARRY_LEN + 8];
    unsigned int extra = (buffer_size < 8 ? buffer_size : 8);
    unsigned int seam_len = dupl_carry_len + extra;
    unsigned int k;
    memcpy(seam, dupl_carry, dupl_carry_len);
    memcpy(seam + dupl_carry_len, buffer, extra);

    for(k = 0; k < dupl_carry_len; k++)
    {
      if(k + sizeof(dupl_pre_header) <= seam_len &&
         memcmp(&seam[k], dupl_pre_header, sizeof(dupl_pre_header)) == 0)
      {
        file_recovery->calculated_file_size = dupl_carry_abs_start + k;
        dupl_carry_len = 0;
        dupl_carry_owner = NULL;
        return DC_STOP;
      }
      if(k + sizeof(dupl_magic) <= seam_len &&
         memcmp(&seam[k], dupl_magic, sizeof(dupl_magic)) == 0)
      {
        file_recovery->calculated_file_size = dupl_carry_abs_start + k + DUPL_FOOTER_LEN;
        dupl_carry_len = 0;
        dupl_carry_owner = NULL;
        return DC_STOP;
      }
    }
  }

  /* Never search inside the header itself (bytes 15..23 of the file are
     the header's own copy of MAGIC and must not be mistaken for a footer). */
  {
    uint64_t search_from = window_start;
    if(search_from < DUPL_HEADER_LEN)
      search_from = DUPL_HEADER_LEN;

    if(search_from < window_start + buffer_size)
    {
      unsigned int i = (unsigned int)(search_from - window_start);
      /* Scan strictly left-to-right. At each position, check for
         PRE_HEADER (9 bytes) before checking for MAGIC (8 bytes) --
         whichever pattern is found at the smaller offset wins, which is
         exactly what distinguishes "next file's header" from "our
         footer" (see the block comment above the file for the full
         reasoning). */
      for(; i < buffer_size; i++)
      {
        if(i + sizeof(dupl_pre_header) <= buffer_size &&
           memcmp(&buffer[i], dupl_pre_header, sizeof(dupl_pre_header)) == 0)
        {
          file_recovery->calculated_file_size = window_start + i;
          dupl_carry_len = 0;
          dupl_carry_owner = NULL;
          return DC_STOP;
        }
        if(i + sizeof(dupl_magic) <= buffer_size &&
           memcmp(&buffer[i], dupl_magic, sizeof(dupl_magic)) == 0)
        {
          file_recovery->calculated_file_size = window_start + i + DUPL_FOOTER_LEN;
          dupl_carry_len = 0;
          dupl_carry_owner = NULL;
          return DC_STOP;
        }
      }
    }
  }

  /* No match yet: cache the tail of this buffer for the seam check on
     the next call, clipped so it never dips back into the header. */
  {
    unsigned int n = (buffer_size < DUPL_CARRY_LEN ? buffer_size : DUPL_CARRY_LEN);
    const uint64_t save_start = window_start + (buffer_size - n);
    if(save_start >= DUPL_HEADER_LEN)
    {
      memcpy(dupl_carry, buffer + (buffer_size - n), n);
      dupl_carry_len = n;
      dupl_carry_abs_start = save_start;
    }
    else
    {
      dupl_carry_len = 0;
    }
    dupl_carry_owner = file_recovery;
  }
  return DC_CONTINUE;
}

/*@
  @ requires buffer_size >= DUPL_HEADER_LEN;
  @ requires separation: \separated(&file_hint_dupl, buffer+(..), file_recovery, file_recovery_new);
  @ requires valid_header_check_param(buffer, buffer_size, safe_header_only, file_recovery, file_recovery_new);
  @ terminates \true;
  @ ensures  valid_header_check_result(\result, file_recovery_new);
  @*/
static int header_check_dupl(const unsigned char *buffer, const unsigned int buffer_size, const unsigned int safe_header_only, const file_recovery_t *file_recovery, file_recovery_t *file_recovery_new)
{
  if(buffer_size < DUPL_HEADER_LEN)
    return 0;
  if(memcmp(buffer, dupl_pre_header, sizeof(dupl_pre_header)) != 0)
    return 0;
  /* bytes [9,15) are the random PADDING and are intentionally not checked */
  if(memcmp(&buffer[sizeof(dupl_pre_header)+DUPL_PADDING_LEN], dupl_magic, sizeof(dupl_magic)) != 0)
    return 0;

  reset_file_recovery(file_recovery_new);
  file_recovery_new->extension = file_hint_dupl.extension;
  file_recovery_new->min_filesize = DUPL_HEADER_LEN + DUPL_FOOTER_LEN;
  if(file_recovery_new->blocksize >= DUPL_FOOTER_LEN)
  {
    file_recovery_new->data_check = &data_check_dupl;
    file_recovery_new->file_check = &file_check_size_max;
  }
  return 1;
}

static void register_header_check_dupl(file_stat_t *file_stat)
{
  register_header_check(0, dupl_pre_header, sizeof(dupl_pre_header), &header_check_dupl, file_stat);
}
#endif
