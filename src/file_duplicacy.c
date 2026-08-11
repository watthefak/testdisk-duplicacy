/*
    File: file_duplicacy.c

    Based on PhotoRec module template by Christophe GRENIER
    Made using garbage AI output and large amounts of electricity
*/

/*
   Recovers Duplicacy backup chunk files.

   File layout:
   HEADER = PRE_HEADER ("duplicacy", 9 bytes)
    + PADDING     (5 random bytes)
    + MAGIC       (8 fixed bytes)
-----------------------------
   22 bytes total
... up to ~600 MB of chunk data ...

   FOOTER = MAGIC (the SAME 8 fixed bytes as in the header)
    + 2 random trailing bytes
-----------------------------
   10 bytes total

*/

#if !defined(SINGLE_FORMAT) || defined(SINGLE_FORMAT_duplicacy)
#ifdef HAVE_CONFIG_H
#include <config.h>
#endif
#include <stdio.h>
#ifdef HAVE_STRING_H
#include <string.h>
#endif
#include "types.h"
#include "filegen.h"

static void register_header_check_duplicacy(file_stat_t *file_stat);
static int header_check_duplicacy(const unsigned char *buffer, const unsigned int buffer_size,
    const unsigned int safe_header_only, const file_recovery_t *file_recovery, file_recovery_t *file_recovery_new);
static data_check_t data_check_duplicacy(const unsigned char *buffer, const unsigned int buffer_size,
    file_recovery_t *file_recovery);

const file_hint_t file_hint_duplicacy= {
  .extension="dup",
  .description="Duplicacy backup chunk",
  .min_header_distance=0,
  .max_filesize=600*1024*1024,
  .recover=1,
  .enable_by_default=1,
  .register_header_check=&register_header_check_duplicacy
};

static const unsigned char duplicacy_pre_header[9]=
  { 'd','u','p','l','i','c','a','c','y' };
#define PRE_HEADER_SIZE 9

#define PADDING_SIZE 5

static const unsigned char duplicacy_magic[8]=
  { 0x00, 0x00, 0x00, 0x00, 0x63, 0x00, 0x01, 0x00 };
#define MAGIC_SIZE 8

/* PRE_HEADER + PADDING + MAGIC */
#define HEADER_SIZE (PRE_HEADER_SIZE + PADDING_SIZE + MAGIC_SIZE)   /* 22 */

/* MAGIC + 2 random trailing bytes */
#define FOOTER_TRAILING_SIZE 2
#define FOOTER_SIZE (MAGIC_SIZE + FOOTER_TRAILING_SIZE)              /* 10 */

static void register_header_check_duplicacy(file_stat_t *file_stat)
{
  register_header_check(0, duplicacy_pre_header, PRE_HEADER_SIZE, &header_check_duplicacy, file_stat);
}

static int header_check_duplicacy(const unsigned char *buffer, const unsigned int buffer_size,
    const unsigned int safe_header_only, const file_recovery_t *file_recovery, file_recovery_t *file_recovery_new)
{
  /* register_header_check() only matched the fixed "duplicacy" text for
   * us; we still need to confirm the magic sits 5 bytes after it before
   * accepting this as a real header. */
  if(buffer_size < HEADER_SIZE)
    return 0;
  if(memcmp(&buffer[PRE_HEADER_SIZE + PADDING_SIZE], duplicacy_magic, MAGIC_SIZE) != 0)
    return 0;

  reset_file_recovery(file_recovery_new);
  file_recovery_new->extension = file_hint_duplicacy.extension;
  /* Smallest possible valid file: header immediately followed by footer. */
  file_recovery_new->min_filesize = HEADER_SIZE + FOOTER_SIZE;
  file_recovery_new->data_check = &data_check_duplicacy;
  file_recovery_new->file_check = NULL;
  return 1;
}

/*
 * Returns 1 if the bytes ending right before buffer[magic_offset] spell
 * out "duplicacy" + 5-byte padding, i.e. buffer[magic_offset] is really
 * the start of a NEW header rather than this file's footer.
 */
static int magic_is_new_header(const unsigned char *buffer, unsigned int magic_offset)
{
  if(magic_offset < PRE_HEADER_SIZE + PADDING_SIZE)
    return 0; /* not enough preceding data in this window to tell; treat as footer */
  return (memcmp(&buffer[magic_offset - PADDING_SIZE - PRE_HEADER_SIZE],
        duplicacy_pre_header, PRE_HEADER_SIZE) == 0);
}

static data_check_t data_check_duplicacy(const unsigned char *buffer, const unsigned int buffer_size,
    file_recovery_t *file_recovery)
{
  const unsigned int mid = buffer_size / 2;
  /* Start scanning a bit before the halfway point of the sliding window
   * so a MAGIC (or a preceding "duplicacy") that straddles the boundary
   * between the previous read and this one is still seen intact. */
  const unsigned int start = (mid > HEADER_SIZE) ? (mid - HEADER_SIZE) : 0;
  unsigned int i;

  for(i = start; i + MAGIC_SIZE <= buffer_size; i++)
  {
    if(memcmp(&buffer[i], duplicacy_magic, MAGIC_SIZE) != 0)
      continue;

    if(magic_is_new_header(buffer, i))
    {
      /* This magic belongs to a NEW header: a later chunk has overwritten
       * the rest of the file we're currently recovering. End the current
       * file right before that new header so PhotoRec's normal header
       * scan can pick the new chunk up on its own. */
      const unsigned int new_header_offset = i - PADDING_SIZE - PRE_HEADER_SIZE;
      file_recovery->file_size = file_recovery->file_size + ((int64_t)new_header_offset - (int64_t)mid);
      return DC_STOP;
    }
    else
    {
      /* Genuine footer: MAGIC + 2 trailing bytes. */
      file_recovery->file_size = file_recovery->file_size + ((int64_t)i - (int64_t)mid) + FOOTER_SIZE;
      return DC_STOP;
    }
  }
  return DC_CONTINUE;
}
#endif
