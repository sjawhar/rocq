/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

/* Measurement only (mainProfile.mli): the wall clock, the page faults, and
   the time the garbage collector takes, counted by OCaml 4.14's GC timing
   hooks. None of these functions allocates on the OCaml heap. */

#define CAML_INTERNALS
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/misc.h>

#include <stdint.h>
#include <time.h>
#include <sys/time.h>
#include <sys/resource.h>

static int64_t mainprofile_clock_ns(void)
{
  struct timespec ts;
  if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
  return (int64_t) ts.tv_sec * 1000000000 + (int64_t) ts.tv_nsec;
}

/* The GC time so far, in ns. Only the outermost of nested phases counts
   (a compaction in a major slice empties the minor heap). */
static int64_t gc_total_ns = 0;
static int64_t gc_since_ns = 0;
static int gc_depth = 0;
static int hooks_installed = 0;

/* The hooks installed before ours, which ours call. */
static caml_timing_hook old_minor_gc_begin = NULL;
static caml_timing_hook old_minor_gc_end = NULL;
static caml_timing_hook old_major_slice_begin = NULL;
static caml_timing_hook old_major_slice_end = NULL;

static void gc_phase_begin(void)
{
  if (gc_depth++ == 0) gc_since_ns = mainprofile_clock_ns();
}

static void gc_phase_end(void)
{
  if (gc_depth > 0 && --gc_depth == 0)
    gc_total_ns += mainprofile_clock_ns() - gc_since_ns;
}

static void mainprofile_minor_gc_begin(void)
{
  gc_phase_begin();
  if (old_minor_gc_begin != NULL) old_minor_gc_begin();
}

static void mainprofile_minor_gc_end(void)
{
  if (old_minor_gc_end != NULL) old_minor_gc_end();
  gc_phase_end();
}

static void mainprofile_major_slice_begin(void)
{
  gc_phase_begin();
  if (old_major_slice_begin != NULL) old_major_slice_begin();
}

static void mainprofile_major_slice_end(void)
{
  if (old_major_slice_end != NULL) old_major_slice_end();
  gc_phase_end();
}

CAMLprim value rocqchk_mainprofile_install_hooks(value unit)
{
  (void) unit;
  if (!hooks_installed) {
    hooks_installed = 1;
    old_minor_gc_begin = caml_minor_gc_begin_hook;
    old_minor_gc_end = caml_minor_gc_end_hook;
    old_major_slice_begin = caml_major_slice_begin_hook;
    old_major_slice_end = caml_major_slice_end_hook;
    caml_minor_gc_begin_hook = mainprofile_minor_gc_begin;
    caml_minor_gc_end_hook = mainprofile_minor_gc_end;
    caml_major_slice_begin_hook = mainprofile_major_slice_begin;
    caml_major_slice_end_hook = mainprofile_major_slice_end;
  }
  return Val_unit;
}

CAMLprim value rocqchk_mainprofile_now_ns(value unit)
{
  (void) unit;
  return Val_long((intnat) mainprofile_clock_ns());
}

CAMLprim value rocqchk_mainprofile_gc_ns(value unit)
{
  (void) unit;
  return Val_long((intnat) gc_total_ns);
}

/* Called from OCaml code, so outside any GC phase. */
CAMLprim value rocqchk_mainprofile_reset_gc_ns(value unit)
{
  (void) unit;
  gc_total_ns = 0;
  return Val_unit;
}

CAMLprim value rocqchk_mainprofile_minflt(value unit)
{
  struct rusage ru;
  (void) unit;
  if (getrusage(RUSAGE_SELF, &ru) != 0) return Val_long(0);
  return Val_long((intnat) ru.ru_minflt);
}

CAMLprim value rocqchk_mainprofile_majflt(value unit)
{
  struct rusage ru;
  (void) unit;
  if (getrusage(RUSAGE_SELF, &ru) != 0) return Val_long(0);
  return Val_long((intnat) ru.ru_majflt);
}
