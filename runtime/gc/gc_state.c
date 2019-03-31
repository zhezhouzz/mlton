/* Copyright (C) 2009,2012 Matthew Fluet.
 * Copyright (C) 1999-2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 */

void displayGCState (GC_state s, FILE *stream) {
  fprintf (stream,
           "GC state\n");
  fprintf (stream, "\tcurrentThread = "FMTOBJPTR"\n", s->currentThread);
  displayThread (s, (GC_thread)(objptrToPointer (s->currentThread, s->heap.start)
                                + offsetofThread (s)), 
                 stream);
  fprintf (stream, "\tgenerational\n");
  displayGenerationalMaps (s, &s->generationalMaps, 
                           stream);
  fprintf (stream, "\theap\n");
  displayHeap (s, &s->heap, 
               stream);
  fprintf (stream,
           "\tlimit = "FMTPTR"\n"
           "\tstackBottom = "FMTPTR"\n"
           "\tstackTop = "FMTPTR"\n",
           (uintptr_t)s->limit,
           (uintptr_t)s->stackBottom,
           (uintptr_t)s->stackTop);
}

size_t sizeofGCStateCurrentStackUsed (GC_state s) {
  return (size_t)(s->stackTop - s->stackBottom);
}

void setGCStateCurrentThreadAndStack (GC_state s) {
  GC_thread thread;
  GC_stack stack;

  thread = getThreadCurrent (s);
  s->exnStack = thread->exnStack;
  stack = getStackCurrent (s);
  s->stackBottom = getStackBottom (s, stack);
  s->stackTop = getStackTop (s, stack);
  s->stackLimit = getStackLimit (s, stack);
  markCard (s, (pointer)stack);
}

void setGCStateCurrentHeap (GC_state s,
                            size_t oldGenBytesRequested,
                            size_t nurseryBytesRequested,
                            bool duringInit) {
  GC_heap h;
  pointer nursery;
  size_t nurserySize;
  pointer genNursery;
  size_t genNurserySize;
  pointer limit;
  pointer frontier;
  size_t bonus = GC_BONUS_SLOP * s->numberOfProcs;

  if (not duringInit) {
    nurseryBytesRequested = 0;
    for (int proc = 0; proc < s->numberOfProcs; proc++) {
      GC_thread thread = getThreadCurrent(&s->procStates[proc]);
      if (thread)
        nurseryBytesRequested += thread->bytesNeeded;
    }
  }

  if (DEBUG_DETAILED)
    fprintf (stderr, "setGCStateCurrentHeap(%s, %s)\n",
             uintmaxToCommaString(oldGenBytesRequested),
             uintmaxToCommaString(nurseryBytesRequested));
  h = s->heap;
  assert (h==s->heap);
  assert (isFrontierAligned (s, h->start + h->oldGenSize + oldGenBytesRequested));
  limit = h->start + h->size - bonus;
  nurserySize = h->size - (h->oldGenSize + oldGenBytesRequested) - bonus;
  assert (isFrontierAligned (s, limit - nurserySize));
  nursery = limit - nurserySize;
  genNursery = alignFrontier (s, limit - (nurserySize / 2));
  genNurserySize = limit - genNursery;
  if (/* The mutator marks cards. */
      s->mutatorMarksCards
      /* There is enough space in the generational nursery. */
      and (nurseryBytesRequested <= genNurserySize)
      /* The nursery is large enough to be worth it. */
      and (((float)(h->size - s->lastMajorStatistics->bytesLive)
            / (float)nurserySize)
           <= s->controls->ratios.nursery)
      and /* There is a reason to use generational GC. */
      (
       /* We must use it for debugging purposes. */
       FORCE_GENERATIONAL
       /* We just did a mark compact, so it will be advantageous to to use it. */
       or (s->lastMajorStatistics->kind == GC_MARK_COMPACT)
       /* The live ratio is low enough to make it worthwhile. */
       or ((float)h->size / (float)s->lastMajorStatistics->bytesLive
           <= (h->size < s->sysvals.ram
               ? s->controls->ratios.copyGenerational
               : s->controls->ratios.markCompactGenerational))
       )) {
    s->canMinor = TRUE;
    nursery = genNursery;
    nurserySize = genNurserySize;
    clearCardMap (s);
    /* XXX copy card map to other processors? */
  } else {
    unless (nurseryBytesRequested <= nurserySize)
      die ("Out of memory.  Insufficient space in nursery.");
    s->canMinor = FALSE;
  }
  if (s->controls->restrictAvailableSize
      and
      (s->cumulativeStatistics->maxBytesLiveSinceReset > 0)) {
    float actualRatio;
    h->availableSize =
      (size_t)(s->controls->ratios.available
               * s->cumulativeStatistics->maxBytesLiveSinceReset);

    if ((h->oldGenSize + oldGenBytesRequested + nurserySize + bonus)
        > h->availableSize) {
      /* Limit allocation in this round */
      if ((h->oldGenSize + oldGenBytesRequested + nurseryBytesRequested + bonus)
          > h->availableSize) {
        /* We can't limit as much as we'd like, so offer enough space to
           satisfy the current request. */
        h->availableSize = h->oldGenSize + oldGenBytesRequested
          + nurseryBytesRequested + bonus;
      }
      if (h->availableSize > h->size) {
        /* Can't offer more than we have. */
        h->availableSize = h->size;
      }
      limit = h->start + h->availableSize - bonus;
      nurserySize = h->availableSize - (h->oldGenSize + oldGenBytesRequested) - bonus;
      assert (isFrontierAligned (s, limit - nurserySize));
      nursery = limit - nurserySize;

      if (s->canMinor) {
        /* If we are planning for a minor collection, we must also adjust the
           start of the nursery */
        nursery = alignFrontier (s, limit - (nurserySize / 2));
        nurserySize = limit - nursery;
      }
      if (DEBUG) {
        fprintf (stderr,
                 "[GC: Restricted nursery at "FMTPTR" of %s bytes (%.1f%%).]\n",
                 (uintptr_t)nursery, uintmaxToCommaString(limit - nursery),
                 100.0 * ((double)(limit - nursery)
                          / (double)h->availableSize));
      }
    }
    else {
      /* No need to limit in this round... reset availableSize. */
      h->availableSize = h->size;
    }

    actualRatio = (float)h->availableSize
      / s->cumulativeStatistics->maxBytesLiveSinceReset;
    if ((DEBUG or s->controls->messages)
        and
        (actualRatio > s->controls->ratios.available)) {
      fprintf (stderr,
               "[GC: Can't restrict available ratio to %f, using %f; worst-case max-live is %s bytes.]\n",
               s->controls->ratios.available, actualRatio,
               uintmaxToCommaString(h->oldGenSize + oldGenBytesRequested + nurserySize));
    }
  }
  else {
    /* Otherwise, make all unused space available */
    h->availableSize = h->size;
  }

  assert (nurseryBytesRequested <= nurserySize);
  s->heap->nursery = nursery;
  frontier = nursery;

  if (not duringInit) {
    for (int proc = 0; proc < s->numberOfProcs; proc++) {
      s->procStates[proc].canMinor = s->canMinor;
      assert (isFrontierAligned (s, frontier));
      s->procStates[proc].start = s->procStates[proc].frontier = frontier;
      s->procStates[proc].limitPlusSlop = s->procStates[proc].start +
        getThreadCurrent(&s->procStates[proc])->bytesNeeded;
      s->procStates[proc].limit = s->procStates[proc].limitPlusSlop - GC_HEAP_LIMIT_SLOP;
      assert (s->procStates[proc].frontier <= s->procStates[proc].limitPlusSlop);
      /* XXX clearCardMap (?) */

      if (DEBUG)
        for (size_t i = 0; i < GC_BONUS_SLOP; i++)
          *(s->procStates[proc].limitPlusSlop + i) = 0xBF;

      frontier = s->procStates[proc].limitPlusSlop + GC_BONUS_SLOP;
    }
  }
  else {
    assert (Proc_processorNumber (s) == 0);
    /* XXX this is a lot of copy-paste */
    for (int proc = 1; proc < s->numberOfProcs; proc++) {
      s->procStates[proc].canMinor = s->canMinor;
      assert (isFrontierAligned (s, frontier));
      s->procStates[proc].start = s->procStates[proc].frontier = frontier;
      s->procStates[proc].limitPlusSlop = s->procStates[proc].start +
        GC_HEAP_LIMIT_SLOP;
      s->procStates[proc].limit = s->procStates[proc].limitPlusSlop - GC_HEAP_LIMIT_SLOP;
      assert (s->procStates[proc].frontier <= s->procStates[proc].limitPlusSlop);
      /* XXX clearCardMap (?) */

      if ( DEBUG)
        for (size_t i = 0; i < GC_BONUS_SLOP; i++)
          *(s->procStates[proc].limitPlusSlop + i) = 0xBF;

      frontier = s->procStates[proc].limitPlusSlop + GC_BONUS_SLOP;
    }

    s->start = s->frontier = frontier;
    s->limitPlusSlop = limit;
    s->limit = s->limitPlusSlop - GC_HEAP_LIMIT_SLOP;
    /* XXX clearCardMap (?) */

    if (DEBUG)
      for (size_t i = 0; i < GC_BONUS_SLOP; i++)
        *(s->limitPlusSlop + i) = 0xBF;

    frontier = s->limitPlusSlop + GC_BONUS_SLOP;
  }
  h->frontier = frontier;
  assert (h->frontier <= h->start + h->availableSize);

  if (not duringInit) {
    assert (getThreadCurrent(s)->bytesNeeded <= (size_t)(s->limitPlusSlop - s->frontier));
    assert (hasHeapBytesFree (s, oldGenBytesRequested, getThreadCurrent(s)->bytesNeeded));
  }
  else {
    assert (nurseryBytesRequested <= (size_t)(s->limitPlusSlop - s->frontier));
    assert (hasHeapBytesFree (s, oldGenBytesRequested, nurseryBytesRequested));
  }
  assert (isFrontierAligned (s, s->frontier));

}

bool GC_getIsPCML (__attribute__ ((unused)) GC_state *gs) {
  GC_state s = pthread_getspecific (gcstate_key);
  return false;
}

bool GC_getAmOriginal (GC_state s) {
  return s->amOriginal;
}
void GC_setAmOriginal (GC_state s, bool b) {
  s->amOriginal = b;
}

void GC_setControlsMessages (GC_state s, bool b) {
  s->controls.messages = b;
}

void GC_setControlsSummary (GC_state s, bool b) {
  s->controls.summary = b;
}

void GC_setControlsRusageMeasureGC (GC_state s, bool b) {
  s->controls.rusageMeasureGC = b;
}

uintmax_t GC_getCumulativeStatisticsBytesAllocated (GC_state s) {
  return s->cumulativeStatistics.bytesAllocated;
}

uintmax_t GC_getCumulativeStatisticsNumCopyingGCs (GC_state s) {
  return s->cumulativeStatistics.numCopyingGCs;
}

uintmax_t GC_getCumulativeStatisticsNumMarkCompactGCs (GC_state s) {
  return s->cumulativeStatistics.numMarkCompactGCs;
}

uintmax_t GC_getCumulativeStatisticsNumMinorGCs (GC_state s) {
  return s->cumulativeStatistics.numMinorGCs;
}

size_t GC_getCumulativeStatisticsMaxBytesLive (GC_state s) {
  return s->cumulativeStatistics.maxBytesLive;
}

void GC_setHashConsDuringGC (GC_state s, bool b) {
  s->hashConsDuringGC = b;
}

size_t GC_getLastMajorStatisticsBytesLive (GC_state s) {
  return s->lastMajorStatistics.bytesLive;
}


pointer GC_getCallFromCHandlerThread (GC_state s) {
  pointer p = objptrToPointer (s->callFromCHandlerThread, s->heap.start);
  return p;
}

void GC_setCallFromCHandlerThread (GC_state s, pointer p) {
  objptr op = pointerToObjptr (p, s->heap.start);
  s->callFromCHandlerThread = op;
}

pointer GC_getCurrentThread (GC_state s) {
  pointer p = objptrToPointer (s->currentThread, s->heap.start);
  return p;
}

pointer GC_getSavedThread (GC_state s) {
  pointer p;

  assert(s->savedThread != BOGUS_OBJPTR);
  p = objptrToPointer (s->savedThread, s->heap.start);
  s->savedThread = BOGUS_OBJPTR;
  return p;
}

void GC_setSavedThread (GC_state s, pointer p) {
  objptr op;

  assert(s->savedThread == BOGUS_OBJPTR);
  op = pointerToObjptr (p, s->heap.start);
  s->savedThread = op;
}

void GC_setSignalHandlerThread (GC_state s, pointer p) {
  objptr op = pointerToObjptr (p, s->heap.start);
  s->signalHandlerThread = op;
}

struct rusage* GC_getRusageGCAddr (GC_state s) {
  return &(s->cumulativeStatistics.ru_gc);
}

sigset_t* GC_getSignalsHandledAddr (GC_state s) {
  return &(s->signalsInfo.signalsHandled);
}

sigset_t* GC_getSignalsSet (__attribute__ ((unused)) GC_state *gs) {
  GC_state s = pthread_getspecific (gcstate_key);
  return &(s->signalsInfo.signalsSet);
}

sigset_t* GC_getSignalsPendingAddr (GC_state s) {
  return &(s->signalsInfo.signalsPending);
}

void GC_setGCSignalHandled (GC_state s, bool b) {
  s->signalsInfo.gcSignalHandled = b;
}

bool GC_getGCSignalPending (GC_state s) {
  return (s->signalsInfo.gcSignalPending);
}

void GC_setGCSignalPending (GC_state s, bool b) {
  s->signalsInfo.gcSignalPending = b;
}
