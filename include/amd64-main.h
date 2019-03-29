/* Copyright (C) 2000-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 */

#ifndef _AMD64_MAIN_H_
#define _AMD64_MAIN_H_

#include "common-main.h"

#ifndef DEBUG_AMD64CODEGEN
#define DEBUG_AMD64CODEGEN TRUE
#endif

#ifndef DEBUG_ALRM
#define DEBUG_ALRM FALSE
#endif

/* A key whose value will be a unique integer per thread */
extern pthread_key_t gcstate_key;

PRIVATE extern struct GC_state * gcState;

/* Globals */
PRIVATE Word64 applyFFTempFun;
PRIVATE Word64 applyFFTempStackArg;
PRIVATE Word64 applyFFTempRegArg[6];
PRIVATE Real32 applyFFTempXmmsRegArgD[8];
PRIVATE Real64 applyFFTempXmmsRegArgS[8];
PRIVATE Word32 checkTemp;
PRIVATE Word64 cReturnTemp[16];
PRIVATE Pointer c_stackP;
PRIVATE Word64 fpcvtTemp;
PRIVATE Word32 fpeqTemp;
PRIVATE Word64 divTemp;
PRIVATE Word64 indexTemp;
PRIVATE Word64 raTemp1;
PRIVATE Word64 spill[32];
PRIVATE Word64 stackTopTemp;

static GC_frameIndex returnAddressToFrameIndex (GC_returnAddress ra) {
        return *((GC_frameIndex*)(ra - sizeof(GC_frameIndex)));
}

#define MLtonCallFromC                                                  \
/* Globals */                                                           \
pthread_key_t gcstate_key;                                            \
PRIVATE void MLton_jumpToSML (pointer jump);                            \
static void MLton_callFromC (pointer ffiOpArgsResPtr) {                 \
                fprintf (stderr, "MLton_callFromC() starting\n");       \
        pointer jump;                                                   \
        GC_state s = pthread_getspecific (gcstate_key);                 \
                                                                        \
        if (DEBUG_AMD64CODEGEN)                                         \
                fprintf (stderr, "MLton_callFromC() starting\n");       \
        GC_setSavedThread (s, GC_getCurrentThread (s));                 \
        s->atomicState += 3;                                            \
        if (s->signalsInfo.signalIsPending)                             \
                s->limit = s->limitPlusSlop - GC_HEAP_LIMIT_SLOP;       \
        /* Return to the C Handler thread. */                           \
        GC_switchToThread (s, GC_getCallFromCHandlerThread (s), 0);     \
        jump = *(pointer*)(s->stackTop - GC_RETURNADDRESS_SIZE);        \
        MLton_jumpToSML(jump);                                          \
        s->atomicState += 1;                                            \
        GC_switchToThread (s, GC_getSavedThread (s), 0);                \
        s->atomicState -= 1;                                            \
        if (0 == s->atomicState && s->signalsInfo.signalIsPending)      \
                s->limit = 0;                                           \
        if (DEBUG_AMD64CODEGEN)                                         \
                fprintf (stderr, "MLton_callFromC() done\n");           \
        return;                                                         \
}

#define MLtonMain(al, mg, mfs, mmc, pk, ps, ml)                         \
MLtonCallFromC                                                          \
                                                                        \
void run (void *arg) {                                                  \
        pointer jump;                                                   \
        extern pointer ml;                                              \
        GC_state s = (GC_state)arg;                                     \
        if (s == NULL) {                                                \
            fprintf (stderr, "gcState is NULL\n");                      \
            exit (1);                                                   \
        }                                                               \
        uint32_t num = Proc_processorNumber (s)                         \
                * s->controls.affinityStride                           \
                + s->controls.affinityBase;                            \
         set_cpu_affinity(num);                                         \
                                                                        \
        /* Save our state locally */                                    \
        pthread_setspecific (gcstate_key, s);                           \
        /* Mask ALRM signal */                                          \
                                                                        \
        if (s->amOriginal) {                                            \
                fprintf (stderr, "Real init\n");                        \
                real_Init();                                            \
                jump = (pointer)&ml;                                    \
        } else {                                                        \
                /* Return to the saved world */                         \
                jump = *(pointer*)(s->stackTop - GC_RETURNADDRESS_SIZE); \
        }                                                               \
        /* Check to see whether or not we are the first thread */       \
        if (Proc_amPrimary (s)) {                                       \
            fprintf (stderr, "main jump\n");                             \
            MLton_jumpToSML(jump);                                      \
        }                                                               \
        else {                                                          \
                Proc_waitForInitialization (s);                         \
                Parallel_run ();                                        \
        }                                                               \
}                                                                       \
                                                                        \
PUBLIC int MLton_main (int argc, char* argv[]) {                        \
        int procNo;                                                     \
        pthread_t *threads;                                             \
        {                                                               \
                struct GC_state s;                                      \
                /* Initialize with a generic state to read in @MLtons, etc */ \
                Initialize (s, al, mg, mfs, mmc, pk, ps, 0);            \
                                                                        \
                threads = (pthread_t *) malloc ((s.numberOfProcs) * sizeof (pthread_t)); \
                gcState = (GC_state) malloc ((s.numberOfProcs+1) * sizeof (struct GC_state)); \
                /* Create key */                                        \
                if (pthread_key_create(&gcstate_key, NULL)) {           \
                        fprintf (stderr, "pthread_key_create failed: %s\n", strerror (errno)); \
                        exit (1);                                       \
                }                                                       \
                /* Now copy initialization to the first processor state */      \
                memcpy (&gcState[0], &s, sizeof (struct GC_state));     \
                gcState[0].procStates = gcState;                        \
                GC_lateInit (&gcState[0]);                              \
        }                                                               \
        /* Fill in per-processor data structures */                     \
        for (procNo = 1; procNo <= gcState[0].numberOfProcs; procNo++) { \
                Duplicate (&gcState[procNo], &gcState[0]);              \
                gcState[procNo].procStates = gcState;                   \
                if (procNo == gcState[0].numberOfProcs)                 \
                    gcState[procNo].atomicState = 0;                    \
        }                                                               \
        /* Now create the threads */                                    \
        for (procNo = 1; procNo < gcState[0].numberOfProcs; procNo++) { \
                if (pthread_create (&threads[procNo - 1], NULL, &run, (void *)&gcState[procNo])) { \
                        fprintf (stderr, "pthread_create failed: %s\n", strerror (errno)); \
                        exit (1);                                       \
                }                                                       \
        }                                                               \
        /* Create the alrmHandler thread */                             \
        run ((void *)&gcState[0]);                                      \
}

#define MLtonLibrary(al, mg, mfs, mmc, pk, ps, ml)                      \
MLtonCallFromC                                                          \
PUBLIC void LIB_OPEN(LIBNAME) (int argc, char* argv[]) {                \
        pointer jump;                                                   \
        extern pointer ml;                                              \
                                                                        \
        gcState = (GC_state) malloc (sizeof (struct GC_state));         \
        Initialize (gcState[0], al, mg, mfs, mmc, pk, ps, 0);           \
        GC_state s = &gcState[0];                                       \
        if (s->amOriginal) {                                            \
                real_Init();                                            \
                jump = (pointer)&ml;                                    \
        } else {                                                        \
                jump = *(pointer*)(s->stackTop - GC_RETURNADDRESS_SIZE); \
        }                                                               \
        MLton_jumpToSML(jump);                                          \
}                                                                       \
PUBLIC void LIB_CLOSE(LIBNAME) () {                                     \
        pointer jump;                                                   \
        GC_state s = &gcState[0];                                       \
        jump = *(pointer*)(s->stackTop - GC_RETURNADDRESS_SIZE);   \
        MLton_jumpToSML(jump);                                          \
}

#endif /* #ifndef _AMD64_MAIN_H_ */
