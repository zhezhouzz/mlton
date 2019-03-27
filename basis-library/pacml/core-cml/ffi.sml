structure PacmlFFI =
struct


  val compareAndSwap = _import "Parallel_compareAndSwap": Int32.int ref * Int32.int * Int32.int -> bool;
  val disablePreemption = _import "Parallel_disablePreemption": unit -> unit;
  val enablePreemption = _import "Parallel_enablePreemption": unit -> unit;
  val fetchAndAdd = _import "Parallel_fetchAndAdd": Int32.int ref * Int32.int -> Int32.int;
  val maybeWaitForGC = _import "Parallel_maybeWaitForGC": unit -> unit;
  val noop = _import "GC_noop": unit -> unit;
  val numberOfProcessors = Int32.toInt ((_import "Parallel_numberOfProcessors": unit -> Int32.int;) ())
  val numIOProcessors = Int32.toInt ((_import "Parallel_numIOThreads": unit -> Int32.int;) ())
  val numComputeProcessors = numberOfProcessors - numIOProcessors
  val processorNumber = _import "Parallel_processorNumber": unit -> Int32.int;
  val vCompareAndSwap = _import "Parallel_vCompareAndSwap": Int32.int ref * Int32.int * Int32.int -> Int32.int;
  val wait = _import "Parallel_wait": unit -> unit;
  val wakeUp = _import "Parallel_wakeUpThread": Int32.int * Int32.int -> unit;

end
