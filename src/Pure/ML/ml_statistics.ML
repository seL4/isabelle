(*  Title:      Pure/ML/ml_statistics.ML
    Author:     Makarius

ML runtime statistics.
*)

signature ML_STATISTICS =
sig
  val set: {tasks_ready: int, tasks_pending: int, tasks_running: int, tasks_passive: int,
    tasks_urgent: int, workers_total: int, workers_active: int, workers_waiting: int} -> unit
  val get: unit -> (string * string) list
  val get_external: int -> (string * string) list
  val monitor: int -> real -> unit
end;

structure ML_Statistics: ML_STATISTICS =
struct

(* print *)

fun print_int x = if x < 0 then "-" ^ Int.toString (~ x) else Int.toString x;

fun print_real0 x =
  let val s = Real.fmt (StringCvt.GEN NONE) x in
    (case String.fields (fn c => c = #".") s of
      [a, b] => if List.all (fn c => c = #"0") (String.explode b) then a else s
    | _ => s)
  end;

fun print_real x =
  if x < 0.0 then "-" ^ print_real0 (~ x) else print_real0 x;

val print_properties =
  String.concatWith "," o map (fn (a, b) => a ^ "=" ^ b);


(* set user properties *)

fun set {tasks_ready, tasks_pending, tasks_running, tasks_passive, tasks_urgent,
    workers_total, workers_active, workers_waiting} =
 (PolyML.Statistics.setUserCounter (0, tasks_ready);
  PolyML.Statistics.setUserCounter (1, tasks_pending);
  PolyML.Statistics.setUserCounter (2, tasks_running);
  PolyML.Statistics.setUserCounter (3, tasks_passive);
  PolyML.Statistics.setUserCounter (4, tasks_urgent);
  PolyML.Statistics.setUserCounter (5, workers_total);
  PolyML.Statistics.setUserCounter (6, workers_active);
  PolyML.Statistics.setUserCounter (7, workers_waiting));


(* get properties *)

local

fun make_properties
   {gcFullGCs,
    gcPartialGCs,
    gcSharePasses,
    sizeAllocation,
    sizeAllocationFree,
    sizeCode,
    sizeHeap,
    sizeHeapFreeLastFullGC,
    sizeHeapFreeLastGC,
    sizeStacks,
    threadsInML,
    threadsTotal,
    threadsWaitCondVar,
    threadsWaitIO,
    threadsWaitMutex,
    threadsWaitSignal,
    timeGCReal,
    timeGCSystem,
    timeGCUser,
    timeNonGCReal,
    timeNonGCSystem,
    timeNonGCUser,
    userCounters,
    gcState = gc_state} =
  let
    val tasks_ready = Vector.sub (userCounters, 0);
    val tasks_pending = Vector.sub (userCounters, 1);
    val tasks_running = Vector.sub (userCounters, 2);
    val tasks_passive = Vector.sub (userCounters, 3);
    val tasks_urgent = Vector.sub (userCounters, 4);
    val tasks_total = tasks_ready + tasks_pending + tasks_running + tasks_passive + tasks_urgent;
    val workers_total = Vector.sub (userCounters, 5);
    val workers_active = Vector.sub (userCounters, 6);
    val workers_waiting = Vector.sub (userCounters, 7);
    val gc_percent =
      (case gc_state of
        PolyML.Statistics.MLCode => 0
      | PolyML.Statistics.MinorGC p => p + 1
      | PolyML.Statistics.MajorGC p => p + 1
      | PolyML.Statistics.GCSharing p => p + 1
      | PolyML.Statistics.OtherState p => p + 1);
  in
    [("now", print_real (Time.toReal (Time.now ()))),
     ("tasks_ready", print_int tasks_ready),
     ("tasks_pending", print_int tasks_pending),
     ("tasks_running", print_int tasks_running),
     ("tasks_passive", print_int tasks_passive),
     ("tasks_urgent", print_int tasks_urgent),
     ("tasks_total", print_int tasks_total),
     ("workers_total", print_int workers_total),
     ("workers_active", print_int workers_active),
     ("workers_waiting", print_int workers_waiting),
     ("full_GCs", print_int gcFullGCs),
     ("partial_GCs", print_int gcPartialGCs),
     ("share_passes", print_int gcSharePasses),
     ("size_allocation", print_int sizeAllocation),
     ("size_allocation_free", print_int sizeAllocationFree),
     ("size_code", print_int sizeCode),
     ("size_heap", print_int sizeHeap),
     ("size_heap_free_last_full_GC", print_int sizeHeapFreeLastFullGC),
     ("size_heap_free_last_GC", print_int sizeHeapFreeLastGC),
     ("size_stacks", print_int sizeStacks),
     ("threads_in_ML", print_int threadsInML),
     ("threads_total", print_int threadsTotal),
     ("threads_wait_condvar", print_int threadsWaitCondVar),
     ("threads_wait_IO", print_int threadsWaitIO),
     ("threads_wait_mutex", print_int threadsWaitMutex),
     ("threads_wait_signal", print_int threadsWaitSignal),
     ("time_elapsed", print_real (Time.toReal timeNonGCReal)),
     ("time_elapsed_GC", print_real (Time.toReal timeGCReal)),
     ("time_CPU", print_real (Time.toReal timeNonGCSystem + Time.toReal timeNonGCUser)),
     ("time_GC", print_real (Time.toReal timeGCSystem + Time.toReal timeGCUser)),
     ("GC_percent", print_int gc_percent)]
  end;

in

fun get () =
  make_properties (PolyML.Statistics.getLocalStats ());

fun get_external pid =
  make_properties (PolyML.Statistics.getRemoteStats pid);

end;


(* monitor process *)

fun monitor pid delay =
  let
    fun loop () =
      (TextIO.output (TextIO.stdOut, print_properties (get_external pid) ^ "\n");
       TextIO.flushOut TextIO.stdOut;
       OS.Process.sleep (Time.fromReal delay);
       loop ());
    fun exit () = OS.Process.exit OS.Process.success;
  in loop () handle _ (*sic!*) => exit () end;

end;
