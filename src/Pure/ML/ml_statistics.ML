(*  Title:      Pure/ML/ml_statistics.ML
    Author:     Makarius

ML runtime statistics.
*)

signature ML_STATISTICS =
sig
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


(* make properties *)

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
    userCounters} =
  let
    val user_counters =
      Vector.foldri
        (fn (i, j, res) => ("user_counter" ^ print_int i, print_int j) :: res)
        [] userCounters;
  in
    [("full_GCs", print_int gcFullGCs),
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
     ("time_GC", print_real (Time.toReal timeGCSystem + Time.toReal timeGCUser))] @
    user_counters
  end;


(* get properties *)

fun get () =
  make_properties (PolyML.Statistics.getLocalStats ());

fun get_external pid =
  make_properties (PolyML.Statistics.getRemoteStats pid);


(* monitor process *)

fun monitor pid delay =
  let
    fun loop () =
      (TextIO.output (TextIO.stdOut, print_properties (get_external pid) ^ "\n");
       TextIO.flushOut TextIO.stdOut;
       OS.Process.sleep (Time.fromReal delay);
       loop ());
  in loop () handle Interrupt => OS.Process.exit OS.Process.success end;

end;
