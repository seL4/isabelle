(*  Title:      Pure/Concurrent/counter.ML
    Author:     Makarius

Synchronized counter for unique identifiers > 0.

NB: ML ticks forwards, JVM ticks backwards.
*)

signature COUNTER =
sig
  val make: unit -> unit -> int
end;

structure Counter: COUNTER =
struct

fun make () =
  let
    val lock = Thread.Mutex.mutex ();
    val count = Unsynchronized.ref 0;
    fun next () =
      Multithreading.synchronized_uninterruptible_body "counter" lock (fn _ =>
        let val k = Unsynchronized.inc count;
        in if Thread_Data.is_virtual then 2 * k + 1 else 2 * k end);
  in next end;

end;
