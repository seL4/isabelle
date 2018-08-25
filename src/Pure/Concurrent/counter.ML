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
    val counter = Synchronized.var "counter" 0;
    fun next () =
      Synchronized.change_result counter
        (fn i =>
          let
            val k = i + 1;
            val n = if Thread_Data.is_virtual then 2 * k + 1 else 2 * k;
          in (n, k) end);
  in next end;

end;
