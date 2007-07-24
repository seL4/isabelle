(*  Title:      Pure/ML-Systems/multithreading_dummy.ML
    ID:         $Id$
    Author:     Makarius

Compatibility file for ML systems without multithreading.
*)

signature MULTITHREADING =
sig
  val number_of_threads: int ref
  val self_critical: unit -> bool
  val CRITICAL: (unit -> 'a) -> 'a
end;

structure Multithreading: MULTITHREADING =
struct

val number_of_threads = ref 0;

fun self_critical () = false;
fun CRITICAL e = e ();

end;

val CRITICAL = Multithreading.CRITICAL;
