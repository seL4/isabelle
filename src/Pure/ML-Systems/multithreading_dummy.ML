(*  Title:      Pure/ML-Systems/multithreading_dummy.ML
    ID:         $Id$
    Author:     Makarius

Compatibility file for ML systems without multithreading.
*)

signature MULTITHREADING =
sig
  val max_threads: int ref
  val self_critical: unit -> bool
  val CRITICAL: (unit -> 'a) -> 'a
  val schedule: int -> ('a -> (unit -> unit) option * 'a) -> 'a -> exn list
end;

structure Multithreading: MULTITHREADING =
struct

val max_threads = ref 1;

fun self_critical () = false;
fun CRITICAL e = e ();

fun schedule _ _ _ = raise Fail ("No multithreading support for " ^ ml_system);

end;

val CRITICAL = Multithreading.CRITICAL;
