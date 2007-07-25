(*  Title:      Pure/ML-Systems/multithreading_dummy.ML
    ID:         $Id$
    Author:     Makarius

Compatibility file for ML systems without multithreading.
*)

structure Task =
struct
  datatype task = Task of (unit -> unit) | Running | Finished;
  fun is_running Running = true | is_running _ = false;
  fun is_finished Finished = true | is_finished _ = false;
end;

signature MULTITHREADING =
sig
  val trace: bool ref
  val tracing: (unit -> string) -> unit
  val available: bool
  val max_threads: int ref
  val self_critical: unit -> bool
  val CRITICAL': string -> (unit -> 'a) -> 'a
  val CRITICAL: (unit -> 'a) -> 'a
  val schedule: int -> ('a -> (Task.task * ('a -> 'a)) * 'a) -> 'a -> exn list
end;

structure Multithreading: MULTITHREADING =
struct

val trace = ref false;
fun tracing _ = ();

val available = false;
val max_threads = ref 1;

fun self_critical () = false;
fun CRITICAL' _ e = e ();
fun CRITICAL e = e ();

fun schedule _ _ _ = raise Fail "Multithreading support unavailable";

end;

val CRITICAL' = Multithreading.CRITICAL';
val CRITICAL = Multithreading.CRITICAL;
