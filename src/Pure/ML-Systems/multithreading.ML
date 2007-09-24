(*  Title:      Pure/ML-Systems/multithreading.ML
    ID:         $Id$
    Author:     Makarius

Dummy implementation of multithreading interface.
*)

signature MULTITHREADING =
sig
  val trace: int ref
  val tracing: int -> (unit -> string) -> unit
  val available: bool
  val max_threads: int ref
  val self_critical: unit -> bool
  val NAMED_CRITICAL: string -> (unit -> 'a) -> 'a
  val CRITICAL: (unit -> 'a) -> 'a
  datatype 'a task =
    Task of {body: unit -> unit, cont: 'a -> 'a, fail: 'a -> 'a} | Wait | Terminate;
  val schedule: int -> ('a -> 'a task * 'a) -> 'a -> exn list
end;

structure Multithreading: MULTITHREADING =
struct

val trace = ref (0: int);
fun tracing _ _ = ();

val available = false;
val max_threads = ref (1: int);

fun self_critical () = false;
fun NAMED_CRITICAL _ e = e ();
fun CRITICAL e = e ();

datatype 'a task =
  Task of {body: unit -> unit, cont: 'a -> 'a, fail: 'a -> 'a} | Wait | Terminate;

fun schedule _ _ _ = raise Fail "No multithreading support";

end;

val NAMED_CRITICAL = Multithreading.NAMED_CRITICAL;
val CRITICAL = Multithreading.CRITICAL;
