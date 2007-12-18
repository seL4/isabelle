(*  Title:      Pure/ML-Systems/multithreading.ML
    ID:         $Id$
    Author:     Makarius

Dummy implementation of multithreading interface.
*)

signature BASIC_MULTITHREADING =
sig
  val NAMED_CRITICAL: string -> (unit -> 'a) -> 'a
  val CRITICAL: (unit -> 'a) -> 'a
end;

signature MULTITHREADING =
sig
  include BASIC_MULTITHREADING
  val trace: int ref
  val tracing: int -> (unit -> string) -> unit
  val available: bool
  val max_threads: int ref
  val self_critical: unit -> bool
  datatype 'a task =
    Task of {body: unit -> unit, cont: 'a -> 'a, fail: 'a -> 'a} | Wait | Terminate;
  val schedule: int -> ('a -> 'a task * 'a) -> 'a -> exn list
  val serial: unit -> int
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

local val count = ref (0: int)
in fun serial () = (count := ! count + 1; ! count) end;

end;

structure BasicMultithreading: BASIC_MULTITHREADING = Multithreading;
open BasicMultithreading;

