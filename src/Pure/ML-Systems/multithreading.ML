(*  Title:      Pure/ML-Systems/multithreading.ML
    Author:     Makarius

Dummy implementation of multithreading setup.
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
  val tracing_time: bool -> Time.time -> (unit -> string) -> unit
  val real_time: ('a -> unit) -> 'a -> Time.time
  val available: bool
  val max_threads: int ref
  val max_threads_value: unit -> int
  val enabled: unit -> bool
  val no_interrupts: Thread.threadAttribute list
  val regular_interrupts: Thread.threadAttribute list
  val restricted_interrupts: Thread.threadAttribute list
  val with_attributes: Thread.threadAttribute list ->
    (Thread.threadAttribute list -> 'a -> 'b) -> 'a -> 'b
  val sync_wait: Time.time option -> ConditionVar.conditionVar -> Mutex.mutex -> bool
  val self_critical: unit -> bool
  val serial: unit -> int
end;

structure Multithreading: MULTITHREADING =
struct

(* tracing *)

val trace = ref (0: int);
fun tracing _ _ = ();
fun tracing_time _ _ _ = ();
fun real_time f x = (f x; Time.zeroTime);


(* options *)

val available = false;
val max_threads = ref (1: int);
fun max_threads_value () = 1: int;
fun enabled () = false;


(* attributes *)

val no_interrupts =
  [Thread.EnableBroadcastInterrupt false, Thread.InterruptState Thread.InterruptDefer];

val regular_interrupts =
  [Thread.EnableBroadcastInterrupt true, Thread.InterruptState Thread.InterruptAsynchOnce];

val restricted_interrupts =
  [Thread.EnableBroadcastInterrupt false, Thread.InterruptState Thread.InterruptAsynchOnce];

fun with_attributes _ f x = f [] x;

fun sync_wait _ _ _ = false;


(* critical section *)

fun self_critical () = false;
fun NAMED_CRITICAL _ e = e ();
fun CRITICAL e = e ();


(* serial numbers *)

local val count = ref (0: int)
in fun serial () = (count := ! count + 1; ! count) end;

end;

structure Basic_Multithreading: BASIC_MULTITHREADING = Multithreading;
open Basic_Multithreading;
