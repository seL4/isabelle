(*  Title:      Pure/Concurrent/isabelle_thread.ML
    Author:     Makarius

Isabelle-specific thread management.
*)

signature ISABELLE_THREAD =
sig
  type T
  val get_thread: T -> Thread.Thread.thread
  val get_name: T -> string
  val get_id: T -> int
  val equal: T * T -> bool
  val print: T -> string
  val self: unit -> T
  val is_self: T -> bool
  val threads_stack_limit: real Unsynchronized.ref
  val stack_limit: unit -> int option
  type params = {name: string, stack_limit: int option, interrupts: bool}
  val attributes: params -> Thread.Thread.threadAttribute list
  val fork: params -> (unit -> unit) -> T
  val is_active: T -> bool
  val join: T -> unit
  val interrupt: exn
  val interrupt_exn: 'a Exn.result
  val interrupt_self: unit -> 'a
  val interrupt_other: T -> unit
  structure Exn: EXN
  val expose_interrupt_result: unit -> unit Exn.result
  val expose_interrupt: unit -> unit  (*exception Interrupt*)
  val try_catch: (unit -> 'a) -> (exn -> 'a) -> 'a
  val try_finally: (unit -> 'a) -> (unit -> unit) -> 'a
  val try: (unit -> 'a) -> 'a option
  val can: (unit -> 'a) -> bool
end;

structure Isabelle_Thread: ISABELLE_THREAD =
struct

(* abstract type *)

abstype T = T of {thread: Thread.Thread.thread, name: string, id: int}
with
  val make = T;
  fun dest (T args) = args;
end;

val get_thread = #thread o dest;
val get_name = #name o dest;
val get_id = #id o dest;

fun equal (t1, t2) = Thread.Thread.equal (get_thread t1, get_thread t2);

fun print t =
  (case get_name t of "" => "ML" | a => "Isabelle." ^ a) ^
    "-" ^ Int.toString (get_id t);


(* self *)

val make_id = Counter.make ();

local
  val self_var = Thread_Data.var () : T Thread_Data.var;
in

fun init_self args =
  let val t = make args in Thread_Data.put self_var (SOME t); t end;

fun self () =
  (case Thread_Data.get self_var of
    SOME t => t
  | NONE => init_self {thread = Thread.Thread.self (), name = "", id = make_id ()});

fun is_self t = equal (t, self ());

end;


(* fork *)

val threads_stack_limit = Unsynchronized.ref 0.25;

fun stack_limit () =
  let
    val limit = Real.floor (! threads_stack_limit * 1024.0 * 1024.0 * 1024.0);
  in if limit <= 0 then NONE else SOME limit end;

type params = {name: string, stack_limit: int option, interrupts: bool};

fun attributes ({stack_limit, interrupts, ...}: params) =
  Thread.Thread.MaximumMLStack stack_limit ::
  Thread_Attributes.convert_attributes
    (if interrupts then Thread_Attributes.public_interrupts else Thread_Attributes.no_interrupts);

fun fork (params: params) body =
  let
    val self = Single_Assignment.var "self";
    fun main () =
      let
        val t = init_self {thread = Thread.Thread.self (), name = #name params, id = make_id ()};
        val _ = Single_Assignment.assign self t;
      in body () end;
    val _ = Thread.Thread.fork (main, attributes params);
  in Single_Assignment.await self end;


(* join *)

val is_active = Thread.Thread.isActive o get_thread;

fun join t =
  while is_active t
  do OS.Process.sleep (seconds 0.1);


(* interrupts *)

val interrupt = Thread.Thread.Interrupt;
val interrupt_exn = Exn.Exn interrupt;

fun interrupt_self () = raise interrupt;

fun interrupt_other t =
  Thread.Thread.interrupt (get_thread t) handle Thread.Thread _ => ();

structure Exn: EXN =
struct
  open Exn;
  val capture = capture0;
end;

fun expose_interrupt_result () =
  let
    val orig_atts = Thread_Attributes.safe_interrupts (Thread_Attributes.get_attributes ());
    val _ = Thread_Attributes.set_attributes Thread_Attributes.test_interrupts;
    val test = Exn.capture Thread.Thread.testInterrupt ();
    val _ = Thread_Attributes.set_attributes orig_atts;
  in test end;

val expose_interrupt = Exn.release o expose_interrupt_result;

fun try_catch e f =
  Thread_Attributes.uninterruptible_body (fn run =>
    run e () handle exn => if Exn.is_interrupt exn then Exn.reraise exn else f exn);

fun try_finally e f =
  Thread_Attributes.uninterruptible_body (fn run =>
    Exn.release (Exn.capture (run e) () before f ()));

fun try e = Basics.try e ();
fun can e = Basics.can e ();

end;

structure Exn = Isabelle_Thread.Exn;
