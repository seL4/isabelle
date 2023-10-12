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
  val default_stack_limit: unit -> int option
  type params
  val params: string -> params
  val stack_limit: int -> params -> params
  val interrupts: params -> params
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
  val expose_interrupt: unit -> unit  (*exception Exn.is_interrupt*)
  val try_catch: (unit -> 'a) -> (exn -> 'a) -> 'a
  val try_finally: (unit -> 'a) -> (unit -> unit) -> 'a
  val try: (unit -> 'a) -> 'a option
  val can: (unit -> 'a) -> bool
end;

structure Isabelle_Thread: ISABELLE_THREAD =
struct

(* abstract type *)

abstype T = T of {thread: Thread.Thread.thread, name: string, id: int, break: bool Synchronized.var}
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

fun init_self name =
  let
    val break = Synchronized.var "Isabelle_Thread.break" false;
    val t = make {thread = Thread.Thread.self (), name = name, id = make_id (), break = break};
  in Thread_Data.put self_var (SOME t); t end;

fun self () =
  (case Thread_Data.get self_var of
    SOME t => t
  | NONE => init_self "");

fun is_self t = equal (t, self ());

end;


(* fork *)

val threads_stack_limit = Unsynchronized.ref 0.25;

fun default_stack_limit () =
  let val limit = Real.floor (! threads_stack_limit * 1024.0 * 1024.0 * 1024.0)
  in if limit <= 0 then NONE else SOME limit end;

abstype params = Params of {name: string, stack_limit: int option, interrupts: bool}
with

fun make_params (name, stack_limit, interrupts) =
  Params {name = name, stack_limit = stack_limit, interrupts = interrupts};

fun params name = make_params (name, default_stack_limit (), false);
fun stack_limit limit (Params {name, interrupts, ...}) = make_params (name, SOME limit, interrupts);
fun interrupts (Params {name, stack_limit, ...}) = make_params (name, stack_limit, true);

fun params_name (Params {name, ...}) = name;
fun params_stack_limit (Params {stack_limit, ...}) = stack_limit;
fun params_interrupts (Params {interrupts, ...}) = interrupts;

end;

fun attributes params =
  Thread.Thread.MaximumMLStack (params_stack_limit params) ::
  Thread_Attributes.convert_attributes
    (if params_interrupts params
     then Thread_Attributes.public_interrupts
     else Thread_Attributes.no_interrupts);

fun fork params body =
  let
    val self = Single_Assignment.var "self";
    fun main () =
      let
        val t = init_self (params_name params);
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

val interrupt = Exn.Interrupt_Break;
val interrupt_exn = Exn.Exn interrupt;

fun interrupt_self () = raise interrupt;

fun interrupt_other t =
  Synchronized.change (#break (dest t))
    (fn b => (Thread.Thread.interrupt (get_thread t); true) handle Thread.Thread _ => b);

fun check_interrupt exn =
  if Exn.is_interrupt_raw exn then
    let
      val t = self ();
      val break = Synchronized.change_result (#break (dest t)) (fn b => (b, false));
    in if break then Exn.Interrupt_Break else Exn.Interrupt_Breakdown end
  else exn;

fun check_interrupt_exn result =
  Exn.map_exn check_interrupt result;

structure Exn: EXN =
struct
  open Exn;
  fun capture f x = Res (f x) handle e => Exn (check_interrupt e);
  fun capture_body e = capture e ();
end;

fun expose_interrupt_result () =
  let
    val orig_atts = Thread_Attributes.safe_interrupts (Thread_Attributes.get_attributes ());
    fun main () =
      (Thread_Attributes.set_attributes Thread_Attributes.test_interrupts;
       Thread.Thread.testInterrupt ());
    val test = check_interrupt_exn (Exn.capture_body main);
    val _ = Thread_Attributes.set_attributes orig_atts;
  in test end;

val expose_interrupt = Exn.release o expose_interrupt_result;

fun try_catch e f =
  Thread_Attributes.uninterruptible_body (fn run =>
    run e () handle exn =>
      if Exn.is_interrupt exn then Exn.reraise (check_interrupt exn) else f exn);

fun try_finally e f =
  Thread_Attributes.uninterruptible_body (fn run =>
    Exn.release (check_interrupt_exn (Exn.capture_body (run e)) before f ()));

fun try e = Basics.try e ();
fun can e = Basics.can e ();

end;

structure Exn = Isabelle_Thread.Exn;
