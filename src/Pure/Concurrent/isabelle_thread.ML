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
  val stack_limit: unit -> int option
  type params = {name: string, stack_limit: int option, interrupts: bool}
  val attributes: params -> Thread.Thread.threadAttribute list
  val fork: params -> (unit -> unit) -> T
  val is_active: T -> bool
  val join: T -> unit
  val interrupt_unsynchronized: T -> unit
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

val equal = Thread.Thread.equal o apply2 get_thread;

fun print t =
  (case get_name t of "" => "ML" | a => "Isabelle." ^ a) ^
    "-" ^ string_of_int (get_id t);


(* self *)

val make_id = Counter.make ();

local
  val self_var = Thread_Data.var () : T Thread_Data.var;
in

fun set_self t = Thread_Data.put self_var (SOME t);

fun self () =
  (case Thread_Data.get self_var of
    SOME t => t
  | NONE =>
      let val t = make {thread = Thread.Thread.self (), name = "", id = make_id ()}
      in set_self t; t end);

fun is_self t = equal (t, self ());

end;


(* fork *)

fun stack_limit () =
  let
    val threads_stack_limit =
      Real.floor (Options.default_real "threads_stack_limit" * 1024.0 * 1024.0 * 1024.0);
  in if threads_stack_limit <= 0 then NONE else SOME threads_stack_limit end;

type params = {name: string, stack_limit: int option, interrupts: bool};

fun attributes ({stack_limit, interrupts, ...}: params) =
  Thread.Thread.MaximumMLStack stack_limit ::
  Thread_Attributes.convert_attributes
    (if interrupts then Thread_Attributes.public_interrupts else Thread_Attributes.no_interrupts);

fun fork (params: params) body =
  let
    val name = #name params;
    val id = make_id ();
    fun main () = (set_self (make {thread = Thread.Thread.self (), name = name, id = id}); body ());
    val thread = Thread.Thread.fork (main, attributes params);
  in make {thread = thread, name = name, id = id} end;


(* join *)

val is_active = Thread.Thread.isActive o get_thread;

fun join t =
  while is_active t
  do OS.Process.sleep (seconds 0.1);


(* interrupt *)

fun interrupt_unsynchronized t =
  Thread.Thread.interrupt (get_thread t) handle Thread.Thread _ => ();

end;
