(*  Title:      Pure/Concurrent/isabelle_thread.ML
    Author:     Makarius

Isabelle-specific thread management.
*)

signature ISABELLE_THREAD =
sig
  val is_self: Thread.thread -> bool
  val get_name: unit -> string
  val stack_limit: unit -> int option
  type params = {name: string, stack_limit: int option, interrupts: bool}
  val attributes: params -> Thread.threadAttribute list
  val fork: params -> (unit -> unit) -> Thread.thread
  val join: Thread.thread -> unit
  val interrupt_unsynchronized: Thread.thread -> unit
end;

structure Isabelle_Thread: ISABELLE_THREAD =
struct

(* self *)

fun is_self thread = Thread.equal (Thread.self (), thread);


(* unique name *)

local
  val name_var = Thread_Data.var () : string Thread_Data.var;
  val count = Counter.make ();
in

fun get_name () =
  (case Thread_Data.get name_var of
    SOME name => name
  | NONE => raise Fail "Isabelle-specific thread required");

fun set_name base =
  Thread_Data.put name_var (SOME ("Isabelle." ^ base ^ "-" ^ string_of_int (count ())));

end;


(* fork *)

fun stack_limit () =
  let
    val threads_stack_limit =
      Real.floor (Options.default_real "threads_stack_limit" * 1024.0 * 1024.0 * 1024.0);
  in if threads_stack_limit <= 0 then NONE else SOME threads_stack_limit end;

type params = {name: string, stack_limit: int option, interrupts: bool};

fun attributes ({stack_limit, interrupts, ...}: params) =
  Thread.MaximumMLStack stack_limit ::
  Thread_Attributes.convert_attributes
    (if interrupts then Thread_Attributes.public_interrupts else Thread_Attributes.no_interrupts);

fun fork (params: params) body =
  Thread.fork (fn () => (set_name (#name params); body ()), attributes params);


(* join *)

fun join thread =
  while Thread.isActive thread
  do OS.Process.sleep (seconds 0.1);


(* interrupt *)

fun interrupt_unsynchronized thread =
  Thread.interrupt thread handle Thread _ => ();

end;
