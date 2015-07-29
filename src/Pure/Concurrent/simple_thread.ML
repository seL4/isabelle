(*  Title:      Pure/Concurrent/simple_thread.ML
    Author:     Makarius

Simplified thread operations.
*)

signature SIMPLE_THREAD =
sig
  val is_self: Thread.thread -> bool
  val name: unit -> string option
  type params = {name: string, stack_limit: int option, interrupts: bool}
  val attributes: params -> Thread.threadAttribute list
  val fork: params -> (unit -> unit) -> Thread.thread
  val join: Thread.thread -> unit
  val interrupt_unsynchronized: Thread.thread -> unit
end;

structure Simple_Thread: SIMPLE_THREAD =
struct

(* self *)

fun is_self thread = Thread.equal (Thread.self (), thread);


(* unique name *)

local
  val tag = Universal.tag () : string Universal.tag;
  val count = Counter.make ();
in

fun name () = Thread.getLocal tag;
fun set_name base = Thread.setLocal (tag, base ^ "/" ^ string_of_int (count ()));

end;


(* fork *)

type params = {name: string, stack_limit: int option, interrupts: bool};

fun attributes ({stack_limit, interrupts, ...}: params) =
  maximum_ml_stack stack_limit @
  (if interrupts then Multithreading.public_interrupts else Multithreading.no_interrupts);

fun fork (params: params) body =
  Thread.fork (fn () =>
    print_exception_trace General.exnMessage tracing (fn () =>
      (set_name (#name params); body ())
        handle exn => if Exn.is_interrupt exn then () (*sic!*) else reraise exn),
    attributes params);


(* join *)

fun join thread =
  while Thread.isActive thread
  do OS.Process.sleep (seconds 0.1);


(* interrupt *)

fun interrupt_unsynchronized thread =
  Thread.interrupt thread handle Thread _ => ();

end;
