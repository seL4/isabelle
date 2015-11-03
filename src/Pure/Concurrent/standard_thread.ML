(*  Title:      Pure/Concurrent/standard_thread.ML
    Author:     Makarius

Standard thread operations.
*)

signature STANDARD_THREAD =
sig
  val is_self: Thread.thread -> bool
  val get_name: unit -> string option
  val the_name: unit -> string
  type params = {name: string, stack_limit: int option, interrupts: bool}
  val attributes: params -> Thread.threadAttribute list
  val fork: params -> (unit -> unit) -> Thread.thread
  val join: Thread.thread -> unit
  val interrupt_unsynchronized: Thread.thread -> unit
end;

structure Standard_Thread: STANDARD_THREAD =
struct

(* self *)

fun is_self thread = Thread.equal (Thread.self (), thread);


(* unique name *)

local
  val tag = Universal.tag () : string Universal.tag;
  val count = Counter.make ();
in

fun get_name () = Thread.getLocal tag;

fun the_name () =
  (case get_name () of
    NONE => raise Fail "Unknown thread name"
  | SOME name => name);

fun set_name base =
  Thread.setLocal (tag, base ^ "/" ^ string_of_int (count ()));

end;


(* fork *)

type params = {name: string, stack_limit: int option, interrupts: bool};

fun attributes ({stack_limit, interrupts, ...}: params) =
  ML_Stack.limit stack_limit @
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
