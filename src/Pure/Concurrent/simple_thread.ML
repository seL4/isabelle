(*  Title:      Pure/Concurrent/simple_thread.ML
    ID:         $Id$
    Author:     Makarius

Simplified thread fork interface.
*)

signature SIMPLE_THREAD =
sig
  val fork: bool -> (unit -> unit) -> Thread.thread
  val interrupt: Thread.thread -> unit
end;

structure SimpleThread: SIMPLE_THREAD =
struct

fun fork interrupts body =
  Thread.fork (fn () => exception_trace (fn () => body ()),
    if interrupts then Multithreading.regular_interrupts else Multithreading.no_interrupts);

fun interrupt thread = Thread.interrupt thread handle Thread _ => ();

end;
