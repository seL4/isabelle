(*  Title:      Pure/Concurrent/simple_thread.ML
    Author:     Makarius

Simplified thread operations.
*)

signature SIMPLE_THREAD =
sig
  val fork: bool -> (unit -> unit) -> Thread.thread
  val interrupt: Thread.thread -> unit
  val synchronized: string -> Mutex.mutex -> (unit -> 'a) -> 'a
end;

structure SimpleThread: SIMPLE_THREAD =
struct

fun fork interrupts body =
  Thread.fork (fn () => exception_trace (fn () => body () handle Exn.Interrupt => ()),
    if interrupts then Multithreading.public_interrupts else Multithreading.no_interrupts);

fun interrupt thread = Thread.interrupt thread handle Thread _ => ();


(* basic synchronization *)

fun synchronized name lock e = Exn.release (uninterruptible (fn restore_attributes => fn () =>
  let
    val immediate =
      if Mutex.trylock lock then true
      else
        let
          val _ = Multithreading.tracing 5 (fn () => name ^ ": locking ...");
          val time = Multithreading.real_time Mutex.lock lock;
          val _ = Multithreading.tracing_time true time
            (fn () => name ^ ": locked after " ^ Time.toString time);
        in false end;
    val result = Exn.capture (restore_attributes e) ();
    val _ =
      if immediate then () else Multithreading.tracing 5 (fn () => name ^ ": unlocking ...");
    val _ = Mutex.unlock lock;
  in result end) ());

end;
