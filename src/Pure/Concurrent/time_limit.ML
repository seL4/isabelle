(*  Title:      Pure/Concurrent/time_limit.ML
    Author:     Makarius

Execution with time limit.
*)

signature TIME_LIMIT =
sig
  exception TimeOut
  val timeLimit : Time.time -> ('a -> 'b) -> 'a -> 'b
end;

structure TimeLimit: TIME_LIMIT =
struct

exception TimeOut;

fun timeLimit time f x = uninterruptible (fn restore_attributes => fn () =>
  let
    val worker = Thread.self ();
    val timeout = Unsynchronized.ref false;
    val watchdog = Thread.fork (fn () =>
      (OS.Process.sleep time; timeout := true; Thread.interrupt worker), []);

    val result = Exn.capture (restore_attributes f) x;
    val was_timeout = Exn.is_interrupt_exn result andalso ! timeout;

    val _ = Thread.interrupt watchdog handle Thread _ => ();
  in if was_timeout then raise TimeOut else Exn.release result end) ();

end;

