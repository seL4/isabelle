(*  Title:      Pure/Concurrent/timeout.ML
    Author:     Makarius

Execution with relative timeout:
  - timeout specification < 1ms means no timeout
  - actual timeout is subject to system option "timeout_scale"
*)

signature TIMEOUT =
sig
  exception TIMEOUT of Time.time
  val ignored: Time.time -> bool
  val scale: unit -> real
  val scale_time: Time.time -> Time.time
  val end_time: Time.time -> Time.time
  val apply: Time.time -> ('a -> 'b) -> 'a -> 'b
  val apply_physical: Time.time -> ('a -> 'b) -> 'a -> 'b
  val print: Time.time -> string
end;

structure Timeout: TIMEOUT =
struct

exception TIMEOUT of Time.time;

fun ignored timeout = timeout < Time.fromMilliseconds 1;

fun scale () = Options.default_real "timeout_scale";
fun scale_time t = Time.scale (scale ()) t;

fun end_time timeout = Time.now () + scale_time timeout;

fun apply' {physical, timeout} f x =
  if ignored timeout then f x
  else
    Thread_Attributes.with_attributes Thread_Attributes.no_interrupts (fn orig_atts =>
      let
        val self = Isabelle_Thread.self ();
        val start = Time.now ();

        val request =
          Event_Timer.request {physical = physical} (start + scale_time timeout)
            (fn () => Isabelle_Thread.interrupt_other self);
        val result =
          Exn.capture (fn () => Thread_Attributes.with_attributes orig_atts (fn _ => f x)) ();

        val stop = Time.now ();
        val was_timeout = not (Event_Timer.cancel request);
        val test = Exn.capture Isabelle_Thread.expose_interrupt ();
      in
        if was_timeout andalso (Exn.is_interrupt_exn result orelse Exn.is_interrupt_exn test)
        then raise TIMEOUT (stop - start)
        else (Exn.release test; Exn.release result)
      end);

fun apply timeout f x = apply' {physical = false, timeout = timeout} f x;
fun apply_physical timeout f x = apply' {physical = true, timeout = timeout} f x;

fun print t = "Timeout after " ^ Value.print_time t ^ "s";

end;
