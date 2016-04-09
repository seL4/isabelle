(*  Title:      Pure/Concurrent/multithreading.ML
    Author:     Makarius

Multithreading in Poly/ML (cf. polyml/basis/Thread.sml).
*)

signature MULTITHREADING =
sig
  val interrupted: unit -> unit  (*exception Interrupt*)
  val max_threads_value: unit -> int
  val max_threads_update: int -> unit
  val enabled: unit -> bool
  val sync_wait: Thread.threadAttribute list option -> Time.time option ->
    ConditionVar.conditionVar -> Mutex.mutex -> bool Exn.result
  val trace: int ref
  val tracing: int -> (unit -> string) -> unit
  val tracing_time: bool -> Time.time -> (unit -> string) -> unit
  val real_time: ('a -> unit) -> 'a -> Time.time
  val synchronized: string -> Mutex.mutex -> (unit -> 'a) -> 'a
end;

structure Multithreading: MULTITHREADING =
struct

(* interrupts *)

fun interrupted () =
  let
    val orig_atts = Thread_Attributes.safe_interrupts (Thread.getAttributes ());
    val _ = Thread.setAttributes Thread_Attributes.test_interrupts;
    val test = Exn.capture Thread.testInterrupt ();
    val _ = Thread.setAttributes orig_atts;
  in Exn.release test end;


(* options *)

fun num_processors () =
  (case Thread.numPhysicalProcessors () of
    SOME n => n
  | NONE => Thread.numProcessors ());

fun max_threads_result m =
  if m > 0 then m else Int.min (Int.max (num_processors (), 1), 8);

val max_threads = ref 1;
fun max_threads_value () = ! max_threads;
fun max_threads_update m = max_threads := max_threads_result m;

fun enabled () = max_threads_value () > 1;


(* synchronous wait *)

fun sync_wait opt_atts time cond lock =
  Thread_Attributes.with_attributes
    (Thread_Attributes.sync_interrupts
      (case opt_atts of SOME atts => atts | NONE => Thread.getAttributes ()))
    (fn _ =>
      (case time of
        SOME t => Exn.Res (ConditionVar.waitUntil (cond, lock, t))
      | NONE => (ConditionVar.wait (cond, lock); Exn.Res true))
      handle exn => Exn.Exn exn);


(* tracing *)

val trace = ref 0;

fun tracing level msg =
  if level > ! trace then ()
  else Thread_Attributes.uninterruptible (fn _ => fn () =>
    (TextIO.output (TextIO.stdErr, (">>> " ^ msg () ^ "\n")); TextIO.flushOut TextIO.stdErr)
      handle _ (*sic*) => ()) ();

fun tracing_time detailed time =
  tracing
   (if not detailed then 5
    else if time >= seconds 1.0 then 1
    else if time >= seconds 0.1 then 2
    else if time >= seconds 0.01 then 3
    else if time >= seconds 0.001 then 4 else 5);

fun real_time f x =
  let
    val timer = Timer.startRealTimer ();
    val () = f x;
    val time = Timer.checkRealTimer timer;
  in time end;


(* synchronized evaluation *)

fun synchronized name lock e =
  Exn.release (Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val immediate =
        if Mutex.trylock lock then true
        else
          let
            val _ = tracing 5 (fn () => name ^ ": locking ...");
            val time = real_time Mutex.lock lock;
            val _ = tracing_time true time (fn () => name ^ ": locked after " ^ Time.toString time);
          in false end;
      val result = Exn.capture (restore_attributes e) ();
      val _ = if immediate then () else tracing 5 (fn () => name ^ ": unlocking ...");
      val _ = Mutex.unlock lock;
    in result end) ());

end;
