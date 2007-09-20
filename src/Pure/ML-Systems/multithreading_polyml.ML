(*  Title:      Pure/ML-Systems/multithreading_polyml.ML
    ID:         $Id$
    Author:     Makarius

Multithreading in Poly/ML 5.1 or later (cf. polyml/basis/Thread.sml).
*)

open Thread;

signature MULTITHREADING =
sig
  include MULTITHREADING
  val ignore_interrupt: ('a -> 'b) -> 'a -> 'b
  val raise_interrupt: ('a -> 'b) -> 'a -> 'b
  val interrupt_timeout: Time.time -> ('a -> 'b) -> 'a -> 'b
end;

structure Multithreading: MULTITHREADING =
struct

(* options *)

val trace = ref 0;
fun tracing level msg =
  if level <= ! trace
  then (TextIO.output (TextIO.stdErr, (">>> " ^ msg () ^ "\n")); TextIO.flushOut TextIO.stdErr)
  else ();

val available = true;
val max_threads = ref 1;


(* misc utils *)

fun cons x xs = x :: xs;

fun change r f = r := f (! r);

fun inc i = (i := ! i + 1; ! i);
fun dec i = (i := ! i - 1; ! i);

fun show "" = "" | show name = " " ^ name;
fun show' "" = "" | show' name = " [" ^ name ^ "]";


(* thread attributes *)

fun with_attributes new_atts f x =
  let
    val orig_atts = Thread.getAttributes ();
    fun restore () = Thread.setAttributes orig_atts;
  in
    Exn.release
    (*RACE for fully asynchronous interrupts!*)
    (let
        val _ = Thread.setAttributes new_atts;
        val result = Exn.capture (f orig_atts) x;
        val _ = restore ();
      in result end
      handle Interrupt => (restore (); Exn.Exn Interrupt))
  end;


(* interrupt handling *)

fun uninterruptible f x = with_attributes
  [Thread.EnableBroadcastInterrupt false, Thread.InterruptState Thread.InterruptDefer] f x;

fun interruptible f x = with_attributes
  [Thread.EnableBroadcastInterrupt true, Thread.InterruptState Thread.InterruptAsynchOnce] f x;

fun ignore_interrupt f = uninterruptible (fn _ => f);
fun raise_interrupt f = interruptible (fn _ => f);

fun interrupt_timeout time f x =
  uninterruptible (fn atts => fn () =>
    let
      val worker = Thread.self ();
      val watchdog = Thread.fork (interruptible (fn _ => fn () =>
        (OS.Process.sleep time; Thread.interrupt worker)), []);
      val result = Exn.capture (with_attributes atts (fn _ => f)) x;
      val _ = Thread.interrupt watchdog handle Thread _ => ();
    in Exn.release result end) ();


(* critical section -- may be nested within the same thread *)

local

val critical_lock = Mutex.mutex ();
val critical_thread = ref (NONE: Thread.thread option);
val critical_name = ref "";

in

fun self_critical () =
  (case ! critical_thread of
    NONE => false
  | SOME id => Thread.equal (id, Thread.self ()));

fun NAMED_CRITICAL name e =
  if self_critical () then e ()
  else
    uninterruptible (fn atts => fn () =>
      let
        val name' = ! critical_name;
        val _ =
          if Mutex.trylock critical_lock then ()
          else
            let
              val timer = Timer.startRealTimer ();
              val _ = tracing 4 (fn () => "CRITICAL" ^ show name ^ show' name' ^ ": waiting");
              val _ = Mutex.lock critical_lock;
              val time = Timer.checkRealTimer timer;
              val _ = tracing (if Time.> (time, Time.fromMilliseconds 10) then 3 else 4) (fn () =>
                "CRITICAL" ^ show name ^ show' name' ^ ": passed after " ^ Time.toString time);
            in () end;
        val _ = critical_thread := SOME (Thread.self ());
        val _ = critical_name := name;
        val result = Exn.capture (with_attributes atts (fn _ => e)) ();
        val _ = critical_name := "";
        val _ = critical_thread := NONE;
        val _ = Mutex.unlock critical_lock;
      in Exn.release result end) ();

fun CRITICAL e = NAMED_CRITICAL "" e;

end;


(* scheduling -- multiple threads working on a queue of tasks *)

datatype 'a task =
  Task of {body: unit -> unit, cont: 'a -> 'a, fail: 'a -> 'a} | Wait | Terminate;

local

val protected_name = ref "";

in

fun schedule n next_task = uninterruptible (fn _ => fn tasks =>
  let
    (*protected execution*)
    val lock = Mutex.mutex ();
    fun PROTECTED name e =
      let
        val name' = ! protected_name;
        val _ =
          if Mutex.trylock lock then ()
          else
            let
              val _ = tracing 2 (fn () => "PROTECTED" ^ show name ^ show' name' ^ ": waiting");
              val _ = Mutex.lock lock;
              val _ = tracing 2 (fn () => "PROTECTED" ^ show name ^ show' name' ^ ": passed");
            in () end;
        val _ = protected_name := name;
        val res = Exn.capture e ();
        val _ = protected_name := "";
        val _ = Mutex.unlock lock;
      in Exn.release res end;

    (*wakeup condition*)
    val wakeup = ConditionVar.conditionVar ();
    fun wakeup_all () = ConditionVar.broadcast wakeup;
    fun wait () = ConditionVar.wait (wakeup, lock);
    fun wait_timeout () = ConditionVar.waitUntil (wakeup, lock, Time.now () + Time.fromSeconds 1);

    (*queue of tasks*)
    val queue = ref tasks;
    val active = ref 0;
    fun trace_active () = tracing 1 (fn () => "SCHEDULE: " ^ Int.toString (! active) ^ " active");
    fun dequeue () =
      let
        val (next, tasks') = next_task (! queue);
        val _ = queue := tasks';
      in
        (case next of Wait =>
          (dec active; trace_active ();
            wait ();
            inc active; trace_active ();
            dequeue ())
        | _ => next)
      end;

    (*pool of running threads*)
    val status = ref ([]: exn list);
    val running = ref ([]: Thread.thread list);
    fun start f =
      (inc active;
       change running (cons (Thread.fork (f, [Thread.InterruptState Thread.InterruptDefer]))));
    fun stop () =
      (dec active;
       change running (List.filter (fn t => not (Thread.equal (t, Thread.self ())))));

   (*worker thread*)
    fun worker () =
      (case PROTECTED "dequeue" dequeue of
        Task {body, cont, fail} =>
          (case Exn.capture (interruptible (fn _ => body)) () of
            Exn.Result () =>
              (PROTECTED "cont" (fn () => (change queue cont; wakeup_all ())); worker ())
          | Exn.Exn exn =>
              PROTECTED "fail" (fn () =>
                (change status (cons exn); change queue fail; stop (); wakeup_all ())))
      | Terminate => PROTECTED "terminate" (fn () => (stop (); wakeup_all ())));

    (*main control: fork and wait*)
    fun fork 0 = ()
      | fork k = (start worker; fork (k - 1));
    val _ = PROTECTED "main" (fn () =>
     (fork (Int.max (n, 1));
      while not (List.null (! running)) do
      (trace_active ();
       if not (List.null (! status)) then (List.app Thread.interrupt (! running)) else ();
       wait_timeout ())));

  in ! status end);

end;

end;

val NAMED_CRITICAL = Multithreading.NAMED_CRITICAL;
val CRITICAL = Multithreading.CRITICAL;
val ignore_interrupt = Multithreading.ignore_interrupt;
val raise_interrupt = Multithreading.raise_interrupt;
val interrupt_timeout = Multithreading.interrupt_timeout;

