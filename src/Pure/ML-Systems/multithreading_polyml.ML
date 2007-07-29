(*  Title:      Pure/ML-Systems/multithreading_polyml.ML
    ID:         $Id$
    Author:     Makarius

Multithreading in Poly/ML (version 5.1).
*)

open Thread;

structure Multithreading: MULTITHREADING =
struct


(* flags *)

val trace = ref false;
fun tracing msg =
  if ! trace
  then (TextIO.output (TextIO.stdErr, (">>> " ^ msg () ^ "\n")); TextIO.flushOut TextIO.stdErr)
  else ();

val available = true;
val max_threads = ref 1;


(* misc utils *)

fun show "" = ""
  | show name = " " ^ name;

fun show' "" = ""
  | show' name = " [" ^ name ^ "]";

fun inc i = (i := ! i + 1; ! i);
fun dec i = (i := ! i - 1; ! i);


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
    let
      val _ =
        if Mutex.trylock critical_lock then ()
        else
          let
            val timer = Timer.startRealTimer ();
            val _ = tracing (fn () =>
              "CRITICAL" ^ show name ^ show' (! critical_name) ^ ": waiting");
            val _ = Mutex.lock critical_lock;
            val _ = tracing (fn () =>
              "CRITICAL" ^ show name ^ show' (! critical_name) ^ ": passed after " ^
              Time.toString (Timer.checkRealTimer timer));
          in () end;
      val _ = critical_thread := SOME (Thread.self ());
      val _ = critical_name := name;
      val result = Exn.capture e ();
      val _ = critical_name := "";
      val _ = critical_thread := NONE;
      val _ = Mutex.unlock critical_lock;
    in Exn.release result end;

fun CRITICAL e = NAMED_CRITICAL "" e;

end;


(* scheduling -- non-interruptible threads working on a queue of tasks *)

local

val protected_name = ref "";

in

fun schedule n next_task tasks =
  let
    (*protected execution*)
    val lock = Mutex.mutex ();
    fun PROTECTED name e =
      let
        val _ =
          if Mutex.trylock lock then ()
          else
           (tracing (fn () => "PROTECTED" ^ show name ^ show' (! protected_name) ^ ": waiting");
            Mutex.lock lock;
            tracing (fn () => "PROTECTED" ^ show name ^ show' (! protected_name) ^ ": passed"));
        val _ = protected_name := name;
        val res = Exn.capture e ();
        val _ = protected_name := "";
        val _ = Mutex.unlock lock;
      in Exn.release res end;

    (*the queue of tasks*)
    val queue = ref tasks;
    fun dequeue () = PROTECTED "dequeue" (fn () =>
      let
        val (next, tasks') = next_task (! queue);
        val _ = queue := tasks';
      in next end);

    (*worker threads*)
    val running = ref 0;
    val active = ref 0;
    fun trace_active () = tracing (fn () => "SCHEDULE: " ^ Int.toString (! active) ^ " active");
    val status = ref ([]: exn list);
    val wakeup = ConditionVar.conditionVar ();
    fun wait () = ConditionVar.wait (wakeup, lock);
    fun work () =
      (case dequeue () of
        (Task.Task f, cont) =>
          (case Exn.capture f () of
            Exn.Result () => continue cont
          | Exn.Exn exn =>
              (PROTECTED "status" (fn () => status := exn :: ! status); continue cont))
      | (Task.Running, _) =>
          (PROTECTED "wait" (fn () =>
            (dec active; trace_active ();
             wait ();
             inc active; trace_active ()));
           work ())
      | (Task.Finished, _) =>
         (PROTECTED "running" (fn () => (dec active; dec running));
          ConditionVar.broadcast wakeup))
    and continue cont =
      (PROTECTED "cont" (fn () => queue := cont (! queue));
       ConditionVar.broadcast wakeup; work ());

    (*main control: fork and wait*)
    fun fork 0 = ()
      | fork k =
         (inc running; inc active;
          Thread.fork (work, [Thread.InterruptState Thread.InterruptDefer]);
          fork (k - 1));
    val _ = PROTECTED "main" (fn () =>
     (fork (Int.max (n, 1));
      while ! running <> 0 do (trace_active (); wait ())));

  in ! status end;

end;

end;

val NAMED_CRITICAL = Multithreading.NAMED_CRITICAL;
val CRITICAL = Multithreading.CRITICAL;
