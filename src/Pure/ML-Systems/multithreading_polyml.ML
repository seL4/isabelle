(*  Title:      Pure/ML-Systems/multithreading_polyml.ML
    ID:         $Id$
    Author:     Makarius

Multithreading in Poly/ML (version 5.1).
*)

open Thread;

structure Multithreading: MULTITHREADING =
struct

val trace = ref false;
fun tracing msg =
  if ! trace
  then (TextIO.output (TextIO.stdErr, (">>> " ^ msg () ^ "\n")); TextIO.flushOut TextIO.stdErr)
  else ();

val available = true;
val max_threads = ref 1;


(* critical section -- may be nested within the same thread *)

local

fun add_name "" = ""
  | add_name name = " " ^ name;

fun add_name' "" = ""
  | add_name' name = " [" ^ name ^ "]";

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
              "CRITICAL" ^ add_name name ^ add_name' (! critical_name) ^ ": waiting for lock");
            val _ = Mutex.lock critical_lock;
            val _ = tracing (fn () =>
              "CRITICAL" ^ add_name name ^ add_name' (! critical_name) ^ ": obtained lock after " ^
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

fun inc i = (i := ! i + 1; ! i);
fun dec i = (i := ! i - 1; ! i);

fun schedule n next_task tasks =
  let
    (*protected execution*)
    val lock = Mutex.mutex ();
    fun PROTECTED name e =
      let
        val _ =
          if Mutex.trylock lock then ()
          else
           (tracing (fn () => "PROTECTED " ^ name ^ ": waiting for lock");
            Mutex.lock lock;
            tracing (fn () => "PROTECTED " ^ name ^ ": obtained lock"));
        val res = Exn.capture e ();
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
    val status = ref ([]: exn list);
    val wakeup = ConditionVar.conditionVar ();
    fun wait () = ConditionVar.wait (wakeup, lock);
    fun continue cont k =
      (PROTECTED "cont" (fn () => queue := cont (! queue));
       ConditionVar.broadcast wakeup; work k ())
    and work k () =
      (case dequeue () of
        (Task.Task f, cont) =>
          (case Exn.capture f () of
            Exn.Result () => continue cont k
          | Exn.Exn exn =>
              (PROTECTED "status" (fn () => status := exn :: ! status); continue cont k))
      | (Task.Running, _) =>
          (PROTECTED "wait" (fn () => (dec active; wait (); inc active)); work k ())
      | (Task.Finished, _) =>
         (PROTECTED "running" (fn () => (dec active; dec running));
          ConditionVar.broadcast wakeup));

    (*main control: fork and wait*)
    fun fork 0 = ()
      | fork k =
         (inc running; inc active;
          Thread.fork (work k, [Thread.InterruptState Thread.InterruptDefer]);
          fork (k - 1));
    val _ = PROTECTED "main" (fn () =>
     (fork (Int.max (n, 1));
      while ! running <> 0 do
        (tracing (fn () => "MAIN: " ^ Int.toString (! active) ^ " active");
         wait ())));

  in ! status end;

end;

val NAMED_CRITICAL = Multithreading.NAMED_CRITICAL;
val CRITICAL = Multithreading.CRITICAL;
