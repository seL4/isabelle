(*  Title:      Pure/ML-Systems/multithreading_polyml.ML
    ID:         $Id$
    Author:     Makarius

Multithreading in Poly/ML (version 5.1).
*)

open Thread;

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

    (*the queue of tasks*)
    val queue = ref tasks;
    val active = ref 0;
    fun trace_active () = tracing 1 (fn () => "SCHEDULE: " ^ Int.toString (! active) ^ " active");
    fun dequeue () =
      let
        val (next, tasks') = next_task (! queue);
        val _ = queue := tasks';
      in
        if Task.is_running (#1 next) then
         (dec active; trace_active ();
          wait ();
          inc active; trace_active ();
          dequeue ())
        else next
      end;

    (*worker threads*)
    val running = ref 0;
    val status = ref ([]: exn list);
    fun work () =
      (case PROTECTED "dequeue" dequeue of
        (Task.Task f, cont) =>
          (case Exn.capture f () of
            Exn.Result () => continue cont
          | Exn.Exn exn =>
              (PROTECTED "status" (fn () => status := exn :: ! status); continue cont))
      | (Task.Finished, _) =>
         (PROTECTED "running" (fn () => (dec active; dec running; wakeup_all ()))))
    and continue cont =
      (PROTECTED "cont" (fn () => (queue := cont (! queue); wakeup_all ())); work ());

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
