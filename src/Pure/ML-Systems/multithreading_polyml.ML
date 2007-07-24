(*  Title:      Pure/ML-Systems/multithreading_polyml.ML
    ID:         $Id$
    Author:     Makarius

Multithreading in Poly/ML (version 5.1).
*)

open Thread;

structure Multithreading: MULTITHREADING =
struct

(* FIXME tmp *)
fun message s =
  (TextIO.output (TextIO.stdErr, (">>> " ^ s ^ "\n")); TextIO.flushOut TextIO.stdErr);


val max_threads = ref 1;


(* critical section -- may be nested within the same thread *)

local

val critical_lock = Mutex.mutex ();
val critical_thread = ref (NONE: Thread.thread option);

in

fun self_critical () =
  (case ! critical_thread of
    NONE => false
  | SOME id => Thread.equal (id, Thread.self ()));

fun CRITICAL e =
  if self_critical () then e ()
  else
    let
      val _ =
        if Mutex.trylock critical_lock then ()
        else
          (message "CRITICAL: waiting for lock";
           Mutex.lock critical_lock;
           message "CRITICAL: obtained lock");
      val _ = critical_thread := SOME (Thread.self ());
      val result = Exn.capture e ();
      val _ = critical_thread := NONE;
      val _ = Mutex.unlock critical_lock;
    in Exn.release result end;

end;


(* scheduling -- non-interruptible threads working on a queue of tasks *)

fun schedule n next_task tasks =
  let
    (*protected execution*)
    val lock = Mutex.mutex ();
    fun PROTECTED e =
      let
        val _ = Mutex.lock lock;
        val res = Exn.capture e ();
        val _ = Mutex.unlock lock;
      in Exn.release res end;

    (*queue of tasks*)
    val queue = ref tasks;
    fun dequeue () = PROTECTED (fn () =>
      let
        val (task, tasks') = next_task (! queue);
        val _ = queue := tasks';
      in task end);

    (*worker threads*)
    val running = ref 0;
    val status = ref ([]: exn list);
    val finished = ConditionVar.conditionVar ();
    fun work k () =
      (message ("WORKER THREAD " ^ Int.toString k);
       case dequeue () of
        SOME f =>
          (case Exn.capture f () of
            Exn.Result () => work k ()
          | Exn.Exn exn => (PROTECTED (fn () => status := exn :: ! status); work k ()))
      | NONE =>
         (PROTECTED (fn () => running := ! running - 1);
          ConditionVar.signal finished));

    (*main control: fork and wait*)
    fun fork 0 = ()
      | fork k =
         (running := ! running + 1;
          Thread.fork (work k, [Thread.InterruptState Thread.InterruptDefer]);
          fork (k - 1));
    val _ = PROTECTED (fn () =>
     (fork (Int.max (n, 1));
      while ! running <> 0 do ConditionVar.wait (finished, lock)));

  in ! status end;

end;

val CRITICAL = Multithreading.CRITICAL;
