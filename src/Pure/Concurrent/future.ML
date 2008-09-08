(*  Title:      Pure/Concurrent/future.ML
    ID:         $Id$
    Author:     Makarius

Functional threads as future values.
*)

signature FUTURE =
sig
  type task = TaskQueue.task
  type group = TaskQueue.group
  type 'a T
  val task_of: 'a T -> task
  val group_of: 'a T -> group option
  val future: group option -> task list -> (unit -> 'a) -> 'a T
  val fork: (unit -> 'a) -> 'a T
  val join: 'a T -> 'a
  val interrupt: task -> unit
  val interrupt_group: group -> unit
end;

structure Future: FUTURE =
struct

(* synchronized execution *)

local
  val lock = Mutex.mutex ();
  val cond = ConditionVar.conditionVar ();
in

fun SYNCHRONIZED e = uninterruptible (fn restore_attributes => fn () =>
  let
    val _ = Mutex.lock lock;
    val result = Exn.capture (restore_attributes e) ();
    val _ = Mutex.unlock lock;
  in Exn.release result end) ();

fun wait () = (*requires SYNCHRONIZED*)
  ConditionVar.wait (cond, lock);

fun wait_timeout timeout = (*requires SYNCHRONIZED*)
  ConditionVar.waitUntil (cond, lock, Time.+ (Time.now (), timeout));

fun notify_all () = (*requires SYNCHRONIZED*)
  ConditionVar.broadcast cond;

end;


(* datatype future *)

type task = TaskQueue.task;
type group = TaskQueue.group;

datatype 'a T = Future of
 {task: task,
  group: group option,
  result: 'a Exn.result option ref};

fun task_of (Future {task, ...}) = task;
fun group_of (Future {group, ...}) = group;


(* global state *)

val queue = ref TaskQueue.empty;
val scheduler = ref (NONE: Thread.thread option);
val workers = ref ([]: Thread.thread list);


(* worker thread *)

local val active = ref 0 in

fun change_active b = (*requires SYNCHRONIZED*)
 (change active (fn n => if b then n + 1 else n - 1);
  Multithreading.tracing 1 (fn () => "SCHEDULE: " ^ string_of_int (! active) ^ " active"));

end;

fun excessive_threads () = false;  (* FIXME *)

fun worker_next () = (*requires SYNCHRONIZED*)
  if excessive_threads () then
   (change_active false;
    change workers (filter_out (fn thread => Thread.equal (thread, Thread.self ())));
    NONE)
  else
    (case change_result queue (TaskQueue.dequeue (Thread.self ())) of
      NONE => (change_active false; wait (); change_active true; worker_next ())
    | some => some);

fun worker_loop () =
  (case SYNCHRONIZED worker_next of
    NONE => ()
  | SOME (task, run) =>
      let
        val _ = TaskQueue.set_thread_data (SOME task);
        val _ = run ();
        val _ = TaskQueue.set_thread_data NONE;
        val _ = SYNCHRONIZED (fn () => (change queue (TaskQueue.finished task); notify_all ()));
      in worker_loop () end);

fun worker_start () = SYNCHRONIZED (fn () =>
 (change_active true;
  change workers (cons (Thread.fork (worker_loop, Multithreading.no_interrupts)))));


(* scheduler *)

fun scheduler_loop () = (*requires SYNCHRONIZED*)
  let
    val m = Multithreading.max_threads_value ();
    val k = m - length (! workers);
    val _ = if k > 0 then funpow k worker_start () else ();
  in wait_timeout (Time.fromMilliseconds 300); scheduler_loop () end;

fun check_scheduler () = SYNCHRONIZED (fn () =>
  let
    val scheduler_active =
      (case ! scheduler of
        NONE => false
      | SOME t => Thread.isActive t);
  in
    if scheduler_active then ()
    else scheduler :=
      SOME (Thread.fork (SYNCHRONIZED o scheduler_loop, Multithreading.no_interrupts))
  end);


(* future values *)

fun future group deps (e: unit -> 'a) =
  let
    val _ = check_scheduler ();

    val result = ref (NONE: 'a Exn.result option);
    val run = Multithreading.with_attributes (Thread.getAttributes ())
      (fn _ => fn () => result := SOME (Exn.capture e ()));
    val task = SYNCHRONIZED (fn () =>
      change_result queue (TaskQueue.enqueue group deps run) before notify_all ());
  in Future {task = task, group = group, result = result} end;

fun fork e = future NONE [] e;

fun join (Future {result, ...}) =
  let
    val _ = check_scheduler ();
    fun loop () =
      (case ! result of
        NONE => (wait (); loop ())
      | SOME res => res);
  in Exn.release (SYNCHRONIZED loop) end;


(* interrupts *)

fun interrupt task = SYNCHRONIZED (fn () => TaskQueue.interrupt (! queue) task);
fun interrupt_group group = SYNCHRONIZED (fn () => TaskQueue.interrupt_group (! queue) group);

end;
