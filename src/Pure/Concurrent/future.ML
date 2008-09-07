(*  Title:      Pure/Concurrent/future.ML
    ID:         $Id$
    Author:     Makarius

Functional threads as future values.
*)

signature FUTURE =
sig
  type 'a T
  eqtype id
  val id_of: 'a T -> id
  val interrupt: id -> unit
  val dependent_future: id list -> (unit -> 'a) -> 'a T
  val future: (unit -> 'a) -> 'a T
  val await: 'a T -> 'a
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

fun wait () = ConditionVar.wait (cond, lock);
fun wait_timeout timeout = ConditionVar.waitUntil (cond, lock, Time.+ (Time.now (), timeout));

fun notify_all () = ConditionVar.broadcast cond;

end;


(* typed futures, unytped ids *)

datatype 'a T = Future of serial * 'a Exn.result option ref;

datatype id = Id of serial;
fun id_of (Future (id, _)) = Id id;

local val tag = Universal.tag () : serial Universal.tag in
  fun get_id () = Thread.getLocal tag;
  fun put_id id = Thread.setLocal (tag, id);
end;


(* ordered queue of tasks *)

datatype task =
  Task of (unit -> unit) |
  Running of Thread.thread;

datatype queue = Queue of task IntGraph.T * (serial * (unit -> unit)) Queue.T;

val empty_queue = Queue (IntGraph.empty, Queue.empty);

fun check_cache (queue as Queue (tasks, cache)) =
  if not (Queue.is_empty cache) then queue
  else
    let fun ready (id, (Task task, ([], _))) = Queue.enqueue (id, task) | ready _ = I
    in Queue (tasks, IntGraph.fold ready tasks Queue.empty) end;

val next_task = check_cache #> (fn queue as Queue (tasks, cache) =>
  if Queue.is_empty cache then (NONE, queue)
  else
    let val (task, cache') = Queue.dequeue cache
    in (SOME task, Queue (tasks, cache')) end);

fun get_task (Queue (tasks, _)) id = IntGraph.get_node tasks id;

fun new_task deps id task (Queue (tasks, _)) =
  let
    fun add_dep (Id dep) G = IntGraph.add_edge_acyclic (dep, id) G
      handle IntGraph.UNDEF _ => G;  (*dep already finished*)
    val tasks' = tasks |> IntGraph.new_node (id, Task task) |> fold add_dep deps;
  in Queue (tasks', Queue.empty) end;

fun running_task id thread (Queue (tasks, cache)) =
  Queue (IntGraph.map_node id (K (Running thread)) tasks, cache);

fun finished_task id (Queue (tasks, _)) =
  Queue (IntGraph.del_nodes [id] tasks, Queue.empty);


(* global state *)

val tasks = ref empty_queue;
val scheduler = ref (NONE: Thread.thread option);
val workers = ref ([]: Thread.thread list);


fun interrupt (Id id) = SYNCHRONIZED (fn () =>
  (case try (get_task (! tasks)) id of
    SOME (Running thread) => Thread.interrupt thread
  | _ => ()));


(* worker thread *)

local val active = ref 0 in

fun change_active b = (*requires SYNCHRONIZED*)
  let
    val _ = change active (fn n => if b then n + 1 else n - 1);
    val n = ! active;
    val _ = Multithreading.tracing 1 (fn () => "SCHEDULE: " ^ string_of_int n ^ " active");
  in () end;

end;

fun excessive_threads () = false;  (* FIXME *)

fun worker_stop () = SYNCHRONIZED (fn () =>
  (change_active false; change workers (filter (fn t => not (Thread.equal (t, Thread.self ()))))));

fun worker_wait () = SYNCHRONIZED (fn () =>
  (change_active false; wait (); change_active true));

fun worker_loop () =
  if excessive_threads () then worker_stop ()
  else
    (case SYNCHRONIZED (fn () => change_result tasks next_task) of
      NONE => (worker_wait (); worker_loop ())
    | SOME (id, task) =>
        let
          val _ = SYNCHRONIZED (fn () => change tasks (running_task id (Thread.self ())));
          val _ = task ();
          val _ = SYNCHRONIZED (fn () => change tasks (finished_task id));
          val _ = notify_all ();
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
  in wait_timeout (Time.fromSeconds 1); scheduler_loop () end;

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

fun dependent_future deps (e: unit -> 'a) =
  let
    val _ = check_scheduler ();

    val r = ref (NONE: 'a Exn.result option);
    val task = Multithreading.with_attributes (Thread.getAttributes ())
      (fn _ => fn () => r := SOME (Exn.capture e ()));

    val id = serial ();
    val _ = SYNCHRONIZED (fn () => change tasks (new_task deps id task));
    val _ = notify_all ();

  in Future (id, r) end;

fun future e = dependent_future [] e;

fun await (Future (_, r)) =
  let
    val _ = check_scheduler ();

    fun loop () =
      (case SYNCHRONIZED (fn () => ! r) of
        NONE => (SYNCHRONIZED (fn () => wait ()); loop ())
      | SOME res => Exn.release res);
  in loop () end;

end;
