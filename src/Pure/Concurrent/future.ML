(*  Title:      Pure/Concurrent/future.ML
    Author:     Makarius

Future values, see also
http://www4.in.tum.de/~wenzelm/papers/parallel-isabelle.pdf

Notes:

  * Futures are similar to delayed evaluation, i.e. delay/force is
    generalized to fork/join (and variants).  The idea is to model
    parallel value-oriented computations, but *not* communicating
    processes.

  * Futures are grouped; failure of one group member causes the whole
    group to be interrupted eventually.  Groups are block-structured.

  * Forked futures are evaluated spontaneously by a farm of worker
    threads in the background; join resynchronizes the computation and
    delivers results (values or exceptions).

  * The pool of worker threads is limited, usually in correlation with
    the number of physical cores on the machine.  Note that allocation
    of runtime resources is distorted either if workers yield CPU time
    (e.g. via system sleep or wait operations), or if non-worker
    threads contend for significant runtime resources independently.
*)

signature FUTURE =
sig
  type task = Task_Queue.task
  type group = Task_Queue.group
  val is_worker: unit -> bool
  val worker_task: unit -> Task_Queue.task option
  val worker_group: unit -> Task_Queue.group option
  type 'a future
  val task_of: 'a future -> task
  val group_of: 'a future -> group
  val peek: 'a future -> 'a Exn.result option
  val is_finished: 'a future -> bool
  val value: 'a -> 'a future
  val fork_group: group -> (unit -> 'a) -> 'a future
  val fork_deps_pri: 'b future list -> int -> (unit -> 'a) -> 'a future
  val fork_deps: 'b future list -> (unit -> 'a) -> 'a future
  val fork_pri: int -> (unit -> 'a) -> 'a future
  val fork: (unit -> 'a) -> 'a future
  val join_results: 'a future list -> 'a Exn.result list
  val join_result: 'a future -> 'a Exn.result
  val join: 'a future -> 'a
  val map: ('a -> 'b) -> 'a future -> 'b future
  val interruptible_task: ('a -> 'b) -> 'a -> 'b
  val cancel_group: group -> unit
  val cancel: 'a future -> unit
  val shutdown: unit -> unit
end;

structure Future: FUTURE =
struct

(** future values **)

(* identifiers *)

type task = Task_Queue.task;
type group = Task_Queue.group;

local
  val tag = Universal.tag () : (string * task * group) option Universal.tag;
in
  fun thread_data () = the_default NONE (Thread.getLocal tag);
  fun setmp_thread_data data f x =
    Library.setmp_thread_data tag (thread_data ()) (SOME data) f x;
end;

val is_worker = is_some o thread_data;
val worker_task = Option.map #2 o thread_data;
val worker_group = Option.map #3 o thread_data;


(* datatype future *)

datatype 'a future = Future of
 {task: task,
  group: group,
  result: 'a Exn.result option Synchronized.var};

fun task_of (Future {task, ...}) = task;
fun group_of (Future {group, ...}) = group;
fun result_of (Future {result, ...}) = result;

fun peek x = Synchronized.value (result_of x);
fun is_finished x = is_some (peek x);

fun value x = Future
 {task = Task_Queue.new_task 0,
  group = Task_Queue.new_group NONE,
  result = Synchronized.var "future" (SOME (Exn.Result x))};



(** scheduling **)

(* global state *)

val queue = Unsynchronized.ref Task_Queue.empty;
val next = Unsynchronized.ref 0;
val workers = Unsynchronized.ref ([]: (Thread.thread * bool) list);
val scheduler = Unsynchronized.ref (NONE: Thread.thread option);
val excessive = Unsynchronized.ref 0;
val canceled = Unsynchronized.ref ([]: Task_Queue.group list);
val do_shutdown = Unsynchronized.ref false;


(* synchronization *)

val scheduler_event = ConditionVar.conditionVar ();
val work_available = ConditionVar.conditionVar ();
val work_finished = ConditionVar.conditionVar ();

local
  val lock = Mutex.mutex ();
in

fun SYNCHRONIZED name = SimpleThread.synchronized name lock;

fun wait cond = (*requires SYNCHRONIZED*)
  Multithreading.sync_wait NONE NONE cond lock;

fun wait_timeout timeout cond = (*requires SYNCHRONIZED*)
  Multithreading.sync_wait NONE (SOME (Time.+ (Time.now (), timeout))) cond lock;

fun signal cond = (*requires SYNCHRONIZED*)
  ConditionVar.signal cond;

fun broadcast cond = (*requires SYNCHRONIZED*)
  ConditionVar.broadcast cond;

fun broadcast_work () = (*requires SYNCHRONIZED*)
 (ConditionVar.broadcast work_available;
  ConditionVar.broadcast work_finished);

end;


(* execute future jobs *)

fun future_job group (e: unit -> 'a) =
  let
    val result = Synchronized.var "future" (NONE: 'a Exn.result option);
    fun job ok =
      let
        val res =
          if ok then
            Exn.capture (fn () =>
              Multithreading.with_attributes Multithreading.private_interrupts (fn _ => e ())) ()
          else Exn.Exn Exn.Interrupt;
        val _ = Synchronized.change result
          (fn NONE => SOME res
            | SOME _ => raise Fail "Duplicate assignment of future value");
      in
        (case res of
          Exn.Exn exn => (Task_Queue.cancel_group group exn; false)
        | Exn.Result _ => true)
      end;
  in (result, job) end;

fun do_cancel group = (*requires SYNCHRONIZED*)
 (Unsynchronized.change canceled (insert Task_Queue.eq_group group);
  broadcast scheduler_event);

fun execute name (task, group, jobs) =
  let
    val valid = not (Task_Queue.is_canceled group);
    val ok = setmp_thread_data (name, task, group) (fn () =>
      fold (fn job => fn ok => job valid andalso ok) jobs true) ();
    val _ = SYNCHRONIZED "finish" (fn () =>
      let
        val maximal = Unsynchronized.change_result queue (Task_Queue.finish task);
        val _ =
          if ok then ()
          else if Task_Queue.cancel (! queue) group then ()
          else do_cancel group;
        val _ = broadcast work_finished;
        val _ = if maximal then () else broadcast work_available;
      in () end);
  in () end;


(* worker activity *)

fun count_active () = (*requires SYNCHRONIZED*)
  fold (fn (_, active) => fn i => if active then i + 1 else i) (! workers) 0;

fun change_active active = (*requires SYNCHRONIZED*)
  Unsynchronized.change workers
    (AList.update Thread.equal (Thread.self (), active));


(* worker threads *)

fun worker_wait cond = (*requires SYNCHRONIZED*)
  (change_active false; wait cond; change_active true);

fun worker_next () = (*requires SYNCHRONIZED*)
  if ! excessive > 0 then
    (Unsynchronized.dec excessive;
     Unsynchronized.change workers
      (filter_out (fn (thread, _) => Thread.equal (thread, Thread.self ())));
     broadcast scheduler_event;
     NONE)
  else if count_active () > Multithreading.max_threads_value () then
    (worker_wait scheduler_event; worker_next ())
  else
    (case Unsynchronized.change_result queue (Task_Queue.dequeue (Thread.self ())) of
      NONE => (worker_wait work_available; worker_next ())
    | some => some);

fun worker_loop name =
  (case SYNCHRONIZED name (fn () => worker_next ()) of
    NONE => ()
  | SOME work => (execute name work; worker_loop name));

fun worker_start name = (*requires SYNCHRONIZED*)
  Unsynchronized.change workers (cons (SimpleThread.fork false (fn () =>
     (broadcast scheduler_event; worker_loop name)), true));


(* scheduler *)

val last_status = Unsynchronized.ref Time.zeroTime;
val next_status = Time.fromMilliseconds 500;
val next_round = Time.fromMilliseconds 50;

fun scheduler_next () = (*requires SYNCHRONIZED*)
  let
    (*queue and worker status*)
    val _ =
      let val now = Time.now () in
        if Time.> (Time.+ (! last_status, next_status), now) then ()
        else
         (last_status := now; Multithreading.tracing 1 (fn () =>
            let
              val {ready, pending, running} = Task_Queue.status (! queue);
              val total = length (! workers);
              val active = count_active ();
            in
              "SCHEDULE " ^ Time.toString now ^ ": " ^
                string_of_int ready ^ " ready, " ^
                string_of_int pending ^ " pending, " ^
                string_of_int running ^ " running; " ^
                string_of_int total ^ " workers, " ^
                string_of_int active ^ " active"
            end))
      end;

    (*worker threads*)
    val _ =
      if forall (Thread.isActive o #1) (! workers) then ()
      else
        (case List.partition (Thread.isActive o #1) (! workers) of
          (_, []) => ()
        | (alive, dead) =>
            (workers := alive; Multithreading.tracing 0 (fn () =>
              "SCHEDULE: disposed " ^ string_of_int (length dead) ^ " dead worker threads")));

    val m = if ! do_shutdown then 0 else Multithreading.max_threads_value ();
    val mm = if m = 9999 then 1 else m * 2;
    val l = length (! workers);
    val _ = excessive := l - mm;
    val _ =
      if mm > l then
        funpow (mm - l) (fn () =>
          worker_start ("worker " ^ string_of_int (Unsynchronized.inc next))) ()
      else ();

    (*canceled groups*)
    val _ =
      if null (! canceled) then ()
      else
       (Multithreading.tracing 1 (fn () =>
          string_of_int (length (! canceled)) ^ " canceled groups");
        Unsynchronized.change canceled (filter_out (Task_Queue.cancel (! queue)));
        broadcast_work ());

    (*delay loop*)
    val _ = Exn.release (wait_timeout next_round scheduler_event);

    (*shutdown*)
    val _ = if Task_Queue.is_empty (! queue) then do_shutdown := true else ();
    val continue = not (! do_shutdown andalso null (! workers));
    val _ = if continue then () else scheduler := NONE;
    val _ = broadcast scheduler_event;
  in continue end
  handle Exn.Interrupt =>
   (Multithreading.tracing 1 (fn () => "Interrupt");
    uninterruptible (fn _ => fn () => List.app do_cancel (Task_Queue.cancel_all (! queue))) ();
    scheduler_next ());

fun scheduler_loop () =
  Multithreading.with_attributes
    (Multithreading.sync_interrupts Multithreading.public_interrupts)
    (fn _ => while SYNCHRONIZED "scheduler" (fn () => scheduler_next ()) do ());

fun scheduler_active () = (*requires SYNCHRONIZED*)
  (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread);

fun scheduler_check () = (*requires SYNCHRONIZED*)
 (do_shutdown := false;
  if scheduler_active () then ()
  else scheduler := SOME (SimpleThread.fork false scheduler_loop));



(** futures **)

(* fork *)

fun fork_future opt_group deps pri e =
  let
    val group =
      (case opt_group of
        SOME group => group
      | NONE => Task_Queue.new_group (worker_group ()));
    val (result, job) = future_job group e;
    val task = SYNCHRONIZED "enqueue" (fn () =>
      let
        val (task, minimal) =
          Unsynchronized.change_result queue (Task_Queue.enqueue group deps pri job);
        val _ = if minimal then signal work_available else ();
        val _ = scheduler_check ();
      in task end);
  in Future {task = task, group = group, result = result} end;

fun fork_group group e = fork_future (SOME group) [] 0 e;
fun fork_deps_pri deps pri e = fork_future NONE (map task_of deps) pri e;
fun fork_deps deps e = fork_deps_pri deps 0 e;
fun fork_pri pri e = fork_deps_pri [] pri e;
fun fork e = fork_deps [] e;


(* join *)

local

fun get_result x =
  (case peek x of
    NONE => Exn.Exn (SYS_ERROR "unfinished future")
  | SOME (Exn.Exn Exn.Interrupt) =>
      Exn.Exn (Exn.EXCEPTIONS (Exn.flatten_list (Task_Queue.group_status (group_of x))))
  | SOME res => res);

fun join_wait x =
  Synchronized.guarded_access (result_of x)
    (fn NONE => NONE | some => SOME ((), some));

fun join_next deps = (*requires SYNCHRONIZED*)
  if null deps then NONE
  else
    (case Unsynchronized.change_result queue (Task_Queue.dequeue_towards (Thread.self ()) deps) of
      (NONE, []) => NONE
    | (NONE, deps') => (worker_wait work_finished; join_next deps')
    | (SOME work, deps') => SOME (work, deps'));

fun execute_work NONE = ()
  | execute_work (SOME (work, deps')) = (execute "join" work; join_work deps')
and join_work deps =
  execute_work (SYNCHRONIZED "join" (fn () => join_next deps));

fun join_depend task deps =
  execute_work (SYNCHRONIZED "join" (fn () =>
    (Unsynchronized.change queue (Task_Queue.depend task deps); join_next deps)));

in

fun join_results xs =
  if forall is_finished xs then map get_result xs
  else if Multithreading.self_critical () then
    error "Cannot join future values within critical section"
  else
    (case worker_task () of
      SOME task => join_depend task (map task_of xs)
    | NONE => List.app join_wait xs;
    map get_result xs);

end;

fun join_result x = singleton join_results x;
fun join x = Exn.release (join_result x);


(* map *)

fun map_future f x =
  let
    val task = task_of x;
    val group = Task_Queue.new_group (SOME (group_of x));
    val (result, job) = future_job group (fn () => f (join x));

    val extended = SYNCHRONIZED "extend" (fn () =>
      (case Task_Queue.extend task job (! queue) of
        SOME queue' => (queue := queue'; true)
      | NONE => false));
  in
    if extended then Future {task = task, group = group, result = result}
    else fork_future (SOME group) [task] (Task_Queue.pri_of_task task) (fn () => f (join x))
  end;


(* cancellation *)

fun interruptible_task f x =
  if Multithreading.available then
    Multithreading.with_attributes
      (if is_worker ()
       then Multithreading.private_interrupts
       else Multithreading.public_interrupts)
      (fn _ => f x)
  else interruptible f x;

(*cancel: present and future group members will be interrupted eventually*)
fun cancel_group group = SYNCHRONIZED "cancel" (fn () => do_cancel group);
fun cancel x = cancel_group (group_of x);


(* shutdown *)

fun shutdown () =
  if Multithreading.available then
    SYNCHRONIZED "shutdown" (fn () =>
     while scheduler_active () do
      (wait scheduler_event; broadcast_work ()))
  else ();


(*final declarations of this structure!*)
val map = map_future;

end;

type 'a future = 'a Future.future;

