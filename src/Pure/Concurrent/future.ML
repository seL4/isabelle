(*  Title:      Pure/Concurrent/future.ML
    Author:     Makarius

Future values.

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
  val enabled: unit -> bool
  type task = Task_Queue.task
  type group = Task_Queue.group
  val is_worker: unit -> bool
  val worker_group: unit -> Task_Queue.group option
  type 'a future
  val task_of: 'a future -> task
  val group_of: 'a future -> group
  val peek: 'a future -> 'a Exn.result option
  val is_finished: 'a future -> bool
  val value: 'a -> 'a future
  val fork: (unit -> 'a) -> 'a future
  val fork_group: group -> (unit -> 'a) -> 'a future
  val fork_deps: 'b future list -> (unit -> 'a) -> 'a future
  val fork_pri: int -> (unit -> 'a) -> 'a future
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

fun enabled () =
  Multithreading.enabled () andalso
    not (Multithreading.self_critical ());


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
val worker_group = Option.map #3 o thread_data;


(* datatype future *)

datatype 'a future = Future of
 {task: task,
  group: group,
  result: 'a Exn.result option ref};

fun task_of (Future {task, ...}) = task;
fun group_of (Future {group, ...}) = group;

fun peek (Future {result, ...}) = ! result;
fun is_finished x = is_some (peek x);

fun value x = Future
 {task = Task_Queue.new_task 0,
  group = Task_Queue.new_group NONE,
  result = ref (SOME (Exn.Result x))};



(** scheduling **)

(* global state *)

val queue = ref Task_Queue.empty;
val next = ref 0;
val workers = ref ([]: (Thread.thread * bool) list);
val scheduler = ref (NONE: Thread.thread option);
val excessive = ref 0;
val canceled = ref ([]: Task_Queue.group list);
val do_shutdown = ref false;


(* synchronization *)

val scheduler_event = ConditionVar.conditionVar ();
val work_available = ConditionVar.conditionVar ();
val work_finished = ConditionVar.conditionVar ();

local
  val lock = Mutex.mutex ();
in

fun SYNCHRONIZED name = SimpleThread.synchronized name lock;

fun wait cond = (*requires SYNCHRONIZED*)
  ConditionVar.wait (cond, lock);

fun wait_timeout cond timeout = (*requires SYNCHRONIZED*)
  ignore (ConditionVar.waitUntil (cond, lock, Time.+ (Time.now (), timeout)));

fun signal cond = (*requires SYNCHRONIZED*)
  ConditionVar.signal cond;

fun broadcast cond = (*requires SYNCHRONIZED*)
  ConditionVar.broadcast cond;

end;


(* worker activity *)

fun count_active ws =
  fold (fn (_, active) => fn i => if active then i + 1 else i) ws 0;

fun trace_active () = Multithreading.tracing 6 (fn () =>
  let
    val ws = ! workers;
    val m = string_of_int (length ws);
    val n = string_of_int (count_active ws);
  in "SCHEDULE: " ^ m ^ " workers, " ^ n ^ " active" end);

fun change_active active = (*requires SYNCHRONIZED*)
  change workers (AList.update Thread.equal (Thread.self (), active));

fun overloaded () =
  count_active (! workers) > Multithreading.max_threads_value ();


(* execute future jobs *)

fun future_job group (e: unit -> 'a) =
  let
    val result = ref (NONE: 'a Exn.result option);
    fun job ok =
      let
        val res =
          if ok then
            Exn.capture
              (Multithreading.with_attributes Multithreading.restricted_interrupts
                (fn _ => fn () => e ())) ()
          else Exn.Exn Exn.Interrupt;
        val _ = result := SOME res;
      in
        (case res of
          Exn.Exn exn => (Task_Queue.cancel_group group exn; false)
        | Exn.Result _ => true)
      end;
  in (result, job) end;

fun do_cancel group = (*requires SYNCHRONIZED*)
  change canceled (insert Task_Queue.eq_group group);

fun execute name (task, group, jobs) =
  let
    val _ = trace_active ();
    val valid = not (Task_Queue.is_canceled group);
    val ok = setmp_thread_data (name, task, group) (fn () =>
      fold (fn job => fn ok => job valid andalso ok) jobs true) ();
    val _ = SYNCHRONIZED "execute" (fn () =>
      let
        val maximal = change_result queue (Task_Queue.finish task);
        val _ =
          if ok then ()
          else if Task_Queue.cancel (! queue) group then ()
          else do_cancel group;
        val _ = broadcast work_finished;
        val _ = if maximal then () else broadcast work_available;
      in () end);
  in () end;


(* worker threads *)

fun worker_wait cond = (*requires SYNCHRONIZED*)
 (change_active false; broadcast scheduler_event;
  wait cond;
  change_active true; broadcast scheduler_event);

fun worker_next () = (*requires SYNCHRONIZED*)
  if ! excessive > 0 then
    (dec excessive;
     change workers (filter_out (fn (thread, _) => Thread.equal (thread, Thread.self ())));
     broadcast scheduler_event;
     NONE)
  else if overloaded () then (worker_wait scheduler_event; worker_next ())
  else
    (case change_result queue Task_Queue.dequeue of
      NONE => (worker_wait work_available; worker_next ())
    | some => some);

fun worker_loop name =
  (case SYNCHRONIZED name (fn () => worker_next ()) of
    NONE => ()
  | SOME work => (execute name work; worker_loop name));

fun worker_start name = (*requires SYNCHRONIZED*)
  change workers (cons (SimpleThread.fork false (fn () => worker_loop name), true));


(* scheduler *)

fun scheduler_next () = (*requires SYNCHRONIZED*)
  let
    (*queue status*)
    val _ = Multithreading.tracing 6 (fn () =>
      let val {ready, pending, running} = Task_Queue.status (! queue) in
        "SCHEDULE: " ^
          string_of_int ready ^ " ready, " ^
          string_of_int pending ^ " pending, " ^
          string_of_int running ^ " running"
      end);

    (*worker threads*)
    val _ =
      if forall (Thread.isActive o #1) (! workers) then ()
      else
        (case List.partition (Thread.isActive o #1) (! workers) of
          (_, []) => ()
        | (alive, dead) =>
            (workers := alive; Multithreading.tracing 0 (fn () =>
              "SCHEDULE: disposed " ^ string_of_int (length dead) ^ " dead worker threads")));
    val _ = trace_active ();

    val m = if ! do_shutdown then 0 else Multithreading.max_threads_value ();
    val mm = (m * 3) div 2;
    val l = length (! workers);
    val _ = excessive := l - mm;
    val _ =
      if mm > l then
       (funpow (mm - l) (fn () => worker_start ("worker " ^ string_of_int (inc next))) ();
        broadcast scheduler_event)
      else ();

    (*canceled groups*)
    val _ = change canceled (filter_out (Task_Queue.cancel (! queue)));

    val timeout =
      Time.fromMilliseconds (if not (! do_shutdown) andalso null (! canceled) then 500 else 50);
    val _ = interruptible (fn () => wait_timeout scheduler_event timeout) ()
      handle Exn.Interrupt => List.app do_cancel (Task_Queue.cancel_all (! queue));

    (*shutdown*)
    val continue = not (! do_shutdown andalso null (! workers));
    val _ = if continue then () else scheduler := NONE;
    val _ = broadcast scheduler_event;
  in continue end;

fun scheduler_loop () =
  while SYNCHRONIZED "scheduler" (fn () => scheduler_next ()) do ();

fun scheduler_active () = (*requires SYNCHRONIZED*)
  (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread);

fun scheduler_check name = SYNCHRONIZED name (fn () =>
  if not (scheduler_active ()) then
   (do_shutdown := false; scheduler := SOME (SimpleThread.fork false scheduler_loop);
    broadcast scheduler_event)
  else if ! do_shutdown then error "Scheduler shutdown in progress"
  else ());



(** futures **)

(* fork *)

fun fork_future opt_group deps pri e =
  let
    val _ = scheduler_check "future check";

    val group =
      (case opt_group of
        SOME group => group
      | NONE => Task_Queue.new_group (worker_group ()));
    val (result, job) = future_job group e;
    val task = SYNCHRONIZED "future" (fn () =>
      let
        val (task, minimal) = change_result queue (Task_Queue.enqueue group deps pri job);
        val _ = if minimal then signal work_available else ();
      in task end);
  in Future {task = task, group = group, result = result} end;

fun fork e = fork_future NONE [] 0 e;
fun fork_group group e = fork_future (SOME group) [] 0 e;
fun fork_deps deps e = fork_future NONE (map task_of deps) 0 e;
fun fork_pri pri e = fork_future NONE [] pri e;


(* join *)

local

fun get_result x =
  (case peek x of
    NONE => Exn.Exn (SYS_ERROR "unfinished future")
  | SOME (Exn.Exn Exn.Interrupt) =>
      Exn.Exn (Exn.EXCEPTIONS (Exn.flatten_list (Task_Queue.group_status (group_of x))))
  | SOME res => res);

fun join_next deps = (*requires SYNCHRONIZED*)
  if overloaded () then (worker_wait scheduler_event; join_next deps)
  else change_result queue (Task_Queue.dequeue_towards deps);

fun join_deps deps =
  (case SYNCHRONIZED "join" (fn () => join_next deps) of
    NONE => ()
  | SOME (work, deps') => (execute "join" work; join_deps deps'));

in

fun join_results xs =
  if forall is_finished xs then map get_result xs
  else uninterruptible (fn _ => fn () =>
    let
      val _ = scheduler_check "join check";
      val _ = Multithreading.self_critical () andalso
        error "Cannot join future values within critical section";

      val worker = is_worker ();
      val _ = if worker then join_deps (map task_of xs) else ();

      fun join_wait x =
        if SYNCHRONIZED "join_wait" (fn () =>
          is_finished x orelse ((if worker then worker_wait else wait) work_finished; false))
        then () else join_wait x;

      val _ = xs |> List.app (fn x =>
        let val time = Multithreading.real_time join_wait x in
          Multithreading.tracing_time true time
            (fn () => "joined after " ^ Time.toString time)
        end);
    in map get_result xs end) ();

end;

fun join_result x = singleton join_results x;
fun join x = Exn.release (join_result x);


(* map *)

fun map_future f x =
  let
    val _ = scheduler_check "map_future check";

    val task = task_of x;
    val group = Task_Queue.new_group (SOME (group_of x));
    val (result, job) = future_job group (fn () => f (join x));

    val extended = SYNCHRONIZED "map_future" (fn () =>
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
       then Multithreading.restricted_interrupts
       else Multithreading.regular_interrupts)
      (fn _ => f) x
  else interruptible f x;

(*cancel_group: present and future group members will be interrupted eventually*)
fun cancel_group group =
 (scheduler_check "cancel check";
  SYNCHRONIZED "cancel" (fn () => (do_cancel group; broadcast scheduler_event)));

fun cancel x = cancel_group (group_of x);


(** global join and shutdown **)

fun shutdown () =
  if Multithreading.available then
   (scheduler_check "shutdown check";
    SYNCHRONIZED "shutdown" (fn () =>
     (while not (scheduler_active ()) do wait scheduler_event;
      while not (Task_Queue.is_empty (! queue)) do wait scheduler_event;
      do_shutdown := true;
      while scheduler_active () do
       (broadcast work_available;
        broadcast scheduler_event;
        wait scheduler_event))))
  else ();


(*final declarations of this structure!*)
val map = map_future;

end;

type 'a future = 'a Future.future;

