(*  Title:      Pure/Concurrent/future.ML
    ID:         $Id$
    Author:     Makarius

Future values.

Notes:

  * Futures are similar to delayed evaluation, i.e. delay/force is
    generalized to fork/join (and variants).  The idea is to model
    parallel value-oriented computations, but *not* communicating
    processes.

  * Futures are grouped; failure of one group member causes the whole
    group to be interrupted eventually.

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
  type task = TaskQueue.task
  type group = TaskQueue.group
  type 'a T
  val task_of: 'a T -> task
  val group_of: 'a T -> group
  val future: group option -> task list -> bool -> (unit -> 'a) -> 'a T
  val fork: (unit -> 'a) -> 'a T
  val fork_irrelevant: (unit -> 'a) -> 'a T
  val join_results: 'a T list -> 'a Exn.result list
  val join: 'a T -> 'a
  val focus: task list -> unit
  val interrupt_task: string -> unit
  val cancel: 'a T -> unit
  val shutdown: unit -> unit
end;

structure Future: FUTURE =
struct

(** future values **)

(* identifiers *)

type task = TaskQueue.task;
type group = TaskQueue.group;

local val tag = Universal.tag () : (task * group) option Universal.tag in
  fun thread_data () = the_default NONE (Thread.getLocal tag);
  fun set_thread_data x = Thread.setLocal (tag, x);
end;


(* datatype future *)

datatype 'a T = Future of
 {task: task,
  group: group,
  result: 'a Exn.result option ref};

fun task_of (Future {task, ...}) = task;
fun group_of (Future {group, ...}) = group;



(** scheduling **)

(* global state *)

val queue = ref TaskQueue.empty;
val workers = ref ([]: (Thread.thread * bool) list);
val scheduler = ref (NONE: Thread.thread option);
val excessive = ref 0;
val canceled = ref ([]: TaskQueue.group list);
val do_shutdown = ref false;


(* synchronization *)

local
  val lock = Mutex.mutex ();
  val cond = ConditionVar.conditionVar ();
in

fun SYNCHRONIZED name e = uninterruptible (fn restore_attributes => fn () =>
  let
    val _ = Multithreading.tracing 4 (fn () => name ^ ": locking");
    val _ = Mutex.lock lock;
    val _ = Multithreading.tracing 4 (fn () => name ^ ": locked");
    val result = Exn.capture (restore_attributes e) ();
    val _ = Mutex.unlock lock;
    val _ = Multithreading.tracing 4 (fn () => name ^ ": unlocked");
  in Exn.release result end) ();

fun wait name = (*requires SYNCHRONIZED*)
  ConditionVar.wait (cond, lock);

fun wait_timeout name timeout = (*requires SYNCHRONIZED*)
  ConditionVar.waitUntil (cond, lock, Time.+ (Time.now (), timeout));

fun notify_all () = (*requires SYNCHRONIZED*)
  ConditionVar.broadcast cond;

end;


(* execute *)

fun execute name (task, group, run) =
  let
    val _ = set_thread_data (SOME (task, group));
    val _ = Multithreading.tracing 4 (fn () => name ^ ": running");
    val ok = run ();
    val _ = Multithreading.tracing 4 (fn () => name ^ ": finished");
    val _ = set_thread_data NONE;
    val _ = SYNCHRONIZED "execute" (fn () =>
     (change queue (TaskQueue.finish task);
      if ok then ()
      else if TaskQueue.cancel (! queue) group then ()
      else change canceled (cons group);
      notify_all ()));
  in () end;


(* worker threads *)

fun change_active active = (*requires SYNCHRONIZED*)
  let
    val _ = change workers (AList.update Thread.equal (Thread.self (), active));
    val ws = ! workers;
    val m = string_of_int (length ws);
    val n = string_of_int (length (filter #2 ws));
  in Multithreading.tracing 1 (fn () => "SCHEDULE: " ^ m ^ " workers, " ^ n ^ " active") end;


fun worker_wait name = (*requires SYNCHRONIZED*)
  (change_active false; wait name; change_active true);

fun worker_next name = (*requires SYNCHRONIZED*)
  if ! excessive > 0 then
    (dec excessive;
     change workers (filter_out (fn (thread, _) => Thread.equal (thread, Thread.self ())));
     notify_all ();
     NONE)
  else
    (case change_result queue TaskQueue.dequeue of
      NONE => (worker_wait name; worker_next name)
    | some => some);

fun worker_loop name =
  (case SYNCHRONIZED name (fn () => worker_next name) of
    NONE => Multithreading.tracing 4 (fn () => name ^ ": exit")
  | SOME work => (execute name work; worker_loop name));

fun worker_start name = (*requires SYNCHRONIZED*)
  change workers (cons (SimpleThread.fork false (fn () => worker_loop name), true));


(* scheduler *)

fun scheduler_next () = (*requires SYNCHRONIZED*)
  let
    (*worker threads*)
    val _ =
      (case List.partition (Thread.isActive o #1) (! workers) of
        (_, []) => ()
      | (active, inactive) =>
          (workers := active; Multithreading.tracing 0 (fn () =>
            "SCHEDULE: disposed " ^ string_of_int (length inactive) ^ " dead worker threads")));

    val m = if ! do_shutdown then 0 else Multithreading.max_threads_value ();
    val l = length (! workers);
    val _ = excessive := l - m;
    val _ =
      if m > l then funpow (m - l) (fn () => worker_start ("worker " ^ serial_string ())) ()
      else ();

    (*canceled groups*)
    val _ =  change canceled (filter_out (TaskQueue.cancel (! queue)));

    (*shutdown*)
    val continue = not (! do_shutdown andalso null (! workers));
    val _ = if continue then () else scheduler := NONE;

    val _ = notify_all ();
    val _ = wait_timeout "scheduler" (Time.fromSeconds 1);
  in continue end;

fun scheduler_loop () =
 (while SYNCHRONIZED "scheduler" scheduler_next do ();
  Multithreading.tracing 4 (fn () => "scheduler: exit"));

fun scheduler_active () = (*requires SYNCHRONIZED*)
  (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread);

fun scheduler_check () = SYNCHRONIZED "scheduler_check" (fn () =>
  if not (scheduler_active ()) then
    (do_shutdown := false; scheduler := SOME (SimpleThread.fork false scheduler_loop))
  else if ! do_shutdown then error "Scheduler shutdown in progress"
  else ());


(* future values: fork independent computation *)

fun future opt_group deps pri (e: unit -> 'a) =
  let
    val _ = scheduler_check ();

    val group = (case opt_group of SOME group => group | NONE => TaskQueue.new_group ());

    val result = ref (NONE: 'a Exn.result option);
    val run = Multithreading.with_attributes (Thread.getAttributes ())
      (fn _ => fn ok =>
        let val res = if ok then Exn.capture e () else Exn.Exn Interrupt
        in result := SOME res; is_some (Exn.get_result res) end);

    val task = SYNCHRONIZED "future" (fn () =>
      change_result queue (TaskQueue.enqueue group deps pri run) before notify_all ());
  in Future {task = task, group = group, result = result} end;

fun fork e = future (Option.map #2 (thread_data ())) [] true e;
fun fork_irrelevant e = future (Option.map #2 (thread_data ())) [] false e;


(* join: retrieve results *)

fun join_results xs =
  let
    val _ = scheduler_check ();
    val _ = Multithreading.self_critical () andalso
      error "Cannot join future values within critical section";

    fun unfinished () =
      xs |> map_filter (fn Future {task, result = ref NONE, ...} => SOME task | _ => NONE);

    (*alien thread -- refrain from contending for resources*)
    fun passive_join () = (*requires SYNCHRONIZED*)
      (case unfinished () of [] => ()
      | _ => (wait "passive_join"; passive_join ()));

    (*proper worker thread -- actively work towards results*)
    fun active_join () = (*requires SYNCHRONIZED*)
      (case unfinished () of [] => ()
      | tasks =>
          (case change_result queue (TaskQueue.dequeue_towards tasks) of
            NONE => (worker_wait "active_join"; active_join ())
          | SOME work => (execute "active_join" work; active_join ())));

    val _ =
      (case thread_data () of
        NONE => SYNCHRONIZED "passive_join" passive_join
      | SOME (task, _) => SYNCHRONIZED "active_join" (fn () =>
         (change queue (TaskQueue.depend (unfinished ()) task); active_join ())));

  in xs |> map (fn Future {result = ref (SOME res), ...} => res) end;

fun join x = Exn.release (singleton join_results x);


(* misc operations *)

(*focus: collection of high-priority task*)
fun focus tasks = SYNCHRONIZED "interrupt" (fn () =>
  change queue (TaskQueue.focus tasks));

(*interrupt: permissive signal, may get ignored*)
fun interrupt_task id = SYNCHRONIZED "interrupt"
  (fn () => TaskQueue.interrupt_external (! queue) id);

(*cancel: present and future group members will be interrupted eventually*)
fun cancel x =
 (scheduler_check ();
  SYNCHRONIZED "cancel" (fn () => (change canceled (cons (group_of x)); notify_all ())));


(*global join and shutdown*)
fun shutdown () =
  if Multithreading.available then
   (scheduler_check ();
    SYNCHRONIZED "shutdown" (fn () =>
     (while not (scheduler_active ()) do wait "shutdown: scheduler inactive";
      while not (TaskQueue.is_empty (! queue)) do wait "shutdown: join";
      do_shutdown := true;
      notify_all ();
      while not (null (! workers)) do wait "shutdown: workers";
      while scheduler_active () do wait "shutdown: scheduler still active")))
  else ();

end;
