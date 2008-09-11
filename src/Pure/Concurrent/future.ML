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
  val future: group option -> task list -> (unit -> 'a) -> 'a T
  val fork: (unit -> 'a) -> 'a T
  val join_results: 'a T list -> 'a Exn.result list
  val join: 'a T -> 'a
  val focus: task list -> unit
  val cancel: 'a T -> unit
  val interrupt_task: string -> unit
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


(* requests *)

datatype request = Shutdown | Cancel of group;
val requests = Mailbox.create () : request Mailbox.T;

fun shutdown_request () = Mailbox.send requests Shutdown;
fun cancel_request group = Mailbox.send requests (Cancel group);


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
  let
    val _ = Multithreading.tracing 4 (fn () => name ^ ": waiting");
    val _ = ConditionVar.wait (cond, lock);
    val _ = Multithreading.tracing 4 (fn () => name ^ ": notified");
  in () end;

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
      else cancel_request group;
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
  change workers
    (cons (Thread.fork (fn () => worker_loop name, Multithreading.no_interrupts), true));


(* scheduler *)

fun scheduler_fork shutdown = SYNCHRONIZED "scheduler_fork" (fn () =>
  let
    val _ =
      (case List.partition (Thread.isActive o #1) (! workers) of
        (_, []) => ()
      | (active, inactive) =>
          (workers := active; Multithreading.tracing 0 (fn () =>
            "SCHEDULE: disposed " ^ string_of_int (length inactive) ^ " dead worker threads")));

    val m = if shutdown then 0 else Multithreading.max_threads_value ();
    val l = length (! workers);
    val _ = excessive := l - m;
    val _ =
      if m > l then funpow (m - l) (fn () => worker_start ("worker " ^ serial_string ())) ()
      else ();
    val terminate = shutdown andalso null (! workers);
    val _ = if terminate then scheduler := NONE else ();
    val _ = notify_all ();
  in terminate end);

fun scheduler_loop (shutdown, canceled) =
  if scheduler_fork shutdown then Multithreading.tracing 4 (fn () => "scheduler: exit")
  else
    let
      val canceled' = SYNCHRONIZED "scheduler"
        (fn () => filter_out (TaskQueue.cancel (! queue)) canceled);
    in
      (case Mailbox.receive_timeout (Time.fromSeconds 1) requests of
        SOME Shutdown => scheduler_loop (true, canceled')
      | SOME (Cancel group) => scheduler_loop (shutdown, group :: canceled')
      | NONE => scheduler_loop (shutdown, canceled'))
    end;

fun scheduler_active () = (*requires SYNCHRONIZED*)
  (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread);

fun scheduler_check () = SYNCHRONIZED "scheduler_check" (fn () =>
  if (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread) then ()
  else scheduler :=
    SOME (Thread.fork (fn () => scheduler_loop (false, []), Multithreading.no_interrupts)));


(* future values: fork independent computation *)

fun future opt_group deps (e: unit -> 'a) =
  let
    val _ = scheduler_check ();

    val group = (case opt_group of SOME group => group | NONE => TaskQueue.new_group ());

    val result = ref (NONE: 'a Exn.result option);
    val run = Multithreading.with_attributes (Thread.getAttributes ())
      (fn _ => fn ok =>
        let val res = if ok then Exn.capture e () else Exn.Exn Interrupt
        in result := SOME res; is_some (Exn.get_result res) end);

    val task = SYNCHRONIZED "future" (fn () =>
      change_result queue (TaskQueue.enqueue group deps run) before notify_all ());
  in Future {task = task, group = group, result = result} end;

fun fork e = future (Option.map #2 (thread_data ())) [] e;


(* join: retrieve results *)

fun join_results xs =
  let
    val _ = Multithreading.self_critical () andalso
      error "Cannot join future values within critical section";
    val _ = scheduler_check ();

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

(*cancel: present and future group members will be interrupted eventually*)
fun cancel x = (scheduler_check (); cancel_request (group_of x));

(*interrupt: permissive signal, may get ignored*)
fun interrupt_task id = SYNCHRONIZED "interrupt"
  (fn () => TaskQueue.interrupt_external (! queue) id);

(*global join and shutdown*)
fun shutdown () =
 (scheduler_check ();
  SYNCHRONIZED "shutdown" (fn () =>
   (while not (TaskQueue.is_empty (! queue)) do wait "shutdown: join";
    shutdown_request ();
    while not (null (! workers)) do wait "shutdown: workers";
    while scheduler_active () do wait "shutdown: scheduler")));

end;
