(*  Title:      Pure/Concurrent/future.ML
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
  val enabled: unit -> bool
  type task = Task_Queue.task
  type group = Task_Queue.group
  val thread_data: unit -> (string * task) option
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
  val interrupt_task: string -> unit
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

local val tag = Universal.tag () : (string * task) option Universal.tag in
  fun thread_data () = the_default NONE (Thread.getLocal tag);
  fun setmp_thread_data data f x = Library.setmp_thread_data tag (thread_data ()) (SOME data) f x;
end;


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
  group = Task_Queue.new_group (),
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

local
  val lock = Mutex.mutex ();
  val cond = ConditionVar.conditionVar ();
in

fun SYNCHRONIZED name = SimpleThread.synchronized name lock;

fun wait () = (*requires SYNCHRONIZED*)
  ConditionVar.wait (cond, lock);

fun wait_timeout timeout = (*requires SYNCHRONIZED*)
  ignore (ConditionVar.waitUntil (cond, lock, Time.+ (Time.now (), timeout)));

fun notify_all () = (*requires SYNCHRONIZED*)
  ConditionVar.broadcast cond;

end;


(* worker activity *)

fun trace_active () =
  let
    val ws = ! workers;
    val m = string_of_int (length ws);
    val n = string_of_int (length (filter #2 ws));
  in Multithreading.tracing 1 (fn () => "SCHEDULE: " ^ m ^ " workers, " ^ n ^ " active") end;

fun change_active active = (*requires SYNCHRONIZED*)
  change workers (AList.update Thread.equal (Thread.self (), active));


(* execute *)

fun do_cancel group = (*requires SYNCHRONIZED*)
  change canceled (insert Task_Queue.eq_group group);

fun execute name (task, group, run) =
  let
    val _ = trace_active ();
    val ok = setmp_thread_data (name, task) run ();
    val _ = SYNCHRONIZED "execute" (fn () =>
     (change queue (Task_Queue.finish task);
      if ok then ()
      else if Task_Queue.cancel (! queue) group then ()
      else do_cancel group;
      notify_all ()));
  in () end;


(* worker threads *)

fun worker_wait () = (*requires SYNCHRONIZED*)
  (change_active false; wait (); change_active true);

fun worker_next () = (*requires SYNCHRONIZED*)
  if ! excessive > 0 then
    (dec excessive;
     change workers (filter_out (fn (thread, _) => Thread.equal (thread, Thread.self ())));
     notify_all ();
     NONE)
  else
    (case change_result queue Task_Queue.dequeue of
      NONE => (worker_wait (); worker_next ())
    | some => some);

fun worker_loop name =
  (case SYNCHRONIZED name worker_next of
    NONE => ()
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
    val _ = trace_active ();

    val m = if ! do_shutdown then 0 else Multithreading.max_threads_value ();
    val l = length (! workers);
    val _ = excessive := l - m;
    val _ =
      if m > l then funpow (m - l) (fn () => worker_start ("worker " ^ string_of_int (inc next))) ()
      else ();

    (*canceled groups*)
    val _ =  change canceled (filter_out (Task_Queue.cancel (! queue)));

    (*shutdown*)
    val continue = not (! do_shutdown andalso null (! workers));
    val _ = if continue then () else scheduler := NONE;

    val _ = notify_all ();
    val _ = interruptible (fn () => wait_timeout (Time.fromSeconds 1)) ()
      handle Exn.Interrupt => List.app do_cancel (Task_Queue.cancel_all (! queue));
  in continue end;

fun scheduler_loop () =
  while SYNCHRONIZED "scheduler" scheduler_next do ();

fun scheduler_active () = (*requires SYNCHRONIZED*)
  (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread);

fun scheduler_check name = SYNCHRONIZED name (fn () =>
  if not (scheduler_active ()) then
    (do_shutdown := false; scheduler := SOME (SimpleThread.fork false scheduler_loop))
  else if ! do_shutdown then error "Scheduler shutdown in progress"
  else ());


(* future values: fork independent computation *)

fun future opt_group deps pri (e: unit -> 'a) =
  let
    val _ = scheduler_check "future check";

    val group = (case opt_group of SOME group => group | NONE => Task_Queue.new_group ());

    val result = ref (NONE: 'a Exn.result option);
    val run = Multithreading.with_attributes (Thread.getAttributes ())
      (fn _ => fn ok =>
        let
          val res = if ok then Exn.capture e () else Exn.Exn Exn.Interrupt;
          val _ = result := SOME res;
          val res_ok =
            (case res of
              Exn.Result _ => true
            | Exn.Exn Exn.Interrupt => (Task_Queue.invalidate_group group; true)
            | _ => false);
        in res_ok end);

    val task = SYNCHRONIZED "future" (fn () =>
      change_result queue (Task_Queue.enqueue group deps pri run) before notify_all ());
  in Future {task = task, group = group, result = result} end;

fun fork e = future NONE [] 0 e;
fun fork_group group e = future (SOME group) [] 0 e;
fun fork_deps deps e = future NONE (map task_of deps) 0 e;
fun fork_pri pri e = future NONE [] pri e;


(* join: retrieve results *)

fun join_results [] = []
  | join_results xs = uninterruptible (fn _ => fn () =>
      let
        val _ = scheduler_check "join check";
        val _ = Multithreading.self_critical () andalso
          exists (not o is_finished) xs andalso
          error "Cannot join future values within critical section";

        fun join_loop _ [] = ()
          | join_loop name tasks =
              (case SYNCHRONIZED name (fn () =>
                  change_result queue (Task_Queue.dequeue_towards tasks)) of
                NONE => ()
              | SOME (work, tasks') => (execute name work; join_loop name tasks'));
        val _ =
          (case thread_data () of
            NONE =>
              (*alien thread -- refrain from contending for resources*)
              while exists (not o is_finished) xs
              do SYNCHRONIZED "join_thread" (fn () => wait ())
          | SOME (name, task) =>
              (*proper task -- actively work towards results*)
              let
                val unfinished = xs |> map_filter
                  (fn Future {task, result = ref NONE, ...} => SOME task | _ => NONE);
                val _ = SYNCHRONIZED "join" (fn () =>
                  (change queue (Task_Queue.depend unfinished task); notify_all ()));
                val _ = join_loop ("join_loop: " ^ name) unfinished;
                val _ =
                  while exists (not o is_finished) xs
                  do SYNCHRONIZED "join_task" (fn () => worker_wait ());
              in () end);

      in xs |> map (fn Future {result = ref (SOME res), ...} => res) end) ();

fun join_result x = singleton join_results x;
fun join x = Exn.release (join_result x);

fun map f x =
  let val task = task_of x
  in future NONE [task] (Task_Queue.pri_of_task task) (fn () => f (join x)) end;


(* misc operations *)

(*interrupt: permissive signal, may get ignored*)
fun interrupt_task id = SYNCHRONIZED "interrupt"
  (fn () => Task_Queue.interrupt_external (! queue) id);

(*cancel: present and future group members will be interrupted eventually*)
fun cancel x =
 (scheduler_check "cancel check";
  SYNCHRONIZED "cancel" (fn () => (do_cancel (group_of x); notify_all ())));


(*global join and shutdown*)
fun shutdown () =
  if Multithreading.available then
   (scheduler_check "shutdown check";
    SYNCHRONIZED "shutdown" (fn () =>
     (while not (scheduler_active ()) do wait ();
      while not (Task_Queue.is_empty (! queue)) do wait ();
      do_shutdown := true;
      notify_all ();
      while not (null (! workers)) do wait ();
      while scheduler_active () do wait ();
      OS.Process.sleep (Time.fromMilliseconds 300))))
  else ();

end;

type 'a future = 'a Future.future;

