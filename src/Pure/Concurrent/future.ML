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
  val thread_data: unit -> (string * task * group) option
  type 'a T
  val task_of: 'a T -> task
  val group_of: 'a T -> group
  val str_of: 'a T -> string
  val is_finished: 'a T -> bool
  val future: group option -> task list -> bool -> (unit -> 'a) -> 'a T
  val fork: (unit -> 'a) -> 'a T
  val fork_background: (unit -> 'a) -> 'a T
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

local val tag = Universal.tag () : (string * task * group) option Universal.tag in
  fun thread_data () = the_default NONE (Thread.getLocal tag);
  fun setmp_thread_data data f x = Library.setmp_thread_data tag (thread_data ()) (SOME data) f x;
end;


(* datatype future *)

datatype 'a T = Future of
 {task: task,
  group: group,
  result: 'a Exn.result option ref};

fun task_of (Future {task, ...}) = task;
fun group_of (Future {group, ...}) = group;

fun str_of (Future {result, ...}) =
  (case ! result of
    NONE => "<future>"
  | SOME (Exn.Result _) => "<finished future>"
  | SOME (Exn.Exn _) => "<failed future>");

fun is_finished (Future {result, ...}) = is_some (! result);



(** scheduling **)

(* global state *)

val queue = ref TaskQueue.empty;
val next = ref 0;
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

fun SYNCHRONIZED name e = Exn.release (uninterruptible (fn restore_attributes => fn () =>
  let
    val _ =
      if Mutex.trylock lock then ()
      else
       (Multithreading.tracing 3 (fn () => name ^ ": locking ...");
        Mutex.lock lock;
        Multithreading.tracing 3 (fn () => name ^ ": ... locked"));
    val result = Exn.capture (restore_attributes e) ();
    val _ = Mutex.unlock lock;
  in result end) ());

fun wait name = (*requires SYNCHRONIZED*)
 (Multithreading.tracing 3 (fn () => name ^ ": wait ...");
  ConditionVar.wait (cond, lock);
  Multithreading.tracing 3 (fn () => name ^ ": ... continue"));

fun wait_timeout name timeout = (*requires SYNCHRONIZED*)
 (Multithreading.tracing 3 (fn () => name ^ ": wait ...");
  ConditionVar.waitUntil (cond, lock, Time.+ (Time.now (), timeout));
  Multithreading.tracing 3 (fn () => name ^ ": ... continue"));

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

fun execute name (task, group, run) =
  let
    val _ = trace_active ();
    val ok = setmp_thread_data (name, task, group) run ();
    val _ = SYNCHRONIZED "execute" (fn () =>
     (change queue (TaskQueue.finish task);
      if ok then ()
      else if TaskQueue.cancel (! queue) group then ()
      else change canceled (cons group);
      notify_all ()));
  in () end;


(* worker threads *)

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
    NONE => Multithreading.tracing 3 (fn () => name ^ ": exit")
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
    val _ =  change canceled (filter_out (TaskQueue.cancel (! queue)));

    (*shutdown*)
    val continue = not (! do_shutdown andalso null (! workers));
    val _ = if continue then () else scheduler := NONE;

    val _ = notify_all ();
    val _ = wait_timeout "scheduler" (Time.fromSeconds 3);
  in continue end;

fun scheduler_loop () =
 (while SYNCHRONIZED "scheduler" scheduler_next do ();
  Multithreading.tracing 3 (fn () => "scheduler: exit"));

fun scheduler_active () = (*requires SYNCHRONIZED*)
  (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread);

fun scheduler_check name = SYNCHRONIZED name (fn () =>
  if not (scheduler_active ()) then
    (Multithreading.tracing 3 (fn () => "scheduler: fork");
     do_shutdown := false; scheduler := SOME (SimpleThread.fork false scheduler_loop))
  else if ! do_shutdown then error "Scheduler shutdown in progress"
  else ());


(* future values: fork independent computation *)

fun future opt_group deps pri (e: unit -> 'a) =
  let
    val _ = scheduler_check "future check";

    val group = (case opt_group of SOME group => group | NONE => TaskQueue.new_group ());

    val result = ref (NONE: 'a Exn.result option);
    val run = Multithreading.with_attributes (Thread.getAttributes ())
      (fn _ => fn ok =>
        let
          val res = if ok then Exn.capture e () else Exn.Exn Exn.Interrupt;
          val res_ok =
            (case res of
              Exn.Result _ => true
            | Exn.Exn Exn.Interrupt => true
            | _ => false);
        in result := SOME res; res_ok end);

    val task = SYNCHRONIZED "future" (fn () =>
      change_result queue (TaskQueue.enqueue group deps pri run) before notify_all ());
  in Future {task = task, group = group, result = result} end;

fun fork_common pri = future (Option.map #3 (thread_data ())) [] pri;

fun fork e = fork_common true e;
fun fork_background e = fork_common false e;


(* join: retrieve results *)

fun join_results [] = []
  | join_results xs = uninterruptible (fn _ => fn () =>
      let
        val _ = scheduler_check "join check";
        val _ = Multithreading.self_critical () andalso
          error "Cannot join future values within critical section";

        fun join_loop _ [] = ()
          | join_loop name tasks =
              (case SYNCHRONIZED name (fn () =>
                  change_result queue (TaskQueue.dequeue_towards tasks)) of
                NONE => ()
              | SOME (work, tasks') => (execute name work; join_loop name tasks'));
        val _ =
          (case thread_data () of
            NONE =>
              (*alien thread -- refrain from contending for resources*)
              while exists (not o is_finished) xs
              do SYNCHRONIZED "join_thread" (fn () => wait "join_thread")
          | SOME (name, task, _) =>
              (*proper task -- actively work towards results*)
              let
                val unfinished = xs |> map_filter
                  (fn Future {task, result = ref NONE, ...} => SOME task | _ => NONE);
                val _ = SYNCHRONIZED "join" (fn () =>
                  (change queue (TaskQueue.depend unfinished task); notify_all ()));
                val _ = join_loop ("join_loop: " ^ name) unfinished;
                val _ =
                  while exists (not o is_finished) xs
                  do SYNCHRONIZED "join_task" (fn () => worker_wait "join_task");
              in () end);

      in xs |> map (fn Future {result = ref (SOME res), ...} => res) end) ();

fun join x = Exn.release (singleton join_results x);


(* misc operations *)

(*focus: collection of high-priority task*)
fun focus tasks = SYNCHRONIZED "focus" (fn () =>
  change queue (TaskQueue.focus tasks));

(*interrupt: permissive signal, may get ignored*)
fun interrupt_task id = SYNCHRONIZED "interrupt"
  (fn () => TaskQueue.interrupt_external (! queue) id);

(*cancel: present and future group members will be interrupted eventually*)
fun cancel x =
 (scheduler_check "cancel check";
  SYNCHRONIZED "cancel" (fn () => (change canceled (cons (group_of x)); notify_all ())));


(*global join and shutdown*)
fun shutdown () =
  if Multithreading.available then
   (scheduler_check "shutdown check";
    SYNCHRONIZED "shutdown" (fn () =>
     (while not (scheduler_active ()) do wait "shutdown: scheduler inactive";
      while not (TaskQueue.is_empty (! queue)) do wait "shutdown: join";
      do_shutdown := true;
      notify_all ();
      while not (null (! workers)) do wait "shutdown: workers";
      while scheduler_active () do wait "shutdown: scheduler still active";
      OS.Process.sleep (Time.fromMilliseconds 300))))
  else ();

end;
