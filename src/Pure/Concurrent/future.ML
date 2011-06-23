(*  Title:      Pure/Concurrent/future.ML
    Author:     Makarius

Future values, see also
http://www4.in.tum.de/~wenzelm/papers/parallel-isabelle.pdf
http://www4.in.tum.de/~wenzelm/papers/parallel-ml.pdf

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

  * Promised futures are fulfilled by external means.  There is no
    associated evaluation task, but other futures can depend on them
    as usual.
*)

signature FUTURE =
sig
  val worker_task: unit -> Task_Queue.task option
  val worker_group: unit -> Task_Queue.group option
  val worker_subgroup: unit -> Task_Queue.group
  type 'a future
  val task_of: 'a future -> Task_Queue.task
  val peek: 'a future -> 'a Exn.result option
  val is_finished: 'a future -> bool
  val forks:
    {name: string, group: Task_Queue.group option, deps: Task_Queue.task list, pri: int} ->
      (unit -> 'a) list -> 'a future list
  val fork_pri: int -> (unit -> 'a) -> 'a future
  val fork: (unit -> 'a) -> 'a future
  val join_results: 'a future list -> 'a Exn.result list
  val join_result: 'a future -> 'a Exn.result
  val join: 'a future -> 'a
  val value: 'a -> 'a future
  val map: ('a -> 'b) -> 'a future -> 'b future
  val cond_forks:
    {name: string, group: Task_Queue.group option, deps: Task_Queue.task list, pri: int} ->
      (unit -> 'a) list -> 'a future list
  val promise_group: Task_Queue.group -> 'a future
  val promise: unit -> 'a future
  val fulfill_result: 'a future -> 'a Exn.result -> unit
  val fulfill: 'a future -> 'a -> unit
  val interruptible_task: ('a -> 'b) -> 'a -> 'b
  val cancel_group: Task_Queue.group -> unit
  val cancel: 'a future -> unit
  val shutdown: unit -> unit
  val status: (unit -> 'a) -> 'a
end;

structure Future: FUTURE =
struct

(** future values **)

(* identifiers *)

local
  val tag = Universal.tag () : Task_Queue.task option Universal.tag;
in
  fun worker_task () = the_default NONE (Thread.getLocal tag);
  fun setmp_worker_task data f x =
    Library.setmp_thread_data tag (worker_task ()) (SOME data) f x;
end;

val worker_group = Option.map Task_Queue.group_of_task o worker_task;
fun worker_subgroup () = Task_Queue.new_group (worker_group ());

fun worker_joining e =
  (case worker_task () of
    NONE => e ()
  | SOME task => Task_Queue.joining task e);

fun worker_waiting deps e =
  (case worker_task () of
    NONE => e ()
  | SOME task => Task_Queue.waiting task deps e);


(* datatype future *)

type 'a result = 'a Exn.result Single_Assignment.var;

datatype 'a future = Future of
 {promised: bool,
  task: Task_Queue.task,
  result: 'a result};

fun task_of (Future {task, ...}) = task;
fun result_of (Future {result, ...}) = result;

fun peek x = Single_Assignment.peek (result_of x);
fun is_finished x = is_some (peek x);

fun assign_result group result res =
  let
    val _ = Single_Assignment.assign result res
      handle exn as Fail _ =>
        (case Single_Assignment.peek result of
          SOME (Exn.Exn e) => reraise (if Exn.is_interrupt e then e else exn)
        | _ => reraise exn);
    val ok =
      (case the (Single_Assignment.peek result) of
        Exn.Exn exn => (Task_Queue.cancel_group group exn; false)
      | Exn.Result _ => true);
  in ok end;



(** scheduling **)

(* synchronization *)

val scheduler_event = ConditionVar.conditionVar ();
val work_available = ConditionVar.conditionVar ();
val work_finished = ConditionVar.conditionVar ();

local
  val lock = Mutex.mutex ();
in

fun SYNCHRONIZED name = Simple_Thread.synchronized name lock;

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


(* global state *)

val queue = Unsynchronized.ref Task_Queue.empty;
val next = Unsynchronized.ref 0;
val scheduler = Unsynchronized.ref (NONE: Thread.thread option);
val canceled = Unsynchronized.ref ([]: Task_Queue.group list);
val do_shutdown = Unsynchronized.ref false;
val max_workers = Unsynchronized.ref 0;
val max_active = Unsynchronized.ref 0;
val worker_trend = Unsynchronized.ref 0;

datatype worker_state = Working | Waiting | Sleeping;
val workers = Unsynchronized.ref ([]: (Thread.thread * worker_state Unsynchronized.ref) list);

fun count_workers state = (*requires SYNCHRONIZED*)
  fold (fn (_, state_ref) => fn i => if ! state_ref = state then i + 1 else i) (! workers) 0;


(* execute future jobs *)

fun future_job group (e: unit -> 'a) =
  let
    val result = Single_Assignment.var "future" : 'a result;
    val pos = Position.thread_data ();
    fun job ok =
      let
        val res =
          if ok then
            Exn.capture (fn () =>
              Multithreading.with_attributes Multithreading.private_interrupts
                (fn _ => Position.setmp_thread_data pos e ()) before
              Multithreading.interrupted ()) ()
          else Exn.interrupt_exn;
      in assign_result group result res end;
  in (result, job) end;

fun cancel_now group = (*requires SYNCHRONIZED*)
  Task_Queue.cancel (! queue) group;

fun cancel_later group = (*requires SYNCHRONIZED*)
 (Unsynchronized.change canceled (insert Task_Queue.eq_group group);
  broadcast scheduler_event);

fun execute (task, jobs) =
  let
    val group = Task_Queue.group_of_task task;
    val valid = not (Task_Queue.is_canceled group);
    val ok =
      Task_Queue.running task (fn () =>
        setmp_worker_task task (fn () =>
          fold (fn job => fn ok => job valid andalso ok) jobs true) ());
    val _ = Multithreading.tracing 2 (fn () =>
      let
        val s = Task_Queue.str_of_task task;
        fun micros time = string_of_int (Time.toNanoseconds time div 1000);
        val (run, wait, deps) = Task_Queue.timing_of_task task;
      in "TASK " ^ s ^ " " ^ micros run ^ " " ^ micros wait ^ " (" ^ commas deps ^ ")" end);
    val _ = SYNCHRONIZED "finish" (fn () =>
      let
        val maximal = Unsynchronized.change_result queue (Task_Queue.finish task);
        val _ =
          if ok then ()
          else if cancel_now group then ()
          else cancel_later group;
        val _ = broadcast work_finished;
        val _ = if maximal then () else signal work_available;
      in () end);
  in () end;


(* worker threads *)

fun worker_wait active cond = (*requires SYNCHRONIZED*)
  let
    val state =
      (case AList.lookup Thread.equal (! workers) (Thread.self ()) of
        SOME state => state
      | NONE => raise Fail "Unregistered worker thread");
    val _ = state := (if active then Waiting else Sleeping);
    val _ = wait cond;
    val _ = state := Working;
  in () end;

fun worker_next () = (*requires SYNCHRONIZED*)
  if length (! workers) > ! max_workers then
    (Unsynchronized.change workers (AList.delete Thread.equal (Thread.self ()));
     signal work_available;
     NONE)
  else if count_workers Working > ! max_active then
    (worker_wait false work_available; worker_next ())
  else
    (case Unsynchronized.change_result queue (Task_Queue.dequeue (Thread.self ())) of
      NONE => (worker_wait false work_available; worker_next ())
    | some => (signal work_available; some));

fun worker_loop name =
  (case SYNCHRONIZED name (fn () => worker_next ()) of
    NONE => ()
  | SOME work => (execute work; worker_loop name));

fun worker_start name = (*requires SYNCHRONIZED*)
  Unsynchronized.change workers (cons (Simple_Thread.fork false (fn () => worker_loop name),
    Unsynchronized.ref Working));


(* scheduler *)

val status_ticks = Unsynchronized.ref 0;

val last_round = Unsynchronized.ref Time.zeroTime;
val next_round = seconds 0.05;

fun scheduler_next () = (*requires SYNCHRONIZED*)
  let
    val now = Time.now ();
    val tick = Time.<= (Time.+ (! last_round, next_round), now);
    val _ = if tick then last_round := now else ();


    (* queue and worker status *)

    val _ =
      if tick then Unsynchronized.change status_ticks (fn i => (i + 1) mod 10) else ();
    val _ =
      if tick andalso ! status_ticks = 0 then
        Multithreading.tracing 1 (fn () =>
          let
            val {ready, pending, running, passive} = Task_Queue.status (! queue);
            val total = length (! workers);
            val active = count_workers Working;
            val waiting = count_workers Waiting;
          in
            "SCHEDULE " ^ Time.toString now ^ ": " ^
              string_of_int ready ^ " ready, " ^
              string_of_int pending ^ " pending, " ^
              string_of_int running ^ " running, " ^
              string_of_int passive ^ " passive; " ^
              string_of_int total ^ " workers, " ^
              string_of_int active ^ " active, " ^
              string_of_int waiting ^ " waiting "
          end)
      else ();

    val _ =
      if forall (Thread.isActive o #1) (! workers) then ()
      else
        let
          val (alive, dead) = List.partition (Thread.isActive o #1) (! workers);
          val _ = workers := alive;
        in
          Multithreading.tracing 0 (fn () =>
            "SCHEDULE: disposed " ^ string_of_int (length dead) ^ " dead worker threads")
        end;


    (* worker pool adjustments *)

    val max_active0 = ! max_active;
    val max_workers0 = ! max_workers;

    val m = if ! do_shutdown then 0 else Multithreading.max_threads_value ();
    val _ = max_active := m;

    val mm =
      if ! do_shutdown then 0
      else if m = 9999 then 1
      else Int.min (Int.max (count_workers Working + 2 * count_workers Waiting, m), 4 * m);
    val _ =
      if tick andalso mm > ! max_workers then
        Unsynchronized.change worker_trend (fn w => if w < 0 then 0 else w + 1)
      else if tick andalso mm < ! max_workers then
        Unsynchronized.change worker_trend (fn w => if w > 0 then 0 else w - 1)
      else ();
    val _ =
      if mm = 0 orelse ! worker_trend > 50 orelse ! worker_trend < ~50 then
        max_workers := mm
      else if ! worker_trend > 5 andalso ! max_workers < 2 * m then
        max_workers := Int.min (mm, 2 * m)
      else ();

    val missing = ! max_workers - length (! workers);
    val _ =
      if missing > 0 then
        funpow missing (fn () =>
          ignore (worker_start ("worker " ^ string_of_int (Unsynchronized.inc next)))) ()
      else ();

    val _ =
      if ! max_active = max_active0 andalso ! max_workers = max_workers0 then ()
      else signal work_available;


    (* canceled groups *)

    val _ =
      if null (! canceled) then ()
      else
       (Multithreading.tracing 1 (fn () =>
          string_of_int (length (! canceled)) ^ " canceled groups");
        Unsynchronized.change canceled (filter_out cancel_now);
        broadcast_work ());


    (* delay loop *)

    val _ = Exn.release (wait_timeout next_round scheduler_event);


    (* shutdown *)

    val _ = if Task_Queue.all_passive (! queue) then do_shutdown := true else ();
    val continue = not (! do_shutdown andalso null (! workers));
    val _ = if continue then () else scheduler := NONE;

    val _ = broadcast scheduler_event;
  in continue end
  handle exn =>
    if Exn.is_interrupt exn then
     (Multithreading.tracing 1 (fn () => "Interrupt");
      List.app cancel_later (Task_Queue.cancel_all (! queue));
      broadcast_work (); true)
    else reraise exn;

fun scheduler_loop () =
  while
    Multithreading.with_attributes
      (Multithreading.sync_interrupts Multithreading.public_interrupts)
      (fn _ => SYNCHRONIZED "scheduler" (fn () => scheduler_next ()))
  do ();

fun scheduler_active () = (*requires SYNCHRONIZED*)
  (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread);

fun scheduler_check () = (*requires SYNCHRONIZED*)
 (do_shutdown := false;
  if scheduler_active () then ()
  else scheduler := SOME (Simple_Thread.fork false scheduler_loop));



(** futures **)

(* fork *)

fun forks {name, group, deps, pri} es =
  if null es then []
  else
    let
      val grp =
        (case group of
          NONE => worker_subgroup ()
        | SOME grp => grp);
      fun enqueue e queue =
        let
          val (result, job) = future_job grp e;
          val (task, queue') = Task_Queue.enqueue name grp deps pri job queue;
          val future = Future {promised = false, task = task, result = result};
        in (future, queue') end;
    in
      SYNCHRONIZED "enqueue" (fn () =>
        let
          val (futures, queue') = fold_map enqueue es (! queue);
          val _ = queue := queue';
          val minimal = forall (not o Task_Queue.known_task queue') deps;
          val _ = if minimal then signal work_available else ();
          val _ = scheduler_check ();
        in futures end)
    end;

fun fork_pri pri e = singleton (forks {name = "", group = NONE, deps = [], pri = pri}) e;
fun fork e = fork_pri 0 e;


(* join *)

local

fun get_result x =
  (case peek x of
    NONE => Exn.Exn (Fail "Unfinished future")
  | SOME res =>
      if Exn.is_interrupt_exn res then
        (case Exn.flatten_list (Task_Queue.group_status (Task_Queue.group_of_task (task_of x))) of
          [] => res
        | exns => Exn.Exn (Exn.EXCEPTIONS exns))
      else res);

fun join_next deps = (*requires SYNCHRONIZED*)
  if null deps then NONE
  else
    (case Unsynchronized.change_result queue (Task_Queue.dequeue_deps (Thread.self ()) deps) of
      (NONE, []) => NONE
    | (NONE, deps') =>
        (worker_waiting deps' (fn () => worker_wait true work_finished); join_next deps')
    | (SOME work, deps') => SOME (work, deps'));

fun execute_work NONE = ()
  | execute_work (SOME (work, deps')) = (worker_joining (fn () => execute work); join_work deps')
and join_work deps =
  Multithreading.with_attributes Multithreading.no_interrupts
    (fn _ => execute_work (SYNCHRONIZED "join" (fn () => join_next deps)));

in

fun join_results xs =
  let
    val _ =
      if forall is_finished xs then ()
      else if Multithreading.self_critical () then
        error "Cannot join future values within critical section"
      else if is_some (worker_task ()) then join_work (map task_of xs)
      else List.app (ignore o Single_Assignment.await o result_of) xs;
  in map get_result xs end;

end;

fun join_result x = singleton join_results x;
fun join x = Exn.release (join_result x);


(* fast-path versions -- bypassing full task management *)

fun value (x: 'a) =
  let
    val task = Task_Queue.dummy_task ();
    val group = Task_Queue.group_of_task task;
    val result = Single_Assignment.var "value" : 'a result;
    val _ = assign_result group result (Exn.Result x);
  in Future {promised = false, task = task, result = result} end;

fun map_future f x =
  let
    val task = task_of x;
    val group = Task_Queue.new_group (SOME (Task_Queue.group_of_task task));
    val (result, job) = future_job group (fn () => f (join x));

    val extended = SYNCHRONIZED "extend" (fn () =>
      (case Task_Queue.extend task job (! queue) of
        SOME queue' => (queue := queue'; true)
      | NONE => false));
  in
    if extended then Future {promised = false, task = task, result = result}
    else
      singleton
        (forks {name = "Future.map", group = SOME group,
          deps = [task], pri = Task_Queue.pri_of_task task})
        (fn () => f (join x))
  end;

fun cond_forks args es =
  if Multithreading.enabled () then forks args es
  else map (fn e => value (e ())) es;


(* promised futures -- fulfilled by external means *)

fun promise_group group : 'a future =
  let
    val result = Single_Assignment.var "promise" : 'a result;
    fun abort () = assign_result group result Exn.interrupt_exn
      handle Fail _ => true
        | exn =>
            if Exn.is_interrupt exn then raise Fail "Concurrent attempt to fulfill promise"
            else reraise exn;
    val task = SYNCHRONIZED "enqueue_passive" (fn () =>
      Unsynchronized.change_result queue (Task_Queue.enqueue_passive group abort));
  in Future {promised = true, task = task, result = result} end;

fun promise () = promise_group (worker_subgroup ());

fun fulfill_result (Future {promised, task, result}) res =
  if not promised then raise Fail "Not a promised future"
  else
    let
      val group = Task_Queue.group_of_task task;
      fun job ok = assign_result group result (if ok then res else Exn.interrupt_exn);
      val _ =
        Multithreading.with_attributes Multithreading.no_interrupts (fn _ =>
          let
            val still_passive =
              SYNCHRONIZED "fulfill_result" (fn () =>
                Unsynchronized.change_result queue
                  (Task_Queue.dequeue_passive (Thread.self ()) task));
          in if still_passive then execute (task, [job]) else () end);
      val _ =
        if is_some (Single_Assignment.peek result) then ()
        else worker_waiting [task] (fn () => ignore (Single_Assignment.await result));
    in () end;

fun fulfill x res = fulfill_result x (Exn.Result res);


(* cancellation *)

fun interruptible_task f x =
  if Multithreading.available then
    Multithreading.with_attributes
      (if is_some (worker_task ())
       then Multithreading.private_interrupts
       else Multithreading.public_interrupts)
      (fn _ => f x)
  else interruptible f x;

(*cancel: present and future group members will be interrupted eventually*)
fun cancel_group group = SYNCHRONIZED "cancel" (fn () =>
 (if cancel_now group then () else cancel_later group;
  signal work_available; scheduler_check ()));

fun cancel x = cancel_group (Task_Queue.group_of_task (task_of x));


(* shutdown *)

fun shutdown () =
  if Multithreading.available then
    SYNCHRONIZED "shutdown" (fn () =>
     while scheduler_active () do
      (wait scheduler_event; broadcast_work ()))
  else ();


(* status markup *)

fun status e =
  let
    val task_props =
      (case worker_task () of
        NONE => I
      | SOME task => Markup.properties [(Markup.taskN, Task_Queue.str_of_task task)]);
    val _ = Output.status (Markup.markup (task_props Markup.forked) "");
    val x = e ();  (*sic -- report "joined" only for success*)
    val _ = Output.status (Markup.markup (task_props Markup.joined) "");
  in x end;


(*final declarations of this structure!*)
val map = map_future;

end;

type 'a future = 'a Future.future;

