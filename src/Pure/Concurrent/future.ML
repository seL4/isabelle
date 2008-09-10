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
  val group_of: 'a T -> group
  val shutdown_request: unit -> unit
  val future: group option -> task list -> (unit -> 'a) -> 'a T
  val fork: (unit -> 'a) -> 'a T
  val cancel: 'a T -> unit
  val join_all: 'a T list -> 'a list
  val join: 'a T -> 'a
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
val workers = ref ([]: Thread.thread list);
val scheduler = ref (NONE: Thread.thread option);

val excessive = ref 0;
val active = ref 0;

fun trace_active () =
  Multithreading.tracing 1 (fn () => "SCHEDULE: " ^ string_of_int (! active) ^ " active");


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

fun SYNCHRONIZED e = uninterruptible (fn restore_attributes => fn () =>
  let
    val _ = Mutex.lock lock;
    val result = Exn.capture (restore_attributes e) ();
    val _ = Mutex.unlock lock;
  in Exn.release result end) ();

fun wait name = (*requires SYNCHRONIZED*)
  let
    val _ = Multithreading.tracing 4 (fn () => name ^ " : waiting");
    val _ = ConditionVar.wait (cond, lock);
    val _ = Multithreading.tracing 4 (fn () => name ^ " : notified");
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
    val _ = SYNCHRONIZED (fn () =>
     (change queue (TaskQueue.finish task);
      if ok then ()
      else if TaskQueue.cancel (! queue) group then ()
      else cancel_request group;
      notify_all ()));
  in () end;


(* worker threads *)

fun change_active b = (*requires SYNCHRONIZED*)
  (change active (fn n => if b then n + 1 else n - 1); trace_active ());

fun worker_wait name = (*requires SYNCHRONIZED*)
  (change_active false; wait name; change_active true);

fun worker_next name = (*requires SYNCHRONIZED*)
  if ! excessive > 0 then
    (dec excessive;
     change_active false;
     change workers (remove Thread.equal (Thread.self ()));
     NONE)
  else
    (case change_result queue TaskQueue.dequeue of
      NONE => (worker_wait name; worker_next name)
    | some => some);

fun worker_loop name =
  (case SYNCHRONIZED (fn () => worker_next name) of
    NONE => ()
  | SOME work => (execute name work; worker_loop name));

fun worker_start name = (*requires SYNCHRONIZED*)
 (change_active true;
  change workers (cons (Thread.fork (fn () => worker_loop name, Multithreading.no_interrupts))));


(* scheduler *)

fun scheduler_fork shutdown = SYNCHRONIZED (fn () =>
  let
    val _ = trace_active ();
    val _ =
      (case List.partition Thread.isActive (! workers) of
        (_, []) => ()
      | (active, inactive) =>
          (workers := active; Multithreading.tracing 0 (fn () =>
            "SCHEDULE: disposed " ^ string_of_int (length inactive) ^ " inactive worker threads")));

    val m = if shutdown then 0 else Multithreading.max_threads_value ();
    val l = length (! workers);
    val _ = excessive := l - m;
    val _ = List.app (fn i => worker_start ("worker " ^ string_of_int i)) (l upto m - 1);
  in null (! workers) end);

fun scheduler_loop (shutdown, canceled) =
  if scheduler_fork shutdown then ()
  else
    let val canceled' = SYNCHRONIZED (fn () => filter_out (TaskQueue.cancel (! queue)) canceled) in
      (case Mailbox.receive_timeout (Time.fromSeconds 1) requests of
        SOME Shutdown => scheduler_loop (true, canceled')
      | SOME (Cancel group) => scheduler_loop (shutdown, group :: canceled')
      | NONE => scheduler_loop (shutdown, canceled'))
    end;

fun scheduler_check () = SYNCHRONIZED (fn () =>
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

    val task = SYNCHRONIZED (fn () =>
      change_result queue (TaskQueue.enqueue group deps run) before notify_all ());
  in Future {task = task, group = group, result = result} end;

fun fork e = future (Option.map #2 (thread_data ())) [] e;


(* join: retrieve results *)

fun join_all xs =
  let
    val _ = scheduler_check ();

    fun unfinished () =
      xs |> map_filter (fn Future {task, result = ref NONE, ...} => SOME task | _ => NONE);

    (*alien thread -- refrain from contending for resources*)
    fun passive_join () = (*requires SYNCHRONIZED*)
      (case unfinished () of [] => ()
      | _ => (wait "join"; passive_join ()));

    (*proper worker thread -- actively work towards results*)
    fun active_join () = (*requires SYNCHRONIZED*)
      (case unfinished () of [] => ()
      | tasks =>
          (case change_result queue (TaskQueue.dequeue_towards tasks) of
            NONE => (worker_wait "join"; active_join ())
          | SOME work => (execute "join" work; active_join ())));

    val _ =
      (case thread_data () of
        NONE => SYNCHRONIZED passive_join
      | SOME (task, _) => SYNCHRONIZED (fn () =>
         (change queue (TaskQueue.depend (unfinished ()) task); active_join ())));

    val res = xs |> map (fn Future {result = ref (SOME res), ...} => res);
  in
    (case get_first (fn Exn.Exn Interrupt => NONE | Exn.Exn e => SOME e | _ => NONE) res of
      NONE => map Exn.release res
    | SOME e => raise e)
  end;

fun join x = singleton join_all x;


(* termination *)

(*cancel: present and future group members will be interrupted eventually*)
fun cancel x = (scheduler_check (); cancel_request (group_of x));

(*interrupt: adhoc signal, permissive, may get ignored*)
fun interrupt_task id = SYNCHRONIZED (fn () => TaskQueue.interrupt (! queue) id);

end;
