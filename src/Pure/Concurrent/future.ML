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
  val interrupt_task: task -> unit
  val interrupt_group: group -> unit
  val interrupt_task_group: task -> unit
  val interrupt: 'a T -> unit
  val shutdown: unit -> unit
  val future: group option -> task list -> (unit -> 'a) -> 'a T
  val fork: (unit -> 'a) -> 'a T
  val join: 'a T -> 'a
end;

structure Future: FUTURE =
struct

(* identifiers *)

type task = TaskQueue.task;
type group = TaskQueue.group;

local val tag = Universal.tag () : task option Universal.tag in
  fun get_task () = the_default NONE (Thread.getLocal tag);
  fun set_task x = Thread.setLocal (tag, x);
end;

local val tag = Universal.tag () : group option Universal.tag in
  fun get_group () = the_default NONE (Thread.getLocal tag);
  fun set_group x = Thread.setLocal (tag, x);
end;


(* datatype future *)

datatype 'a T = Future of
 {task: task,
  group: group option,
  result: 'a Exn.result option ref};

fun task_of (Future {task, ...}) = task;
fun group_of (Future {group, ...}) = group;


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

fun wait name = (*requires SYNCHRONIZED*)
  let
    val _ = Multithreading.tracing 4 (fn () => name ^ " : waiting");
    val _ = ConditionVar.wait (cond, lock);
    val _ = Multithreading.tracing 4 (fn () => name ^ " : notified");
  in () end;

fun notify_all () = (*requires SYNCHRONIZED*)
  ConditionVar.broadcast cond;

end;


(** scheduling **)

datatype request = Shutdown | CancelGroup of group;
val requests = Mailbox.create () : request Mailbox.T;

val queue = ref TaskQueue.empty;
val scheduler = ref (NONE: Thread.thread option);
val workers = ref ([]: Thread.thread list);


(* signals *)

fun interrupt_task x = SYNCHRONIZED (fn () => TaskQueue.interrupt_task (! queue) x);
fun interrupt_group x = SYNCHRONIZED (fn () => TaskQueue.interrupt_group (! queue) x);
fun interrupt_task_group x = SYNCHRONIZED (fn () => TaskQueue.interrupt_task_group (! queue) x);

fun interrupt (Future {task, ...}) = interrupt_task_group task;

fun shutdown () = Mailbox.send Shutdown requests;


(* execute *)

fun execute name (task, group, run) =
  let
    val _ = set_task (SOME task);
    val _ = set_group group;
    val _ = Multithreading.tracing 4 (fn () => name ^ ": running");
    val ok = run ();
    val _ = Multithreading.tracing 4 (fn () => name ^ ": finished");
    val _ = set_task NONE;
    val _ = set_group NONE;
    val _ = SYNCHRONIZED (fn () => (change queue (TaskQueue.finished task); notify_all ()));
    val _ = (case (ok, group) of (false, SOME g) => Mailbox.send (CancelGroup g) requests | _ => ());
  in () end;


(* worker threads *)

val excessive = ref 0;
val active = ref 0;

fun change_active b = (*requires SYNCHRONIZED*)
 (change active (fn n => if b then n + 1 else n - 1);
  Multithreading.tracing 1 (fn () => "SCHEDULE: " ^ string_of_int (! active) ^ " active"));

fun worker_next name = (*requires SYNCHRONIZED*)
  if ! excessive > 0 then
    (dec excessive;
     change_active false;
     change workers (remove Thread.equal (Thread.self ()));
     NONE)
  else
    (case change_result queue (TaskQueue.dequeue (Thread.self ())) of
      NONE => (change_active false; wait name; change_active true; worker_next name)
    | some => some);

fun worker_loop name =
  (case SYNCHRONIZED (fn () => worker_next name) of
    NONE => ()
  | SOME work => (execute name work; worker_loop name));

fun worker_start name = (*requires SYNCHRONIZED*)
 (change_active true;
  change workers (cons (Thread.fork (fn () => worker_loop name, Multithreading.no_interrupts))));


(* scheduler *)

fun scheduler_fork () = SYNCHRONIZED (fn () =>
  let
    val m = Multithreading.max_threads_value ();
    val l = length (! workers);
    val _ = excessive := l - m;
  in List.app (fn i => worker_start ("worker " ^ string_of_int i)) (l upto m - 1) end);

fun scheduler_loop () =
  (scheduler_fork ();
    (case Mailbox.receive_timeout (Time.fromMilliseconds 300) requests of
      SOME Shutdown => ()   (* FIXME *)
    | SOME (CancelGroup group) => (interrupt_group group; scheduler_loop ())  (* FIXME *)
    | NONE => scheduler_loop ()));

fun check_scheduler () = SYNCHRONIZED (fn () =>
  if (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread) then ()
  else scheduler := SOME (Thread.fork (scheduler_loop, Multithreading.no_interrupts)));


(* future values *)

fun future group deps (e: unit -> 'a) =
  let
    val _ = check_scheduler ();
    val result = ref (NONE: 'a Exn.result option);
    val run = Multithreading.with_attributes (Thread.getAttributes ()) (fn _ => fn () =>
      let val res = Exn.capture e () in result := SOME res; is_some (Exn.get_result res) end);
    val task = SYNCHRONIZED (fn () =>
      change_result queue (TaskQueue.enqueue group deps run) before notify_all ());
  in Future {task = task, group = group, result = result} end;

fun fork e = future (get_group ()) [] e;

fun join (Future {result, ...}) =
  let
    val _ = check_scheduler ();
    fun loop () =
      (case ! result of
        NONE => (wait "join"; loop ())
      | SOME res => res);
  in Exn.release (SYNCHRONIZED loop) end;

end;
