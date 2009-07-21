(*  Title:      Pure/Concurrent/task_queue.ML
    Author:     Makarius

Ordered queue of grouped tasks.
*)

signature TASK_QUEUE =
sig
  type task
  val new_task: int -> task
  val pri_of_task: task -> int
  val str_of_task: task -> string
  type group
  val group_id: group -> int
  val eq_group: group * group -> bool
  val new_group: unit -> group
  val is_valid: group -> bool
  val invalidate_group: group -> unit
  val str_of_group: group -> string
  type queue
  val empty: queue
  val is_empty: queue -> bool
  val status: queue -> {ready: int, pending: int, running: int}
  val enqueue: group -> task list -> int -> (bool -> bool) -> queue -> task * queue
  val extend: task -> (bool -> bool) -> queue -> queue option
  val dequeue: queue -> (task * group * (bool -> bool) list) option * queue
  val dequeue_towards: task list -> queue ->
    (((task * group * (bool -> bool) list) * task list) option * queue)
  val interrupt: queue -> task -> unit
  val interrupt_external: queue -> string -> unit
  val cancel: queue -> group -> bool
  val cancel_all: queue -> group list
  val finish: task -> queue -> queue
end;

structure Task_Queue:> TASK_QUEUE =
struct

(* tasks *)

datatype task = Task of int * serial;
fun new_task pri = Task (pri, serial ());

fun pri_of_task (Task (pri, _)) = pri;
fun str_of_task (Task (_, i)) = string_of_int i;

fun task_ord (Task t1, Task t2) = prod_ord (rev_order o int_ord) int_ord (t1, t2);
structure Task_Graph = Graph(type key = task val ord = task_ord);


(* groups *)

datatype group = Group of serial * bool ref;

fun group_id (Group (gid, _)) = gid;
fun eq_group (Group (gid1, _), Group (gid2, _)) = gid1 = gid2;

fun new_group () = Group (serial (), ref true);

fun is_valid (Group (_, ref ok)) = ok;
fun invalidate_group (Group (_, ok)) = ok := false;

fun str_of_group (Group (i, ref ok)) =
  if ok then string_of_int i else enclose "(" ")" (string_of_int i);


(* jobs *)

datatype job =
  Job of (bool -> bool) list |
  Running of Thread.thread;

type jobs = (group * job) Task_Graph.T;

fun get_group (jobs: jobs) task = #1 (Task_Graph.get_node jobs task);
fun get_job (jobs: jobs) task = #2 (Task_Graph.get_node jobs task);
fun set_job task job (jobs: jobs) = Task_Graph.map_node task (fn (group, _) => (group, job)) jobs;

fun add_job task dep (jobs: jobs) =
  Task_Graph.add_edge (dep, task) jobs handle Task_Graph.UNDEF _ => jobs;


(* queue of grouped jobs *)

datatype result = Unknown | Result of task | No_Result;

datatype queue = Queue of
 {groups: task list Inttab.table,   (*groups with presently active members*)
  jobs: jobs,                       (*job dependency graph*)
  cache: result};                   (*last dequeue result*)

fun make_queue groups jobs cache = Queue {groups = groups, jobs = jobs, cache = cache};

val empty = make_queue Inttab.empty Task_Graph.empty No_Result;
fun is_empty (Queue {jobs, ...}) = Task_Graph.is_empty jobs;


(* status *)

fun status (Queue {jobs, ...}) =
  let
    val (x, y, z) =
      Task_Graph.fold (fn (task, ((_, job), (deps, _))) => fn (x, y, z) =>
          (case job of
            Job _ => if null deps then (x + 1, y, z) else (x, y + 1, z)
          | Running _ => (x, y, z + 1)))
        jobs (0, 0, 0);
  in {ready = x, pending = y, running = z} end;


(* enqueue *)

fun enqueue (group as Group (gid, _)) deps pri job (Queue {groups, jobs, cache}) =
  let
    val task = new_task pri;
    val groups' = Inttab.cons_list (gid, task) groups;
    val jobs' = jobs
      |> Task_Graph.new_node (task, (group, Job [job])) |> fold (add_job task) deps;
    val cache' =
      (case cache of
        Result last =>
          if task_ord (last, task) = LESS
          then cache else Unknown
      | _ => Unknown);
  in (task, make_queue groups' jobs' cache') end;

fun extend task job (Queue {groups, jobs, cache}) =
  (case try (get_job jobs) task of
    SOME (Job list) => SOME (make_queue groups (set_job task (Job (job :: list)) jobs) cache)
  | _ => NONE);


(* dequeue *)

fun dequeue (queue as Queue {groups, jobs, cache}) =
  let
    fun ready (task, ((group, Job list), ([], _))) = SOME (task, group, rev list)
      | ready _ = NONE;
    fun deq boundary =
      (case Task_Graph.get_first boundary ready jobs of
        NONE => (NONE, make_queue groups jobs No_Result)
      | SOME (result as (task, _, _)) =>
          let
            val jobs' = set_job task (Running (Thread.self ())) jobs;
            val cache' = Result task;
          in (SOME result, make_queue groups jobs' cache') end);
  in
    (case cache of
      Unknown => deq NONE
    | Result last => deq (SOME last)
    | No_Result => (NONE, queue))
  end;


(* dequeue_towards -- adhoc dependencies *)

fun dequeue_towards deps (queue as Queue {groups, jobs, ...}) =
  let
    fun ready task =
      (case Task_Graph.get_node jobs task of
        (group, Job list) =>
          if null (Task_Graph.imm_preds jobs task) then SOME (task, group, rev list)
          else NONE
      | _ => NONE);

    val tasks = filter (can (Task_Graph.get_node jobs)) deps;
    fun result (res as (task, _, _)) =
      let
        val jobs' = set_job task (Running (Thread.self ())) jobs;
        val cache' = Unknown;
      in (SOME (res, tasks), make_queue groups jobs' cache') end;
  in
    (case get_first ready tasks of
      SOME res => result res
    | NONE =>
        (case get_first ready (Task_Graph.all_preds jobs tasks) of
          SOME res => result res
        | NONE => (NONE, queue)))
  end;


(* sporadic interrupts *)

fun interrupt (Queue {jobs, ...}) task =
  (case try (get_job jobs) task of SOME (Running thread) => SimpleThread.interrupt thread | _ => ());

fun interrupt_external (queue as Queue {jobs, ...}) str =
  (case Int.fromString str of
    SOME i =>
      (case Task_Graph.get_first NONE
          (fn (task as Task (_, j), _) => if i = j then SOME task else NONE) jobs
        of SOME task => interrupt queue task | NONE => ())
  | NONE => ());


(* termination *)

fun cancel (Queue {groups, jobs, ...}) (group as Group (gid, _)) =
  let
    val _ = invalidate_group group;
    val tasks = Inttab.lookup_list groups gid;
    val running = fold (get_job jobs #> (fn Running t => insert Thread.equal t | _ => I)) tasks [];
    val _ = List.app SimpleThread.interrupt running;
  in null running end;

fun cancel_all (Queue {jobs, ...}) =
  let
    fun cancel_job (group, job) (groups, running) =
      (invalidate_group group;
        (case job of Running t => (insert eq_group group groups, insert Thread.equal t running)
        | _ => (groups, running)));
    val (groups, running) = Task_Graph.fold (cancel_job o #1 o #2) jobs ([], []);
    val _ = List.app SimpleThread.interrupt running;
  in groups end;

fun finish task (Queue {groups, jobs, cache}) =
  let
    val Group (gid, _) = get_group jobs task;
    val groups' = Inttab.remove_list (op =) (gid, task) groups;
    val jobs' = Task_Graph.del_node task jobs;
    val cache' =
      if null (Task_Graph.imm_succs jobs task) then cache
      else Unknown;
  in make_queue groups' jobs' cache' end;

end;
