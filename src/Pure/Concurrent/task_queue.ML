(*  Title:      Pure/Concurrent/task_queue.ML
    Author:     Makarius

Ordered queue of grouped tasks.
*)

signature TASK_QUEUE =
sig
  type task
  val dummy_task: task
  val pri_of_task: task -> int
  val str_of_task: task -> string
  type group
  val new_group: group option -> group
  val group_id: group -> int
  val eq_group: group * group -> bool
  val cancel_group: group -> exn -> unit
  val is_canceled: group -> bool
  val group_status: group -> exn list
  val str_of_group: group -> string
  type queue
  val empty: queue
  val all_passive: queue -> bool
  val status: queue -> {ready: int, pending: int, running: int, passive: int}
  val cancel: group -> queue -> bool * queue
  val cancel_all: queue -> group list * queue
  val enqueue_passive: group -> queue -> task * queue
  val enqueue: group -> task list -> int -> (bool -> bool) -> queue -> (task * bool) * queue
  val extend: task -> (bool -> bool) -> queue -> queue option
  val dequeue: Thread.thread -> queue -> (task * group * (bool -> bool) list) option * queue
  val depend: task -> task list -> queue -> queue
  val dequeue_towards: Thread.thread -> task list -> queue ->
    (((task * group * (bool -> bool) list) option * task list) * queue)
  val finish: task -> queue -> bool * queue
end;

structure Task_Queue:> TASK_QUEUE =
struct

(* tasks *)

datatype task = Task of int option * serial;
val dummy_task = Task (NONE, ~1);
fun new_task pri = Task (pri, serial ());

fun pri_of_task (Task (pri, _)) = the_default 0 pri;
fun str_of_task (Task (_, i)) = string_of_int i;

fun task_ord (Task t1, Task t2) = prod_ord (rev_order o option_ord int_ord) int_ord (t1, t2);
structure Task_Graph = Graph(type key = task val ord = task_ord);


(* nested groups *)

datatype group = Group of
 {parent: group option,
  id: serial,
  status: exn list Synchronized.var};

fun make_group (parent, id, status) = Group {parent = parent, id = id, status = status};

fun new_group parent = make_group (parent, serial (), Synchronized.var "group" []);

fun group_id (Group {id, ...}) = id;
fun eq_group (group1, group2) = group_id group1 = group_id group2;

fun group_ancestry (Group {parent, id, ...}) =
  id :: (case parent of NONE => [] | SOME group => group_ancestry group);


(* group status *)

fun cancel_group (Group {status, ...}) exn =
  Synchronized.change status
    (fn exns =>
      (case exn of
        Exn.Interrupt => if null exns then [exn] else exns
      | _ => exn :: exns));

fun is_canceled (Group {parent, status, ...}) =
  not (null (Synchronized.value status)) orelse
    (case parent of NONE => false | SOME group => is_canceled group);

fun is_ready deps group = null deps orelse is_canceled group;

fun group_status (Group {parent, status, ...}) =
  Synchronized.value status @
    (case parent of NONE => [] | SOME group => group_status group);

fun str_of_group group =
  (is_canceled group ? enclose "(" ")") (string_of_int (group_id group));


(* jobs *)

datatype job =
  Job of (bool -> bool) list |
  Running of Thread.thread |
  Passive;

type jobs = (group * job) Task_Graph.T;

fun get_group (jobs: jobs) task = #1 (Task_Graph.get_node jobs task);
fun get_job (jobs: jobs) task = #2 (Task_Graph.get_node jobs task);
fun set_job task job (jobs: jobs) = Task_Graph.map_node task (fn (group, _) => (group, job)) jobs;

fun add_job task dep (jobs: jobs) =
  Task_Graph.add_edge (dep, task) jobs handle Task_Graph.UNDEF _ => jobs;

fun add_dep task dep (jobs: jobs) =
  if Task_Graph.is_edge jobs (task, dep) then
    raise Fail "Cyclic dependency of future tasks"
  else add_job task dep jobs;

fun get_deps (jobs: jobs) task =
  Task_Graph.imm_preds jobs task handle Task_Graph.UNDEF _ => [];


(* queue of grouped jobs *)

datatype result = Unknown | Result of task | No_Result;

datatype queue = Queue of
 {groups: task list Inttab.table,   (*groups with presently active members*)
  jobs: jobs,                       (*job dependency graph*)
  cache: result};                   (*last dequeue result*)

fun make_queue groups jobs cache = Queue {groups = groups, jobs = jobs, cache = cache};

val empty = make_queue Inttab.empty Task_Graph.empty No_Result;

fun all_passive (Queue {jobs, ...}) =
  Task_Graph.get_first NONE
    ((fn Job _ => SOME () | Running _ => SOME () | Passive => NONE) o #2 o #1 o #2) jobs |> is_none;


(* queue status *)

fun status (Queue {jobs, ...}) =
  let
    val (x, y, z, w) =
      Task_Graph.fold (fn (_, ((group, job), (deps, _))) => fn (x, y, z, w) =>
          (case job of
            Job _ => if is_ready deps group then (x + 1, y, z, w) else (x, y + 1, z, w)
          | Running _ => (x, y, z + 1, w)
          | Passive => (x, y, z, w + 1)))
        jobs (0, 0, 0, 0);
  in {ready = x, pending = y, running = z, passive = w} end;


(* cancel -- peers and sub-groups *)

fun cancel group (Queue {groups, jobs, ...}) =
  let
    val _ = cancel_group group Exn.Interrupt;
    val tasks = Inttab.lookup_list groups (group_id group);
    val running =
      fold (get_job jobs #> (fn Running t => insert Thread.equal t | _ => I)) tasks [];
    val _ = List.app SimpleThread.interrupt running;
  in (null running, make_queue groups jobs Unknown) end;

fun cancel_all (Queue {groups, jobs, ...}) =
  let
    fun cancel_job (group, job) (groups, running) =
      (cancel_group group Exn.Interrupt;
        (case job of
          Running t => (insert eq_group group groups, insert Thread.equal t running)
        | _ => (groups, running)));
    val (running_groups, running) = Task_Graph.fold (cancel_job o #1 o #2) jobs ([], []);
    val _ = List.app SimpleThread.interrupt running;
  in (running_groups, make_queue groups jobs Unknown) end;


(* enqueue *)

fun enqueue_passive group (Queue {groups, jobs, cache}) =
  let
    val task = new_task NONE;
    val groups' = groups
      |> fold (fn gid => Inttab.cons_list (gid, task)) (group_ancestry group);
    val jobs' = jobs |> Task_Graph.new_node (task, (group, Passive));
  in (task, make_queue groups' jobs' cache) end;

fun enqueue group deps pri job (Queue {groups, jobs, cache}) =
  let
    val task = new_task (SOME pri);
    val groups' = groups
      |> fold (fn gid => Inttab.cons_list (gid, task)) (group_ancestry group);
    val jobs' = jobs
      |> Task_Graph.new_node (task, (group, Job [job]))
      |> fold (add_job task) deps
      |> fold (fold (add_job task) o get_deps jobs) deps;
    val minimal = null (get_deps jobs' task);
    val cache' =
      (case cache of
        Result last =>
          if task_ord (last, task) = LESS
          then cache else Unknown
      | _ => Unknown);
  in ((task, minimal), make_queue groups' jobs' cache') end;

fun extend task job (Queue {groups, jobs, cache}) =
  (case try (get_job jobs) task of
    SOME (Job list) => SOME (make_queue groups (set_job task (Job (job :: list)) jobs) cache)
  | _ => NONE);


(* dequeue *)

fun dequeue thread (queue as Queue {groups, jobs, cache}) =
  let
    fun ready (task, ((group, Job list), (deps, _))) =
          if is_ready deps group then SOME (task, group, rev list) else NONE
      | ready _ = NONE;
    fun deq boundary =
      (case Task_Graph.get_first boundary ready jobs of
        NONE => (NONE, make_queue groups jobs No_Result)
      | SOME (result as (task, _, _)) =>
          let
            val jobs' = set_job task (Running thread) jobs;
            val cache' = Result task;
          in (SOME result, make_queue groups jobs' cache') end);
  in
    (case cache of
      Unknown => deq NONE
    | Result last => deq (SOME last)
    | No_Result => (NONE, queue))
  end;


(* dequeue_towards -- adhoc dependencies *)

fun depend task deps (Queue {groups, jobs, ...}) =
  make_queue groups (fold (add_dep task) deps jobs) Unknown;

fun dequeue_towards thread deps (queue as Queue {groups, jobs, ...}) =
  let
    fun ready task =
      (case Task_Graph.get_node jobs task of
        (group, Job list) =>
          if is_ready (get_deps jobs task) group
          then SOME (task, group, rev list)
          else NONE
      | _ => NONE);
    val tasks = filter (can (Task_Graph.get_node jobs)) deps;
    fun result (res as (task, _, _)) =
      let
        val jobs' = set_job task (Running thread) jobs;
        val cache' = Unknown;
      in ((SOME res, tasks), make_queue groups jobs' cache') end;
  in
    (case get_first ready tasks of
      SOME res => result res
    | NONE =>
        (case get_first (get_first ready o get_deps jobs) tasks of
          SOME res => result res
        | NONE => ((NONE, tasks), queue)))
  end;


(* finish *)

fun finish task (Queue {groups, jobs, cache}) =
  let
    val group = get_group jobs task;
    val groups' = groups
      |> fold (fn gid => Inttab.remove_list (op =) (gid, task)) (group_ancestry group);
    val jobs' = Task_Graph.del_node task jobs;
    val maximal = null (Task_Graph.imm_succs jobs task);
    val cache' = if maximal then cache else Unknown;
  in (maximal, make_queue groups' jobs' cache') end;

end;
