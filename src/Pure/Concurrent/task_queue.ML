(*  Title:      Pure/Concurrent/task_queue.ML
    ID:         $Id$
    Author:     Makarius

Ordered queue of grouped tasks.
*)

signature TASK_QUEUE =
sig
  eqtype task
  eqtype group
  val new_group: unit -> group
  type queue
  val empty: queue
  val enqueue: group -> task list -> (bool -> bool) -> queue -> task * queue
  val dequeue: Thread.thread -> queue -> (task * group * (unit -> bool)) option * queue
  val cancel: group -> queue -> Thread.thread list * queue
  val finish: task -> queue -> queue
end;

structure TaskQueue: TASK_QUEUE =
struct

(* identifiers *)

datatype task = Task of serial;

datatype group = Group of serial;
fun new_group () = Group (serial ());


(* jobs *)

datatype job =
  Job of bool * (bool -> bool) |
  Running of Thread.thread;

type jobs = (group * job) IntGraph.T;

fun get_group (jobs: jobs) (Task id) = #1 (IntGraph.get_node jobs id);
fun get_job (jobs: jobs) (Task id) = #2 (IntGraph.get_node jobs id);
fun map_job (Task id) f (jobs: jobs) = IntGraph.map_node id (apsnd f) jobs;


(* queue of grouped jobs *)

datatype queue = Queue of
 {groups: task list Inttab.table,                         (*groups with presently active members*)
  jobs: jobs,                                             (*job dependency graph*)
  cache: (task * group * (unit -> bool)) Queue.T option}; (*cache of ready tasks*)

fun make_queue groups jobs cache =
  Queue {groups = groups, jobs = jobs, cache = cache};

val empty = make_queue Inttab.empty IntGraph.empty NONE;


(* queue operations *)

fun enqueue (group as Group gid) deps job (Queue {groups, jobs, ...}) =
  let
    val id = serial ();
    val task = Task id;
    val groups' = Inttab.cons_list (gid, task) groups;

    fun add_dep (Task dep) G = IntGraph.add_edge_acyclic (dep, id) G
      handle IntGraph.UNDEF _ => G;
    val jobs' = jobs |> IntGraph.new_node (id, (group, Job (true, job))) |> fold add_dep deps;
  in (task, make_queue groups' jobs' NONE) end;

fun dequeue thread (queue as Queue {groups, jobs, cache}) =
  let
    fun add_ready (id, ((group, Job (ok, job)), ([], _))) =
          Queue.enqueue (Task id, group, (fn () => job ok))
      | add_ready _ = I;
    val ready =
      (case cache of
        SOME ready => ready
      | NONE => IntGraph.fold add_ready jobs Queue.empty);
  in
    (case try Queue.dequeue ready of
      NONE => (NONE, make_queue groups jobs (SOME ready))
    | SOME (result, ready') =>
        let val jobs' = map_job (#1 result) (K (Running thread)) jobs
        in (SOME result, make_queue groups jobs' (SOME ready')) end)
  end;


(* termination *)

fun cancel (group as Group gid) (Queue {groups, jobs, ...}) =
  let
    val tasks = Inttab.lookup_list groups gid;
    val running = fold (get_job jobs #> (fn Running thread => cons thread | _ => I)) tasks [];
    val jobs' = fold (fn task =>
        (case get_job jobs task of
          Job (true, job) => map_job task (K (Job (false, job)))
        | _ => I)) tasks jobs;
  in (running, make_queue groups jobs' NONE) end;

fun finish (task as Task id) (Queue {groups, jobs, ...}) =
  let
    val Group gid = get_group jobs task;
    val groups' = Inttab.remove_list (op =) (gid, task) groups;
    val jobs' = IntGraph.del_nodes [id] jobs;
  in make_queue groups' jobs' NONE end;

end;
