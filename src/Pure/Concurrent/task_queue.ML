(*  Title:      Pure/Concurrent/task_queue.ML
    ID:         $Id$
    Author:     Makarius

Ordered queue of grouped tasks.
*)

signature TASK_QUEUE =
sig
  eqtype task
  val str_of_task: task -> string
  eqtype group
  val new_group: unit -> group
  val str_of_group: group -> string
  type queue
  val empty: queue
  val enqueue: group -> task list -> (bool -> bool) -> queue -> task * queue
  val depend: task list -> task -> queue -> queue
  val dequeue: queue -> (task * group * (unit -> bool)) option * queue
  val dequeue_towards: task list -> queue -> (task * group * (unit -> bool)) option * queue
  val interrupt: queue -> task -> unit
  val interrupt_external: queue -> string -> unit
  val finish: task -> queue -> queue
  val cancel: queue -> group -> bool
end;

structure TaskQueue: TASK_QUEUE =
struct

(* identifiers *)

datatype task = Task of serial;
fun str_of_task (Task i) = string_of_int i;

datatype group = Group of serial * bool ref;
fun new_group () = Group (serial (), ref true);

fun str_of_group (Group (i, ref ok)) =
  if ok then string_of_int i else enclose "(" ")" (string_of_int i);


(* jobs *)

datatype job =
  Job of bool -> bool |
  Running of Thread.thread;

type jobs = (group * job) IntGraph.T;

fun defined_job (jobs: jobs) (Task id) = can (IntGraph.get_node jobs) id;
fun get_group (jobs: jobs) (Task id) = #1 (IntGraph.get_node jobs id);
fun get_job (jobs: jobs) (Task id) = #2 (IntGraph.get_node jobs id);
fun map_job (Task id) f (jobs: jobs) = IntGraph.map_node id (apsnd f) jobs;
fun add_job (Task id) (Task dep) (jobs: jobs) =
  IntGraph.add_edge_acyclic (dep, id) jobs handle IntGraph.UNDEF _ => jobs;


(* queue of grouped jobs *)

datatype queue = Queue of
 {groups: task list Inttab.table,   (*groups with presently active members*)
  jobs: jobs};                      (*job dependency graph*)

fun make_queue groups jobs = Queue {groups = groups, jobs = jobs};
val empty = make_queue Inttab.empty IntGraph.empty;


(* enqueue *)

fun enqueue (group as Group (gid, _)) deps job (Queue {groups, jobs}) =
  let
    val id = serial ();
    val task = Task id;
    val groups' = Inttab.cons_list (gid, task) groups;
    val jobs' = jobs
      |> IntGraph.new_node (id, (group, Job job)) |> fold (add_job task) deps;
  in (task, make_queue groups' jobs') end;

fun depend deps task (Queue {groups, jobs}) =
  make_queue groups (fold (add_job task) deps jobs);


(* dequeue *)

fun dequeue_if P (queue as Queue {groups, jobs}) =
  let
    fun ready (id, ((group as Group (_, ref ok), Job job), ([], _))) =
          if P id then SOME (Task id, group, (fn () => job ok)) else NONE
      | ready _ = NONE;
  in
    (case IntGraph.get_first ready jobs of
      NONE => (NONE, queue)
    | SOME result =>
        let val jobs' = map_job (#1 result) (K (Running (Thread.self ()))) jobs
        in (SOME result, make_queue groups jobs') end)
  end;

val dequeue = dequeue_if (K true);

fun dequeue_towards tasks (queue as Queue {jobs, ...}) =
  let val ids = tasks
    |> map_filter (fn task as Task id => if defined_job jobs task then SOME id else NONE)
  in dequeue_if (member (op =) (IntGraph.all_preds jobs ids)) queue end;


(* sporadic interrupts *)

fun interrupt_thread thread = Thread.interrupt thread handle Thread _ => ();

fun interrupt (Queue {jobs, ...}) task =
  (case try (get_job jobs) task of SOME (Running thread) => interrupt_thread thread | _ => ());

fun interrupt_external queue str =
  (case Int.fromString str of SOME id => interrupt queue (Task id) | NONE => ());


(* termination *)

fun cancel (Queue {groups, jobs}) (Group (gid, ok)) =
  let
    val _ = ok := false;  (*invalidate any future group members*)
    val tasks = Inttab.lookup_list groups gid;
    val running = fold (get_job jobs #> (fn Running thread => cons thread | _ => I)) tasks [];
    val _ = List.app interrupt_thread running;
  in null running end;

fun finish (task as Task id) (Queue {groups, jobs}) =
  let
    val Group (gid, _) = get_group jobs task;
    val groups' = Inttab.remove_list (op =) (gid, task) groups;
    val jobs' = IntGraph.del_nodes [id] jobs;
  in make_queue groups' jobs' end;

end;
