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
  val focus: task list -> queue -> queue
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

fun get_group (jobs: jobs) (Task id) = #1 (IntGraph.get_node jobs id);
fun get_job (jobs: jobs) (Task id) = #2 (IntGraph.get_node jobs id);
fun map_job (Task id) f (jobs: jobs) = IntGraph.map_node id (apsnd f) jobs;

fun add_job (Task id) (Task dep) (jobs: jobs) =
  IntGraph.add_edge_acyclic (dep, id) jobs handle IntGraph.UNDEF _ => jobs;

fun check_job (jobs: jobs) (task as Task id) =
  if can (IntGraph.get_node jobs) id then SOME task else NONE;


(* queue of grouped jobs *)

datatype queue = Queue of
 {groups: task list Inttab.table,   (*groups with presently active members*)
  jobs: jobs,                       (*job dependency graph*)
  focus: task list};                (*particular collection of high-priority tasks*)

fun make_queue groups jobs focus = Queue {groups = groups, jobs = jobs, focus = focus};
val empty = make_queue Inttab.empty IntGraph.empty [];


(* enqueue *)

fun enqueue (group as Group (gid, _)) deps job (Queue {groups, jobs, focus}) =
  let
    val id = serial ();
    val task = Task id;
    val groups' = Inttab.cons_list (gid, task) groups;
    val jobs' = jobs
      |> IntGraph.new_node (id, (group, Job job)) |> fold (add_job task) deps;
  in (task, make_queue groups' jobs' focus) end;

fun depend deps task (Queue {groups, jobs, focus}) =
  make_queue groups (fold (add_job task) deps jobs) focus;

fun focus tasks (Queue {groups, jobs, ...}) =
  make_queue groups jobs (map_filter (check_job jobs) tasks);


(* dequeue *)

local

fun dequeue_result NONE queue = (NONE, queue)
  | dequeue_result (SOME (result as (task, _, _))) (Queue {groups, jobs, focus}) =
      (SOME result, make_queue groups (map_job task (K (Running (Thread.self ()))) jobs) focus);

fun dequeue_global (queue as Queue {jobs, ...}) =
  let
    fun ready (id, ((group as Group (_, ref ok), Job job), ([], _))) =
          SOME (Task id, group, (fn () => job ok))
      | ready _ = NONE;
  in dequeue_result (IntGraph.get_first ready jobs) queue end;

fun dequeue_local focus (queue as Queue {jobs, ...}) =
  let
    fun ready id =
      (case IntGraph.get_node jobs id of
        (group as Group (_, ref ok), Job job) =>
          if null (IntGraph.imm_preds jobs id) then SOME (Task id, group, (fn () => job ok))
          else NONE
      | _ => NONE);
    val ids = map (fn Task id => id) focus;
  in dequeue_result (get_first ready (IntGraph.all_preds jobs ids)) queue end;

in

fun dequeue (queue as Queue {focus, ...}) =
  (case dequeue_local focus queue of (NONE, _) => dequeue_global queue | res => res);

fun dequeue_towards tasks (queue as Queue {jobs, ...}) =
  dequeue_local (map_filter (check_job jobs) tasks) queue;

end;


(* sporadic interrupts *)

fun interrupt_thread thread = Thread.interrupt thread handle Thread _ => ();

fun interrupt (Queue {jobs, ...}) task =
  (case try (get_job jobs) task of SOME (Running thread) => interrupt_thread thread | _ => ());

fun interrupt_external queue str =
  (case Int.fromString str of SOME id => interrupt queue (Task id) | NONE => ());


(* misc operations *)

fun cancel (Queue {groups, jobs, ...}) (Group (gid, ok)) =
  let
    val _ = ok := false;  (*invalidate any future group members*)
    val tasks = Inttab.lookup_list groups gid;
    val running = fold (get_job jobs #> (fn Running thread => cons thread | _ => I)) tasks [];
    val _ = List.app interrupt_thread running;
  in null running end;

fun finish (task as Task id) (Queue {groups, jobs, focus}) =
  let
    val Group (gid, _) = get_group jobs task;
    val groups' = Inttab.remove_list (op =) (gid, task) groups;
    val jobs' = IntGraph.del_nodes [id] jobs;
    val focus' = remove (op =) task focus;
  in make_queue groups' jobs' focus' end;

end;
