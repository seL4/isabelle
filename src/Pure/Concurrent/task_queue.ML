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
  val enqueue: group option -> task list -> (unit -> bool) -> queue -> task * queue
  val dequeue: Thread.thread -> queue -> (task * group option * (unit -> bool)) option * queue
  val finished: task -> queue -> queue
  val interrupt_task: queue -> task -> unit
  val interrupt_group: queue -> group -> unit
  val interrupt_task_group: queue -> task -> unit
end;

structure TaskQueue (* : TASK_QUEUE *) =
struct

(* identifiers *)

datatype task = Task of serial;

datatype group = Group of serial;
fun new_group () = Group (serial ());


(* queue of dependent jobs *)

datatype job =
  Job of unit -> bool |
  Running of Thread.thread;

datatype queue = Queue of
  {jobs: (group option * job) IntGraph.T,                         (*job dependency graph*)
   cache: (task * group option * (unit -> bool)) Queue.T option,  (*cache of ready tasks*)
   groups: task list Inttab.table};                               (*active group members*)

fun make_queue jobs cache groups =
  Queue {jobs = jobs, cache = cache, groups = groups};


(* queue operations *)

val empty = make_queue IntGraph.empty NONE Inttab.empty;

fun enqueue group deps job (Queue {jobs, groups, ...}) =
  let
    val id = serial ();
    val task = Task id;

    fun add_dep (Task dep) G = IntGraph.add_edge_acyclic (dep, id) G
      handle IntGraph.UNDEF _ => G;
    val jobs' = jobs |> IntGraph.new_node (id, (group, Job job)) |> fold add_dep deps;

    val groups' =
      (case group of
        NONE => groups
      | SOME (Group gid) => Inttab.cons_list (gid, task) groups);
  in (task, make_queue jobs' NONE groups') end;

fun dequeue thread (queue as Queue {jobs, cache, groups}) =
  let
    val ready =
      (case cache of
        SOME ready => ready
      | NONE =>
          let
            fun add (id, ((group, Job job), ([], _))) = Queue.enqueue (Task id, group, job)
              | add _ = I;
          in IntGraph.fold add jobs Queue.empty end);
  in
    if Queue.is_empty ready then (NONE, make_queue jobs (SOME ready) groups)
    else
      let
        val (result as (Task id, _, _), ready') = Queue.dequeue ready;
        val jobs' = IntGraph.map_node id (fn (group, _) => (group, Running thread)) jobs;
      in (SOME result, make_queue jobs' (SOME ready') groups) end
  end;

fun finished (task as Task id) (Queue {jobs, groups, ...}) =
  let
    val groups' =
      (case #1 (IntGraph.get_node jobs id) of
        NONE => groups
      | SOME (Group gid) => Inttab.remove_list (op =) (gid, task) groups);
    val jobs' = IntGraph.del_nodes [id] jobs;
  in make_queue jobs' NONE groups' end;


(* interrupt *)

fun interrupt_task (Queue {jobs, ...}) (Task id) =
  (case IntGraph.get_node jobs id of
    (_, Running thread) => (Thread.interrupt thread handle Thread _ => ())
  | _ => ())
  handle IntGraph.UNDEF _ => ();

fun interrupt_group (queue as Queue {groups, ...}) (Group gid) =
  List.app (interrupt_task queue) (Inttab.lookup_list groups gid);

fun interrupt_task_group (queue as Queue {jobs, ...}) (task as Task id) =
  (case IntGraph.get_node jobs id of
    (NONE, _) => interrupt_task queue task
  | (SOME group, _) => interrupt_group queue group);

end;
