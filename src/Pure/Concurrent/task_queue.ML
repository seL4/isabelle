(*  Title:      Pure/Concurrent/task_queue.ML
    ID:         $Id$
    Author:     Makarius

Ordered queue of grouped tasks.
*)

signature TASK_QUEUE =
sig
  eqtype task
  val get_thread_data: unit -> task option
  val set_thread_data: task option -> unit
  eqtype group
  val new_group: unit -> group
  type queue
  val empty: queue
  val dequeue: Thread.thread -> queue -> (task * (unit -> unit)) option * queue
  val enqueue: group option -> task list -> (unit -> unit) -> queue -> task * queue
  val finished: task -> queue -> queue
  val interrupt: queue -> task -> unit
  val interrupt_group: queue -> group -> unit
end;

structure TaskQueue: TASK_QUEUE =
struct

(* identified tasks *)

datatype task = Task of serial;

local val tag = Universal.tag () : task option Universal.tag in
  fun get_thread_data () = the_default NONE (Thread.getLocal tag);
  fun set_thread_data x = Thread.setLocal (tag, x);
end;

datatype group = Group of serial;
fun new_group () = Group (serial ());


(* queue of dependent jobs *)

datatype job =
  Job of unit -> unit |
  Running of Thread.thread;

datatype queue = Queue of
  {jobs: (job * group option) IntGraph.T,             (*job dependency graph*)
   cache: (task * (unit -> unit)) Queue.T option,     (*cache of ready tasks*)
   groups: task list Inttab.table};                   (*active group members*)

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
    val jobs' = jobs |> IntGraph.new_node (id, (Job job, group)) |> fold add_dep deps;

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
          let val add = fn (id, ((Job job, _), ([], _))) => Queue.enqueue (Task id, job) | _ => I
          in IntGraph.fold add jobs Queue.empty end);
  in
    if Queue.is_empty ready then (NONE, make_queue jobs (SOME ready) groups)
    else
      let
        val (task as (Task id, _), ready') = Queue.dequeue ready;
        val jobs' = IntGraph.map_node id (fn (_, group) => (Running thread, group)) jobs;
      in (SOME task, make_queue jobs' (SOME ready') groups) end
  end;

fun finished (task as Task id) (Queue {jobs, groups, ...}) =
  let
    val groups' =
      (case #2 (IntGraph.get_node jobs id) of
        NONE => groups
      | SOME (Group gid) => Inttab.remove_list (op =) (gid, task) groups);
    val jobs' = IntGraph.del_nodes [id] jobs;
  in make_queue jobs' NONE groups' end;


(* interrupts *)

fun interrupt (Queue {jobs, ...}) (Task id) =
  (case IntGraph.get_node jobs id of
    (Running thread, _) => (Thread.interrupt thread handle Thread _ => ())
  | _ => ())
  handle IntGraph.UNDEF _ => ();

fun interrupt_group (queue as Queue {groups, ...}) (Group gid) =
  List.app (interrupt queue) (Inttab.lookup_list groups gid);

end;
