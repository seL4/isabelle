(*  Title:      Pure/Concurrent/task_queue.ML
    Author:     Makarius

Ordered queue of grouped tasks.
*)

signature TASK_QUEUE =
sig
  type group
  val new_group: group option -> group
  val group_id: group -> int
  val eq_group: group * group -> bool
  val cancel_group: group -> exn -> unit
  val is_canceled: group -> bool
  val group_status: group -> exn list
  val str_of_group: group -> string
  type task
  val dummy_task: unit -> task
  val group_of_task: task -> group
  val name_of_task: task -> string
  val pri_of_task: task -> int
  val str_of_task: task -> string
  val timing_of_task: task -> Time.time * Time.time * string list
  val running: task -> (unit -> 'a) -> 'a
  val joining: task -> (unit -> 'a) -> 'a
  val waiting: task -> task list -> (unit -> 'a) -> 'a
  type queue
  val empty: queue
  val known_task: queue -> task -> bool
  val all_passive: queue -> bool
  val status: queue -> {ready: int, pending: int, running: int, passive: int}
  val cancel: queue -> group -> bool
  val cancel_all: queue -> group list
  val finish: task -> queue -> bool * queue
  val enqueue_passive: group -> (unit -> bool) -> queue -> task * queue
  val enqueue: string -> group -> task list -> int -> (bool -> bool) -> queue -> task * queue
  val extend: task -> (bool -> bool) -> queue -> queue option
  val dequeue_passive: Thread.thread -> task -> queue -> bool * queue
  val dequeue: Thread.thread -> queue -> (task * (bool -> bool) list) option * queue
  val dequeue_deps: Thread.thread -> task list -> queue ->
    (((task * (bool -> bool) list) option * task list) * queue)
end;

structure Task_Queue: TASK_QUEUE =
struct

val new_id = Synchronized.counter ();


(** nested groups of tasks **)

(* groups *)

abstype group = Group of
 {parent: group option,
  id: int,
  status: exn list Synchronized.var}
with

fun make_group (parent, id, status) = Group {parent = parent, id = id, status = status};

fun new_group parent = make_group (parent, new_id (), Synchronized.var "group" []);

fun group_id (Group {id, ...}) = id;
fun eq_group (group1, group2) = group_id group1 = group_id group2;

fun group_ancestry f (Group {parent = NONE, id, ...}) a = f id a
  | group_ancestry f (Group {parent = SOME group, id, ...}) a = group_ancestry f group (f id a);


(* group status *)

fun cancel_group (Group {status, ...}) exn =
  Synchronized.change status
    (fn exns =>
      if not (Exn.is_interrupt exn) orelse null exns then exn :: exns
      else exns);

fun is_canceled (Group {parent, status, ...}) =
  not (null (Synchronized.value status)) orelse
    (case parent of NONE => false | SOME group => is_canceled group);

fun group_status (Group {parent, status, ...}) =
  Synchronized.value status @
    (case parent of NONE => [] | SOME group => group_status group);

fun str_of_group group =
  (is_canceled group ? enclose "(" ")") (string_of_int (group_id group));

end;


(* tasks *)

type timing = Time.time * Time.time * string list;  (*run, wait, wait dependencies*)

fun new_timing () =
  Synchronized.var "timing" ((Time.zeroTime, Time.zeroTime, []): timing);

abstype task = Task of
 {group: group,
  name: string,
  id: int,
  pri: int option,
  timing: timing Synchronized.var}
with

fun dummy_task () =
  Task {group = new_group NONE, name = "", id = 0, pri = NONE, timing = new_timing ()};

fun new_task group name pri =
  Task {group = group, name = name, id = new_id (), pri = pri, timing = new_timing ()};

fun group_of_task (Task {group, ...}) = group;
fun name_of_task (Task {name, ...}) = name;
fun pri_of_task (Task {pri, ...}) = the_default 0 pri;
fun str_of_task (Task {name, id, ...}) =
  if name = "" then string_of_int id else string_of_int id ^ " (" ^ name ^ ")";

fun timing_of_task (Task {timing, ...}) = Synchronized.value timing;

fun update_timing update (Task {timing, ...}) e =
  uninterruptible (fn restore_attributes => fn () =>
    let
      val start = Time.now ();
      val result = Exn.capture (restore_attributes e) ();
      val t = Time.- (Time.now (), start);
      val _ = Synchronized.change timing (update t);
    in Exn.release result end) ();

fun task_ord (Task {id = id1, pri = pri1, ...}, Task {id = id2, pri = pri2, ...}) =
  prod_ord (rev_order o option_ord int_ord) int_ord ((pri1, id1), (pri2, id2));

end;

structure Tasks = Table(type key = task val ord = task_ord);
structure Task_Graph = Graph(type key = task val ord = task_ord);


(* timing *)

fun running task =
  update_timing (fn t => fn (a, b, ds) => (Time.+ (a, t), b, ds)) task;

fun joining task =
  update_timing (fn t => fn (a, b, ds) => (Time.- (a, t), b, ds)) task;

fun waiting task deps =
  update_timing (fn t => fn (a, b, ds) =>
    (Time.- (a, t), Time.+ (b, t),
      if ! Multithreading.trace > 0
      then fold (insert (op =) o name_of_task) deps ds else ds)) task;



(** queue of jobs and groups **)

(* known group members *)

type groups = unit Tasks.table Inttab.table;

fun get_tasks (groups: groups) gid =
  the_default Tasks.empty (Inttab.lookup groups gid);

fun add_task (gid, task) groups =
  Inttab.update (gid, Tasks.update (task, ()) (get_tasks groups gid)) groups;

fun del_task (gid, task) groups =
  let val tasks = Tasks.delete_safe task (get_tasks groups gid) in
    if Tasks.is_empty tasks then Inttab.delete_safe gid groups
    else Inttab.update (gid, tasks) groups
  end;


(* job dependency graph *)

datatype job =
  Job of (bool -> bool) list |
  Running of Thread.thread |
  Passive of unit -> bool;

type jobs = job Task_Graph.T;

fun get_job (jobs: jobs) task = Task_Graph.get_node jobs task;
fun set_job task job (jobs: jobs) = Task_Graph.map_node task (K job) jobs;

fun add_job task dep (jobs: jobs) =
  Task_Graph.add_edge (dep, task) jobs handle Task_Graph.UNDEF _ => jobs;


(* queue *)

datatype queue = Queue of {groups: groups, jobs: jobs};

fun make_queue groups jobs = Queue {groups = groups, jobs = jobs};
val empty = make_queue Inttab.empty Task_Graph.empty;

fun known_task (Queue {jobs, ...}) task = can (Task_Graph.get_entry jobs) task;


(* job status *)

fun ready_job task (Job list, ([], _)) = SOME (task, rev list)
  | ready_job task (Passive abort, ([], _)) =
      if is_canceled (group_of_task task) then SOME (task, [fn _ => abort ()])
      else NONE
  | ready_job _ _ = NONE;

fun active_job (_, (Job _, _)) = SOME ()
  | active_job (_, (Running _, _)) = SOME ()
  | active_job (task, (Passive _, _)) =
      if is_canceled (group_of_task task) then SOME () else NONE;

fun all_passive (Queue {jobs, ...}) = is_none (Task_Graph.get_first active_job jobs);


(* queue status *)

fun status (Queue {jobs, ...}) =
  let
    val (x, y, z, w) =
      Task_Graph.fold (fn (_, (job, (deps, _))) => fn (x, y, z, w) =>
          (case job of
            Job _ => if null deps then (x + 1, y, z, w) else (x, y + 1, z, w)
          | Running _ => (x, y, z + 1, w)
          | Passive _ => (x, y, z, w + 1)))
        jobs (0, 0, 0, 0);
  in {ready = x, pending = y, running = z, passive = w} end;



(** task queue operations **)

(* cancel -- peers and sub-groups *)

fun cancel (Queue {groups, jobs}) group =
  let
    val _ = cancel_group group Exn.Interrupt;
    val running =
      Tasks.fold (#1 #> get_job jobs #> (fn Running t => insert Thread.equal t | _ => I))
        (get_tasks groups (group_id group)) [];
    val _ = List.app Simple_Thread.interrupt running;
  in null running end;

fun cancel_all (Queue {jobs, ...}) =
  let
    fun cancel_job (task, (job, _)) (groups, running) =
      let
        val group = group_of_task task;
        val _ = cancel_group group Exn.Interrupt;
      in
        (case job of
          Running t => (insert eq_group group groups, insert Thread.equal t running)
        | _ => (groups, running))
      end;
    val (running_groups, running) = Task_Graph.fold cancel_job jobs ([], []);
    val _ = List.app Simple_Thread.interrupt running;
  in running_groups end;


(* finish *)

fun finish task (Queue {groups, jobs}) =
  let
    val group = group_of_task task;
    val groups' = group_ancestry (fn gid => del_task (gid, task)) group groups;
    val jobs' = Task_Graph.del_node task jobs;
    val maximal = null (Task_Graph.imm_succs jobs task);
  in (maximal, make_queue groups' jobs') end;


(* enqueue *)

fun enqueue_passive group abort (Queue {groups, jobs}) =
  let
    val task = new_task group "passive" NONE;
    val groups' = group_ancestry (fn gid => add_task (gid, task)) group groups;
    val jobs' = jobs |> Task_Graph.new_node (task, Passive abort);
  in (task, make_queue groups' jobs') end;

fun enqueue name group deps pri job (Queue {groups, jobs}) =
  let
    val task = new_task group name (SOME pri);
    val groups' = group_ancestry (fn gid => add_task (gid, task)) group groups;
    val jobs' = jobs
      |> Task_Graph.new_node (task, Job [job])
      |> fold (add_job task) deps;
  in (task, make_queue groups' jobs') end;

fun extend task job (Queue {groups, jobs}) =
  (case try (get_job jobs) task of
    SOME (Job list) => SOME (make_queue groups (set_job task (Job (job :: list)) jobs))
  | _ => NONE);


(* dequeue *)

fun dequeue_passive thread task (queue as Queue {groups, jobs}) =
  (case try (get_job jobs) task of
    SOME (Passive _) =>
      let val jobs' = set_job task (Running thread) jobs
      in (true, make_queue groups jobs') end
  | _ => (false, queue));

fun dequeue thread (queue as Queue {groups, jobs}) =
  (case Task_Graph.get_first (uncurry ready_job) jobs of
    SOME (result as (task, _)) =>
      let val jobs' = set_job task (Running thread) jobs
      in (SOME result, make_queue groups jobs') end
  | NONE => (NONE, queue));


(* dequeue wrt. dynamic dependencies *)

fun dequeue_deps thread deps (queue as Queue {groups, jobs}) =
  let
    fun ready [] rest = (NONE, rev rest)
      | ready (task :: tasks) rest =
          (case try (Task_Graph.get_entry jobs) task of
            NONE => ready tasks rest
          | SOME entry =>
              (case ready_job task entry of
                NONE => ready tasks (task :: rest)
              | some => (some, List.revAppend (rest, tasks))));

    fun ready_dep _ [] = NONE
      | ready_dep seen (task :: tasks) =
          if Tasks.defined seen task then ready_dep seen tasks
          else
            let val entry as (_, (ds, _)) = Task_Graph.get_entry jobs task in
              (case ready_job task entry of
                NONE => ready_dep (Tasks.update (task, ()) seen) (ds @ tasks)
              | some => some)
            end;

    fun result (res as (task, _)) deps' =
      let val jobs' = set_job task (Running thread) jobs
      in ((SOME res, deps'), make_queue groups jobs') end;
  in
    (case ready deps [] of
      (SOME res, deps') => result res deps'
    | (NONE, deps') =>
        (case ready_dep Tasks.empty deps' of
          SOME res => result res deps'
        | NONE => ((NONE, deps'), queue)))
  end;

end;
