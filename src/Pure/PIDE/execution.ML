(*  Title:      Pure/PIDE/execution.ML
    Author:     Makarius

Global management of execution.  Unique running execution serves as
barrier for further exploration of forked command execs.
*)

signature EXECUTION =
sig
  val start: unit -> Document_ID.execution
  val discontinue: unit -> unit
  val is_running: Document_ID.execution -> bool
  val active_tasks: string -> Future.task list
  val worker_task_active: bool -> string -> unit
  val is_running_exec: Document_ID.exec -> bool
  val running: Document_ID.execution -> Document_ID.exec -> Future.group list -> bool
  val snapshot: Document_ID.exec list -> Future.task list
  val join: Document_ID.exec list -> unit
  val peek: Document_ID.exec -> Future.group list
  val cancel: Document_ID.exec -> unit
  type params = {name: string, pos: Position.T, pri: int}
  val fork: params -> (unit -> 'a) -> 'a future
  val print: params -> (unit -> unit) -> unit
  val fork_prints: Document_ID.exec -> unit
  val purge: Document_ID.exec list -> unit
  val reset: unit -> Future.group list
  val shutdown: unit -> unit
end;

structure Execution: EXECUTION =
struct

(* global state *)

type print = {name: string, pri: int, body: unit -> unit};
type execs = (Future.group list * print list) (*active forks, prints*) Inttab.table;
val init_execs: execs = Inttab.make [(Document_ID.none, ([], []))];

datatype state =
  State of
   {execution_id: Document_ID.execution,  (*overall document execution*)
    nodes: Future.task list Symtab.table,  (*active nodes*)
    execs: execs};  (*running command execs*)

fun make_state (execution_id, nodes, execs) =
  State {execution_id = execution_id, nodes = nodes, execs = execs};

local
  val state =
    Synchronized.var "Execution.state" (make_state (Document_ID.none, Symtab.empty, init_execs));
in

fun get_state () = let val State args = Synchronized.value state in args end;

fun change_state_result f =
  Synchronized.change_result state (fn (State {execution_id, nodes, execs}) =>
    let val (result, args') = f (execution_id, nodes, execs)
    in (result, make_state args') end);

fun change_state f =
  Synchronized.change state (fn (State {execution_id, nodes, execs}) =>
    make_state (f (execution_id, nodes, execs)));

end;

fun unregistered exec_id = "Unregistered execution: " ^ Document_ID.print exec_id;


(* unique running execution *)

fun start () =
  let
    val execution_id = Document_ID.make ();
    val _ = change_state (fn (_, nodes, execs) => (execution_id, nodes, execs));
  in execution_id end;

fun discontinue () =
  change_state (fn (_, nodes, execs) => (Document_ID.none, nodes, execs));

fun is_running execution_id =
  execution_id = #execution_id (get_state ());


(* active nodes *)

fun active_tasks node_name =
  Symtab.lookup_list (#nodes (get_state ())) node_name;

fun worker_task_active insert node_name =
  change_state (fn (execution_id, nodes, execs) =>
    let
      val nodes' = nodes
        |> (if insert then Symtab.insert_list else Symtab.remove_list)
          Task_Queue.eq_task (node_name, the (Future.worker_task ()));
    in (execution_id, nodes', execs) end);


(* running execs *)

fun is_running_exec exec_id =
  Inttab.defined (#execs (get_state ())) exec_id;

fun running execution_id exec_id groups =
  change_state_result (fn (execution_id', nodes, execs) =>
    let
      val ok = execution_id = execution_id' andalso not (Inttab.defined execs exec_id);
      val execs' = execs |> ok ? Inttab.update (exec_id, (groups, []));
    in (ok, (execution_id', nodes, execs')) end);


(* exec groups and tasks *)

fun exec_groups (execs: execs) exec_id =
  (case Inttab.lookup execs exec_id of
    SOME (groups, _) => groups
  | NONE => []);

fun snapshot [] = []
  | snapshot exec_ids =
      change_state_result
        (`(fn (_, _, execs) => Future.snapshot (maps (exec_groups execs) exec_ids)));

fun join exec_ids =
  (case snapshot exec_ids of
    [] => ()
  | tasks =>
      ((singleton o Future.forks)
        {name = "Execution.join", group = SOME (Future.new_group NONE),
          deps = tasks, pri = 0, interrupts = false} I
      |> Future.join; join exec_ids));

fun peek exec_id = exec_groups (#execs (get_state ())) exec_id;

fun cancel exec_id = List.app Future.cancel_group (peek exec_id);


(* fork *)

fun status task markups =
  let
    val props =
      if ! Multithreading.trace >= 2
      then [(Markup.taskN, Task_Queue.str_of_task task)] else [];
  in Output.status (map (Markup.markup_only o Markup.properties props) markups) end;

type params = {name: string, pos: Position.T, pri: int};

fun fork ({name, pos, pri}: params) e =
  Thread_Attributes.uninterruptible (fn _ => Position.setmp_thread_data pos (fn () =>
    let
      val exec_id = the_default 0 (Position.parse_id pos);
      val group = Future.worker_subgroup ();
      val _ = change_state (fn (execution_id, nodes, execs) =>
        (case Inttab.lookup execs exec_id of
          SOME (groups, prints) =>
            let val execs' = Inttab.update (exec_id, (group :: groups, prints)) execs
            in (execution_id, nodes, execs') end
        | NONE => raise Fail (unregistered exec_id)));

      val future =
        (singleton o Future.forks)
          {name = name, group = SOME group, deps = [], pri = pri, interrupts = false}
          (fn () =>
            let
              val task = the (Future.worker_task ());
              val _ = status task [Markup.running];
              val result =
                Exn.capture (Future.interruptible_task e) ()
                |> Future.identify_result pos
                |> Exn.map_exn Runtime.thread_context;
              val errors =
                Exn.capture (fn () =>
                  (case result of
                    Exn.Exn exn =>
                     (status task [Markup.failed];
                      status task [Markup.finished];
                      Position.report pos (Markup.bad ());
                      if exec_id = 0 then ()
                      else List.app (Future.error_message pos) (Runtime.exn_messages exn))
                  | Exn.Res _ =>
                      status task [Markup.finished])) ();
              val _ = status task [Markup.joined];
            in Exn.release errors; Exn.release result end);

      val _ = status (Future.task_of future) [Markup.forked];
    in future end)) ();


(* print *)

fun print ({name, pos, pri}: params) e =
  change_state (fn (execution_id, nodes, execs) =>
    let
      val exec_id = the_default 0 (Position.parse_id pos);
      val print = {name = name, pri = pri, body = e};
    in
      (case Inttab.lookup execs exec_id of
        SOME (groups, prints) =>
          let val execs' = Inttab.update (exec_id, (groups, print :: prints)) execs
          in (execution_id, nodes, execs') end
      | NONE => raise Fail (unregistered exec_id))
    end);

fun fork_prints exec_id =
  (case Inttab.lookup (#execs (get_state ())) exec_id of
    SOME (_, prints) =>
      if Future.relevant prints then
        let val pos = Position.thread_data () in
          List.app (fn {name, pri, body} =>
            ignore (fork {name = name, pos = pos, pri = pri} body)) (rev prints)
        end
      else List.app (fn {body, ...} => body ()) (rev prints)
  | NONE => raise Fail (unregistered exec_id));


(* cleanup *)

fun purge exec_ids =
  change_state (fn (execution_id, nodes, execs) =>
    let
      val execs' = fold Inttab.delete_safe exec_ids execs;
      val () =
        (execs', ()) |-> Inttab.fold (fn (exec_id, (groups, _)) => fn () =>
          if Inttab.defined execs' exec_id then ()
          else groups |> List.app (fn group =>
            if Task_Queue.is_canceled group then ()
            else raise Fail ("Attempt to purge valid execution: " ^ Document_ID.print exec_id)));
    in (execution_id, nodes, execs') end);

fun reset () =
  change_state_result (fn (_, _, execs) =>
    let val groups = Inttab.fold (append o #1 o #2) execs []
    in (groups, (Document_ID.none, Symtab.empty, init_execs)) end);

fun shutdown () =
  (Future.shutdown ();
    (case maps Task_Queue.group_status (reset ()) of
      [] => ()
    | exns => raise Par_Exn.make exns));

end;
