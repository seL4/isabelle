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
  val is_running_exec: Document_ID.exec -> bool
  val running: Document_ID.execution -> Document_ID.exec -> Future.group list -> bool
  val peek: Document_ID.exec -> Future.group list
  val cancel: Document_ID.exec -> unit
  val terminate: Document_ID.exec -> unit
  val fork: {name: string, pos: Position.T, pri: int} -> (unit -> 'a) -> 'a future
  val purge: Document_ID.exec list -> unit
  val reset: unit -> Future.group list
  val shutdown: unit -> unit
end;

structure Execution: EXECUTION =
struct

(* global state *)

datatype state = State of
  {execution: Document_ID.execution,  (*overall document execution*)
   execs: Future.group list Inttab.table};  (*command execs with registered forks*)

fun make_state (execution, execs) = State {execution = execution, execs = execs};
fun map_state f (State {execution, execs}) = make_state (f (execution, execs));

val init_state = make_state (Document_ID.none, Inttab.make [(Document_ID.none, [])]);
val state = Synchronized.var "Execution.state" init_state;

fun get_state () = let val State args = Synchronized.value state in args end;
fun change_state f = Synchronized.change state (map_state f);


(* unique running execution *)

fun start () =
  let
    val execution_id = Document_ID.make ();
    val _ = change_state (apfst (K execution_id));
  in execution_id end;

fun discontinue () = change_state (apfst (K Document_ID.none));

fun is_running execution_id = execution_id = #execution (get_state ());


(* execs *)

fun is_running_exec exec_id =
  Inttab.defined (#execs (get_state ())) exec_id;

fun running execution_id exec_id groups =
  Synchronized.change_result state
    (fn State {execution = execution_id', execs} =>
      let
        val continue = execution_id = execution_id';
        val execs' =
          if continue then
            Inttab.update_new (exec_id, groups) execs
              handle Inttab.DUP dup =>
                raise Fail ("Execution already registered: " ^ Document_ID.print dup)
          else execs;
      in (continue, make_state (execution_id', execs')) end);

fun peek exec_id =
  Inttab.lookup_list (#execs (get_state ())) exec_id;

fun cancel exec_id = List.app Future.cancel_group (peek exec_id);
fun terminate exec_id = List.app Future.terminate (peek exec_id);


(* fork *)

fun status task markups =
  let val props = Markup.properties [(Markup.taskN, Task_Queue.str_of_task task)]
  in Output.status (implode (map (Markup.markup_only o props) markups)) end;

fun fork {name, pos, pri} e =
  uninterruptible (fn _ => Position.setmp_thread_data pos (fn () =>
    let
      val exec_id = the_default 0 (Position.parse_id pos);
      val group = Future.worker_subgroup ();
      val _ = change_state (apsnd (fn execs =>
        if Inttab.defined execs exec_id
        then Inttab.cons_list (exec_id, group) execs
        else raise Fail ("Cannot fork from unregistered execution: " ^ Document_ID.print exec_id)));

      val future =
        (singleton o Future.forks)
          {name = name, group = SOME group, deps = [], pri = pri, interrupts = false}
          (fn () =>
            let
              val task = the (Future.worker_task ());
              val _ = status task [Markup.running];
              val result =
                Exn.capture (Future.interruptible_task e) ()
                |> Future.identify_result pos;
              val _ = status task [Markup.finished, Markup.joined];
              val _ =
                (case result of
                  Exn.Res _ => ()
                | Exn.Exn exn =>
                    if exec_id = 0 orelse Exn.is_interrupt exn then ()
                    else
                      (status task [Markup.failed];
                       Output.report (Markup.markup_only Markup.bad);
                       List.app (Future.error_msg pos) (ML_Compiler.exn_messages_ids exn)));
            in Exn.release result end);
      val _ = status (Future.task_of future) [Markup.forked];
    in future end)) ();


(* cleanup *)

fun purge exec_ids =
  (change_state o apsnd) (fn execs =>
    let
      val execs' = fold Inttab.delete_safe exec_ids execs;
      val () =
        (execs', ()) |-> Inttab.fold (fn (exec_id, groups) => fn () =>
          if Inttab.defined execs' exec_id then ()
          else groups |> List.app (fn group =>
            if Task_Queue.is_canceled group then ()
            else raise Fail ("Attempt to purge valid execution: " ^ Document_ID.print exec_id)));
    in execs' end);

fun reset () =
  Synchronized.change_result state (fn State {execs, ...} =>
    let val groups = Inttab.fold (append o #2) execs []
    in (groups, init_state) end);

fun shutdown () =
  (Future.shutdown ();
    (case maps Task_Queue.group_status (reset ()) of
      [] => ()
    | exns => raise Par_Exn.make exns));

end;

