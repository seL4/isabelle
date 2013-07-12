(*  Title:      Pure/PIDE/execution.ML
    Author:     Makarius

Global management of execution.  Unique running execution serves as
barrier for further exploration of exec particles.
*)

signature EXECUTION =
sig
  val start: unit -> Document_ID.execution
  val discontinue: unit -> unit
  val is_running: Document_ID.execution -> bool
  val running: Document_ID.execution -> Document_ID.exec -> bool
  val finished: Document_ID.exec -> bool -> unit
  val is_stable: Document_ID.exec -> bool
  val peek_running: Document_ID.exec -> Future.group option
  val purge_canceled: unit -> unit
  val terminate_all: unit -> unit
end;

structure Execution: EXECUTION =
struct

type status = Future.group option;  (*SOME group: running, NONE: canceled*)
val state = Synchronized.var "Execution.state" (Document_ID.none, Inttab.empty: status Inttab.table);


(* unique running execution *)

fun start () =
  let
    val execution_id = Document_ID.make ();
    val _ = Synchronized.change state (apfst (K execution_id));
  in execution_id end;

fun discontinue () =
  Synchronized.change state (apfst (K Document_ID.none));

fun is_running execution_id = execution_id = fst (Synchronized.value state);


(* registered execs *)

fun running execution_id exec_id =
  Synchronized.guarded_access state
    (fn (execution_id', execs) =>
      let
        val continue = execution_id = execution_id';
        val execs' =
          if continue then
            Inttab.update_new (exec_id, SOME (Future.the_worker_group ())) execs
              handle Inttab.DUP dup => error ("Duplicate execution " ^ Document_ID.print dup)
          else execs;
      in SOME (continue, (execution_id', execs')) end);

fun finished exec_id stable =
  Synchronized.change state
    (apsnd (fn execs =>
      if not (Inttab.defined execs exec_id) then
        error ("Attempt to finish unknown execution: " ^ Document_ID.print exec_id)
      else if stable then Inttab.delete exec_id execs
      else Inttab.update (exec_id, NONE) execs));

fun is_stable exec_id =
  not (Par_Exn.is_interrupted (Future.join_results (Goal.peek_futures exec_id))) andalso
  (case Inttab.lookup (snd (Synchronized.value state)) exec_id of
    NONE => true
  | SOME status => is_some status);

fun peek_running exec_id =
  (case Inttab.lookup (snd (Synchronized.value state)) exec_id of
    SOME (SOME group) => SOME group
  | _ => NONE);

fun purge_canceled () =
  Synchronized.guarded_access state
    (fn (execution_id, execs) =>
      let
        val canceled = Inttab.fold (fn (exec_id, NONE) => cons exec_id | _ => I) execs [];
        val execs' = fold Inttab.delete canceled execs;
      in SOME ((), (execution_id, execs')) end);

fun terminate_all () =
  let
    val groups =
      Inttab.fold (fn (_, SOME group) => cons group | _ => I)
        (snd (Synchronized.value state)) [];
    val _ = List.app Future.cancel_group groups;
    val _ = List.app Future.terminate groups;
  in () end;

end;

