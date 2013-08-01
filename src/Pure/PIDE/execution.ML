(*  Title:      Pure/PIDE/execution.ML
    Author:     Makarius

Global management of execution.  Unique running execution serves as
barrier for further exploration of exec fragments.
*)

signature EXECUTION =
sig
  val reset: unit -> unit
  val start: unit -> Document_ID.execution
  val discontinue: unit -> unit
  val is_running: Document_ID.execution -> bool
  val is_running_exec: Document_ID.exec -> bool
  val running: Document_ID.execution -> Document_ID.exec -> bool
  val cancel: Document_ID.exec -> unit
  val terminate: Document_ID.exec -> unit
end;

structure Execution: EXECUTION =
struct

(* global state *)

type state = Document_ID.execution * Future.group Inttab.table;

val init_state: state = (Document_ID.none, Inttab.empty);
val state = Synchronized.var "Execution.state" init_state;


(* unique running execution *)

fun reset () = Synchronized.change state (K init_state);

fun start () =
  let
    val execution_id = Document_ID.make ();
    val _ = Synchronized.change state (apfst (K execution_id));
  in execution_id end;

fun discontinue () =
  Synchronized.change state (apfst (K Document_ID.none));

fun is_running execution_id = execution_id = fst (Synchronized.value state);


(* registered execs *)

fun is_running_exec exec_id =
  Inttab.defined (snd (Synchronized.value state)) exec_id;

fun running execution_id exec_id =
  Synchronized.guarded_access state
    (fn (execution_id', execs) =>
      let
        val continue = execution_id = execution_id';
        val execs' =
          if continue then
            Inttab.update_new (exec_id, Future.the_worker_group ()) execs
              handle Inttab.DUP dup => error ("Duplicate execution " ^ Document_ID.print dup)
          else execs;
      in SOME (continue, (execution_id', execs')) end);

fun peek_list exec_id =
  the_list (Inttab.lookup (snd (Synchronized.value state)) exec_id);

fun cancel exec_id = List.app Future.cancel_group (peek_list exec_id);
fun terminate exec_id = List.app Future.terminate (peek_list exec_id);

end;

