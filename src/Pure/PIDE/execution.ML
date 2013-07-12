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
  val finished: Document_ID.exec -> unit
  val peek: Document_ID.exec -> Future.group option
  val snapshot: unit -> Future.group list
end;

structure Execution: EXECUTION =
struct

val state =
  Synchronized.var "Execution.state"
    (Document_ID.none, Inttab.empty: Future.group Inttab.table);


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
            Inttab.update_new (exec_id, Future.the_worker_group ()) execs
              handle Inttab.DUP dup => error ("Duplicate execution " ^ Document_ID.print dup)
          else execs;
      in SOME (continue, (execution_id', execs')) end);

fun finished exec_id =
  Synchronized.change state
    (apsnd (fn execs =>
      Inttab.delete exec_id execs
        handle Inttab.UNDEF bad =>
          error ("Attempt to finish unknown execution: " ^ Document_ID.print bad)));

fun peek exec_id =
  Inttab.lookup (snd (Synchronized.value state)) exec_id;

fun snapshot () =
  Inttab.fold (cons o #2) (snd (Synchronized.value state)) [];

end;

