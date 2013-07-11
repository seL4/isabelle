(*  Title:      Pure/PIDE/exec.ML
    Author:     Makarius

Global management of command execution fragments.
*)

signature EXEC =
sig
  val running: Document_ID.exec -> unit
  val finished: Document_ID.exec -> bool -> unit
  val is_stable: Document_ID.exec -> bool
  val peek_running: Document_ID.exec -> Future.group option
  val purge_unstable: unit -> unit
end;

structure Exec: EXEC =
struct

type status = Future.group option;  (*SOME group: running, NONE: canceled/unstable*)
val execs = Synchronized.var "Exec.execs" (Inttab.empty: status Inttab.table);

fun running exec_id =
  let
    val group =
      (case Future.worker_group () of
        SOME group => group
      | NONE => error ("Missing worker thread context for execution " ^ Document_ID.print exec_id));
  in Synchronized.change execs (Inttab.update_new (exec_id, SOME group)) end;

fun finished exec_id stable =
  Synchronized.change execs
    (if stable then Inttab.delete exec_id else Inttab.update (exec_id, NONE));

fun is_stable exec_id =
  not (Par_Exn.is_interrupted (Future.join_results (Goal.peek_futures exec_id))) andalso
  (case Inttab.lookup (Synchronized.value execs) exec_id of
    NONE => true
  | SOME status => is_some status);

fun peek_running exec_id =
  (case Inttab.lookup (Synchronized.value execs) exec_id of
    SOME (SOME group) => SOME group
  | _ => NONE);

fun purge_unstable () =
  Synchronized.guarded_access execs
    (fn tab =>
      let
        val unstable = Inttab.fold (fn (exec_id, NONE) => cons exec_id | _ => I) tab [];
        val tab' = fold Inttab.delete unstable tab;
      in SOME ((), tab') end);

end;

