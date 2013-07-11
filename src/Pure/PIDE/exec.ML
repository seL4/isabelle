(*  Title:      Pure/PIDE/exec.ML
    Author:     Makarius

Global management of command execution fragments.
*)

signature EXEC =
sig
  val is_stable: Document_ID.exec -> bool
  val running: Document_ID.exec -> unit
  val finished: Document_ID.exec -> unit
  val canceled: Document_ID.exec -> unit
  val purge_unstable: unit -> unit
end;

structure Exec: EXEC =
struct

val running_execs =
  Synchronized.var "Exec.running_execs" (Inttab.empty: {stable: bool} Inttab.table);

fun is_stable exec_id =
  not (Par_Exn.is_interrupted (Future.join_results (Goal.peek_futures exec_id))) andalso
  (case Inttab.lookup (Synchronized.value running_execs) exec_id of
    NONE => true
  | SOME {stable} => stable);

fun running exec_id =
  Synchronized.change running_execs (Inttab.update_new (exec_id, {stable = true}));

fun finished exec_id =
  Synchronized.change running_execs (Inttab.delete exec_id);

fun canceled exec_id =
  Synchronized.change running_execs (Inttab.update (exec_id, {stable = false}));

fun purge_unstable () =
  Synchronized.guarded_access running_execs
    (fn tab =>
      let
        val unstable = Inttab.fold (fn (exec_id, {stable = false}) => cons exec_id | _ => I) tab [];
        val tab' = fold Inttab.delete unstable tab;
      in SOME ((), tab') end);

end;

