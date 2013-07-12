(*  Title:      Pure/PIDE/execution.ML
    Author:     Makarius

Global management of command execution fragments.
*)

signature EXECUTION =
sig
  type context
  val no_context: context
  val drop_context: context -> unit
  val fresh_context: unit -> context
  val is_running: context -> bool
  val running: context -> Document_ID.exec -> bool
  val finished: Document_ID.exec -> bool -> unit
  val is_stable: Document_ID.exec -> bool
  val peek_running: Document_ID.exec -> Future.group option
  val purge_canceled: unit -> unit
  val terminate_all: unit -> unit
end;

structure Execution: EXECUTION =
struct

(* global state *)

datatype context = Context of Document_ID.generic;
val no_context = Context Document_ID.none;

type status = Future.group option;  (*SOME group: running, NONE: canceled*)
val state = Synchronized.var "Execution.state" (no_context, Inttab.empty: status Inttab.table);


(* unique execution context *)

fun drop_context context =
  Synchronized.change state
    (apfst (fn context' => if context = context' then no_context else context'));

fun fresh_context () =
  let
    val context = Context (Document_ID.make ());
    val _ = Synchronized.change state (apfst (K context));
  in context end;

fun is_running context = context = fst (Synchronized.value state);


(* registered execs *)

fun running context exec_id =
  Synchronized.guarded_access state
    (fn (current_context, execs) =>
      let
        val cont = context = current_context;
        val execs' =
          if cont then
            Inttab.update_new (exec_id, SOME (Future.the_worker_group ())) execs
              handle Inttab.DUP dup => error ("Duplicate execution " ^ Document_ID.print dup)
          else execs;
      in SOME (cont, (current_context, execs')) end);

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
    (fn (context, execs) =>
      let
        val canceled = Inttab.fold (fn (exec_id, NONE) => cons exec_id | _ => I) execs [];
        val execs' = fold Inttab.delete canceled execs;
      in SOME ((), (context, execs')) end);

fun terminate_all () =
  let
    val groups =
      Inttab.fold (fn (_, SOME group) => cons group | _ => I)
        (snd (Synchronized.value state)) [];
    val _ = List.app Future.cancel_group groups;
    val _ = List.app Future.terminate groups;
  in () end;

end;

