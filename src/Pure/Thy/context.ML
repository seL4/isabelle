(*  Title:      Pure/Thy/context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Global contexts: session and theory.
*)

signature BASIC_CONTEXT =
sig
  val get_session: unit -> string list
  val add_session: string -> unit
  val reset_session: unit -> unit
  val get_context: unit -> theory
  val context: theory -> unit
  val reset_context: unit -> unit
  val thm: xstring -> thm
  val thms: xstring -> thm list
end;

signature CONTEXT =
sig
  include BASIC_CONTEXT
  val >> : (theory -> theory) -> unit
end;

structure Context: CONTEXT =
struct


(** session **)

val current_session = ref ([]: string list);

fun get_session () = ! current_session;
fun add_session s = current_session := ! current_session @ [s];
fun reset_session () = current_session := [];



(** theory context **)

val current_theory = ref (None: theory option);

fun get_context () =
  (case current_theory of
    ref (Some thy) => thy
  | _ => error "Unknown theory context");

fun context thy = current_theory := Some thy;
fun reset_context () = current_theory := None;


(* map context *)

nonfix >>;
fun >> f = current_theory := Some (f (get_context ()));


(* retrieve thms *)

fun thm name = PureThy.get_thm (get_context ()) name;
fun thms name = PureThy.get_thms (get_context ()) name;


end;


structure BasicContext: BASIC_CONTEXT = Context;
open BasicContext;
