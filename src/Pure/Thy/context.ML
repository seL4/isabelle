(*  Title:      Pure/Thy/context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Global contexts: session and theory.
*)

signature CONTEXT =
sig
  val get_session: unit -> string list
  val add_session: string -> unit
  val reset_session: unit -> unit
  val get_context: unit -> theory
  val context: theory -> unit
  val reset_context: unit -> unit
end;

structure Context: CONTEXT =
struct


(* session *)

val current_session = ref ([]: string list);

fun get_session () = ! current_session;
fun add_session s = current_session := ! current_session @ [s];
fun reset_session () = current_session := [];


(* theory context *)

val current_theory = ref (None: theory option);

fun get_context () =
  (case current_theory of
    ref (Some thy) => thy
  | _ => error "Unknown theory context");

fun context thy = current_theory := Some thy;
fun reset_context () = current_theory := None;


end;

open Context;
