(*  Title:      Pure/Thy/context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Global contexts: session and theory.
*)

signature BASIC_CONTEXT =
sig
  val context: theory -> unit
  val the_context: unit -> theory
  val thm: xstring -> thm
  val thms: xstring -> thm list
  val Goal: string -> thm list
  val Goalw: thm list -> string -> thm list
  val Open_locale: xstring -> unit
  val Close_locale: unit -> unit
end;

signature CONTEXT =
sig
  include BASIC_CONTEXT
  val get_session: unit -> string list
  val add_session: string -> unit
  val reset_session: unit -> unit
  val welcome: unit -> string
  val get_context: unit -> theory option
  val set_context: theory option -> unit
  val reset_context: unit -> unit
  val >> : (theory -> theory) -> unit
end;

structure Context: CONTEXT =
struct


(** session **)

val current_session = ref ([]: string list);

fun get_session () = ! current_session;
fun add_session s = current_session := ! current_session @ [s];
fun reset_session () = current_session := [];

fun welcome () =
  "Welcome to Isabelle/" ^
    (case get_session () of [] => "Pure" | ss => space_implode "/" ss) ^
    " (" ^ version ^ ")";



(** theory context **)

local
  val current_theory = ref (None: theory option);
in
  fun get_context () = ! current_theory;
  fun set_context opt_thy = current_theory := opt_thy;
end;

fun the_context () =
  (case get_context () of
    Some thy => thy
  | _ => error "Unknown theory context");

fun context thy = set_context (Some thy);
fun reset_context () = set_context None;


(* map context *)

nonfix >>;
fun >> f = set_context (Some (f (the_context ())));


(* retrieve thms *)

fun thm name = Locale.get_thm (the_context ()) name;
fun thms name = Locale.get_thms (the_context ()) name;


(* shortcut goal commands *)

fun Goal s = Goals.atomic_goal (the_context ()) s;
fun Goalw thms s = Goals.atomic_goalw (the_context ()) thms s;


(* scope manipulation *)

fun Open_locale xname = (Locale.open_locale xname (the_context ()); ());
fun Close_locale () = (Locale.close_locale (the_context ()); ());


end;


structure BasicContext: BASIC_CONTEXT = Context;
open BasicContext;
