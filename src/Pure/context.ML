(*  Title:      Pure/context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Global theory context.
*)

signature BASIC_CONTEXT =
sig
  val context: theory -> unit
  val the_context: unit -> theory
end;

signature CONTEXT =
sig
  include BASIC_CONTEXT
  val get_context: unit -> theory option
  val set_context: theory option -> unit
  val reset_context: unit -> unit
  val setmp: theory option -> ('a -> 'b) -> 'a -> 'b
  val pass: theory option -> ('a -> 'b) -> 'a -> 'b * theory option
  val pass_theory: theory -> ('a -> 'b) -> 'a -> 'b * theory
  val save: ('a -> 'b) -> 'a -> 'b
  val >> : (theory -> theory) -> unit
  val ml_output: (string -> unit) * (string -> unit)
  val use_mltext: string -> bool -> theory option -> unit
  val use_mltext_theory: string -> bool -> theory -> theory
  val use_let: string -> string -> string -> theory -> theory
  val use_setup: string -> theory -> theory
end;

structure Context: CONTEXT =
struct


(* theory context *)

local
  val current_theory = ref (None: theory option);
in
  fun get_context () = ! current_theory;
  fun set_context opt_thy = current_theory := opt_thy;
  fun setmp opt_thy f x = Library.setmp current_theory opt_thy f x;
end;

fun the_context () =
  (case get_context () of
    Some thy => thy
  | _ => error "Unknown theory context");

fun context thy = set_context (Some thy);
fun reset_context () = set_context None;

fun pass opt_thy f x =
  setmp opt_thy (fn x => let val y = f x in (y, get_context ()) end) x;

fun pass_theory thy f x =
  (case pass (Some thy) f x of
    (y, Some thy') => (y, thy')
  | (_, None) => error "Lost theory context in ML");

fun save f x = setmp (get_context ()) f x;


(* map context *)

nonfix >>;
fun >> f = set_context (Some (f (the_context ())));


(* use ML text *)

val ml_output = (writeln, error_msg: string -> unit);
fun use_output verb txt = use_text ml_output verb (Symbol.plain_output txt);

fun use_mltext txt verb opt_thy = setmp opt_thy (fn () => use_output verb txt) ();
fun use_mltext_theory txt verb thy = #2 (pass_theory thy (use_output verb) txt);

fun use_context txt = use_mltext_theory ("Context.>> (" ^ txt ^ ");") false;

fun use_let bind body txt =
  use_context ("let " ^ bind ^ " = " ^ txt ^ " in\n" ^ body ^ " end");

val use_setup =
  use_let "val setup: (theory -> theory) list" "Library.apply setup";


end;

structure BasicContext: BASIC_CONTEXT = Context;
open BasicContext;
