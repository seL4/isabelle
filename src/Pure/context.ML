(*  Title:      Pure/context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

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
  val save: ('a -> 'b) -> 'a -> 'b
  val >> : (theory -> theory) -> unit
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

fun save f x = setmp (get_context ()) f x;


(* map context *)

nonfix >>;
fun >> f = set_context (Some (f (the_context ())));


end;

structure BasicContext: BASIC_CONTEXT = Context;
open BasicContext;
