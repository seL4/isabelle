(*  Title:      Pure/markup_expression.ML
    Author:     Makarius

Formally defined kind for Markup.expression.
*)

signature MARKUP_EXPRESSION =
sig
  val check_kind: Proof.context -> xstring * Position.T -> string
  val setup_kind: binding -> theory -> string * theory
  val check: Proof.context -> xstring * Position.T -> Markup.T
  val setup: binding -> Markup.T
end;

structure Markup_Expression: MARKUP_EXPRESSION =
struct

(* theory data *)

structure Data = Theory_Data
(
  type T = unit Name_Space.table;
  val empty : T = Name_Space.empty_table "markup_expression_kind";
  fun merge data : T = Name_Space.merge_tables data;
);


(* kind *)

fun check_kind ctxt =
  Name_Space.check (Context.Proof ctxt) (Data.get (Proof_Context.theory_of ctxt)) #> #1;

fun setup_kind binding thy =
  let
    val context = Name_Space.map_naming (K Name_Space.global_naming) (Context.Theory thy);
    val (name, data') = Name_Space.define context true (binding, ()) (Data.get thy);
  in (name, Data.put data' thy) end;


(* markup *)

fun check ctxt = check_kind ctxt #> Markup.expression;

fun setup binding =
  Context.>>> (Context.map_theory_result (setup_kind binding #>> Markup.expression));

end;
