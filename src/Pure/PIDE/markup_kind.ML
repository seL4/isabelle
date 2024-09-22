(*  Title:      Pure/markup_kind.ML
    Author:     Makarius

Formally defined kind for Markup.expression.
*)

signature MARKUP_KIND =
sig
  val check_expression_kind: Proof.context -> xstring * Position.T -> string
  val setup_expression_kind: binding -> theory -> string * theory
  val check_expression: Proof.context -> xstring * Position.T -> Markup.T
  val setup_expression: binding -> Markup.T
  val markup_type: Markup.T
  val markup_type_application: Markup.T
  val markup_term: Markup.T
  val markup_term_application: Markup.T
  val markup_term_abstraction: Markup.T
  val markup_prop: Markup.T
  val markup_prop_application: Markup.T
  val markup_prop_abstraction: Markup.T
end;

structure Markup_Kind: MARKUP_KIND =
struct

(* theory data *)

structure Data = Theory_Data
(
  type T = unit Name_Space.table;
  val empty : T = Name_Space.empty_table "markup_expression_kind";
  fun merge data : T = Name_Space.merge_tables data;
);


(* kind *)

fun check_expression_kind ctxt =
  Name_Space.check (Context.Proof ctxt) (Data.get (Proof_Context.theory_of ctxt)) #> #1;

fun setup_expression_kind binding thy =
  let
    val context = Name_Space.map_naming (K Name_Space.global_naming) (Context.Theory thy);
    val (name, data') = Name_Space.define context true (binding, ()) (Data.get thy);
  in (name, Data.put data' thy) end;


(* markup *)

fun check_expression ctxt = check_expression_kind ctxt #> Markup.expression;

fun setup_expression binding =
  Context.>>> (Context.map_theory_result (setup_expression_kind binding #>> Markup.expression));


(* concrete markup *)

val markup_type = setup_expression (Binding.make ("type", \<^here>));
val markup_type_application = setup_expression (Binding.make ("type_application", \<^here>));

val markup_term = setup_expression (Binding.make ("term", \<^here>));
val markup_term_application = setup_expression (Binding.make ("term_application", \<^here>));
val markup_term_abstraction = setup_expression (Binding.make ("term_abstraction", \<^here>));

val markup_prop = setup_expression (Binding.make ("prop", \<^here>));
val markup_prop_application = setup_expression (Binding.make ("prop_application", \<^here>));
val markup_prop_abstraction = setup_expression (Binding.make ("prop_abstraction", \<^here>));

end;
