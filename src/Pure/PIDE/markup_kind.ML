(*  Title:      Pure/markup_kind.ML
    Author:     Makarius

Formally defined kind for Markup.notation and Markup.expression.
*)

signature MARKUP_KIND =
sig
  val get_notation_kinds: Proof.context -> string list
  val check_notation_kind: Proof.context -> xstring * Position.T -> string
  val setup_notation_kind: binding -> theory -> string * theory
  val check_notation: Proof.context -> xstring * Position.T -> Markup.T
  val setup_notation: binding -> Markup.T
  val get_expression_kinds: Proof.context -> string list
  val check_expression_kind: Proof.context -> xstring * Position.T -> string
  val setup_expression_kind: binding -> theory -> string * theory
  val check_expression: Proof.context -> xstring * Position.T -> Markup.T
  val setup_expression: binding -> Markup.T
  val markup_mixfix: Markup.T
  val markup_prefix: Markup.T
  val markup_postfix: Markup.T
  val markup_infix: Markup.T
  val markup_binder: Markup.T
  val markup_type_application: Markup.T
  val markup_application: Markup.T
  val markup_abstraction: Markup.T
end;

structure Markup_Kind: MARKUP_KIND =
struct

(* theory data *)

structure Data = Theory_Data
(
  type T = unit Name_Space.table * unit Name_Space.table;
  val empty : T =
   (Name_Space.empty_table "markup_notation_kind",
    Name_Space.empty_table "markup_expression_kind");
  fun merge ((tab1, tab2), (tab1', tab2')) : T =
   (Name_Space.merge_tables (tab1, tab1'),
    Name_Space.merge_tables (tab2, tab2'));
);


(* kind *)

local

fun get_kinds which ctxt =
  which (Data.get (Proof_Context.theory_of ctxt))
  |> Name_Space.dest_table
  |> map #1
  |> sort_strings;

fun check_kind which ctxt =
  Name_Space.check (Context.Proof ctxt) (which (Data.get (Proof_Context.theory_of ctxt))) #> #1;

fun setup_kind which ap binding thy =
  let
    val context = Name_Space.map_naming (K Name_Space.global_naming) (Context.Theory thy);
    val (name, tab') = Name_Space.define context true (binding, ()) (which (Data.get thy));
  in (name, (Data.map o ap) (K tab') thy) end;

in

val get_notation_kinds = get_kinds #1;
val get_expression_kinds = get_kinds #2;

val check_notation_kind = check_kind #1;
val check_expression_kind = check_kind #2;

val setup_notation_kind = setup_kind #1 apfst;
val setup_expression_kind = setup_kind #2 apsnd;

end;


(* markup *)

fun check_notation ctxt = check_notation_kind ctxt #> Markup.notation;

fun check_expression ctxt = check_expression_kind ctxt #> Markup.expression;

fun setup_notation binding =
  Context.>>> (Context.map_theory_result (setup_notation_kind binding #>> Markup.notation));

fun setup_expression binding =
  Context.>>> (Context.map_theory_result (setup_expression_kind binding #>> Markup.expression));


(* concrete markup *)

val markup_mixfix = setup_notation (Binding.make ("mixfix", \<^here>));
val markup_prefix = setup_notation (Binding.make ("prefix", \<^here>));
val markup_postfix = setup_notation (Binding.make ("postfix", \<^here>));
val markup_infix = setup_notation (Binding.make ("infix", \<^here>));
val markup_binder = setup_notation (Binding.make ("binder", \<^here>));

val markup_type_application = setup_notation (Binding.make ("type_application", \<^here>));
val markup_application = setup_notation (Binding.make ("application", \<^here>));
val markup_abstraction = setup_notation (Binding.make ("abstraction", \<^here>));

end;
