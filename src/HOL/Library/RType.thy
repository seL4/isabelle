(*  Title:      HOL/Library/RType.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Reflecting Pure types into HOL *}

theory RType
imports Plain "~~/src/HOL/List" "~~/src/HOL/Code_Message" "~~/src/HOL/Code_Index" (* import all 'special code' types *)
begin

datatype "rtype" = RType message_string "rtype list"

class rtype =
  fixes rtype :: "'a\<Colon>{} itself \<Rightarrow> rtype"
begin

definition
  rtype_of :: "'a \<Rightarrow> rtype"
where
  [simp]: "rtype_of x = rtype TYPE('a)"

end

setup {*
let
  fun rtype_tr (*"_RTYPE"*) [ty] =
        Lexicon.const @{const_syntax rtype} $ (Lexicon.const "_constrain" $ Lexicon.const "TYPE" $
          (Lexicon.const "itself" $ ty))
    | rtype_tr (*"_RTYPE"*) ts = raise TERM ("rtype_tr", ts);
  fun rtype_tr' show_sorts (*"rtype"*)
          (Type ("fun", [Type ("itself", [T]), _])) (Const (@{const_syntax TYPE}, _) :: ts) =
        Term.list_comb (Lexicon.const "_RTYPE" $ Syntax.term_of_typ show_sorts T, ts)
    | rtype_tr' _ T ts = raise Match;
in
  Sign.add_syntax_i
    [("_RTYPE", SimpleSyntax.read_typ "type => logic", Delimfix "(1RTYPE/(1'(_')))")]
  #> Sign.add_trfuns ([], [("_RTYPE", rtype_tr)], [], [])
  #> Sign.add_trfunsT [(@{const_syntax rtype}, rtype_tr')]
end
*}

ML {*
structure RType =
struct

fun mk f (Type (tyco, tys)) =
      @{term RType} $ Message_String.mk tyco
        $ HOLogic.mk_list @{typ rtype} (map (mk f) tys)
  | mk f (TFree v) =
      f v;

fun rtype ty =
  Const (@{const_name rtype}, Term.itselfT ty --> @{typ rtype})
    $ Logic.mk_type ty;

fun add_def tyco thy =
  let
    val sorts = replicate (Sign.arity_number thy tyco) @{sort rtype};
    val vs = Name.names Name.context "'a" sorts;
    val ty = Type (tyco, map TFree vs);
    val lhs = Const (@{const_name rtype}, Term.itselfT ty --> @{typ rtype})
      $ Free ("T", Term.itselfT ty);
    val rhs = mk (rtype o TFree) ty;
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in
    thy
    |> TheoryTarget.instantiation ([tyco], vs, @{sort rtype})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (("", []), eq)))
    |> snd
    |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
    |> LocalTheory.exit
    |> ProofContext.theory_of
  end;

fun perhaps_add_def tyco thy =
  let
    val inst = can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort rtype}
  in if inst then thy else add_def tyco thy end;

end;
*}

setup {*
  RType.add_def @{type_name prop}
  #> RType.add_def @{type_name fun}
  #> RType.add_def @{type_name itself}
  #> RType.add_def @{type_name bool}
  #> TypedefPackage.interpretation RType.perhaps_add_def
*}

lemma [code func]:
  "RType tyco1 tys1 = RType tyco2 tys2 \<longleftrightarrow> tyco1 = tyco2
     \<and> list_all2 (op =) tys1 tys2"
  by (auto simp add: list_all2_eq [symmetric])

code_type rtype
  (SML "Term.typ")

code_const RType
  (SML "Term.Type/ (_, _)")

code_reserved SML Term

hide (open) const rtype RType

end
