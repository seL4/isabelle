(* Author: Florian Haftmann, TU Muenchen *)

header {* Reflecting Pure types into HOL *}

theory Typerep
imports Plain String
begin

datatype typerep = Typerep String.literal "typerep list"

class typerep =
  fixes typerep :: "'a itself \<Rightarrow> typerep"
begin

definition typerep_of :: "'a \<Rightarrow> typerep" where
  [simp]: "typerep_of x = typerep TYPE('a)"

end

setup {*
let
  fun typerep_tr (*"_TYPEREP"*) [ty] =
        Lexicon.const @{const_syntax typerep} $ (Lexicon.const "_constrain" $ Lexicon.const "TYPE" $
          (Lexicon.const "itself" $ ty))
    | typerep_tr (*"_TYPEREP"*) ts = raise TERM ("typerep_tr", ts);
  fun typerep_tr' show_sorts (*"typerep"*)
          (Type ("fun", [Type ("itself", [T]), _])) (Const (@{const_syntax TYPE}, _) :: ts) =
        Term.list_comb (Lexicon.const "_TYPEREP" $ Syntax.term_of_typ show_sorts T, ts)
    | typerep_tr' _ T ts = raise Match;
in
  Sign.add_syntax_i
    [("_TYPEREP", SimpleSyntax.read_typ "type => logic", Delimfix "(1TYPEREP/(1'(_')))")]
  #> Sign.add_trfuns ([], [("_TYPEREP", typerep_tr)], [], [])
  #> Sign.add_trfunsT [(@{const_syntax typerep}, typerep_tr')]
end
*}

setup {*
let

fun add_typerep tyco thy =
  let
    val sorts = replicate (Sign.arity_number thy tyco) @{sort typerep};
    val vs = Name.names Name.context "'a" sorts;
    val ty = Type (tyco, map TFree vs);
    val lhs = Const (@{const_name typerep}, Term.itselfT ty --> @{typ typerep})
      $ Free ("T", Term.itselfT ty);
    val rhs = @{term Typerep} $ HOLogic.mk_literal tyco
      $ HOLogic.mk_list @{typ typerep} (map (HOLogic.mk_typerep o TFree) vs);
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in
    thy
    |> TheoryTarget.instantiation ([tyco], vs, @{sort typerep})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (Attrib.empty_binding, eq)))
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun ensure_typerep tyco thy = if not (can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort typerep})
  andalso can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort type}
  then add_typerep tyco thy else thy;

in

add_typerep @{type_name fun}
#> TypedefPackage.interpretation ensure_typerep
#> Code.type_interpretation (ensure_typerep o fst)

end
*}

lemma [code]:
  "eq_class.eq (Typerep tyco1 tys1) (Typerep tyco2 tys2) \<longleftrightarrow> eq_class.eq tyco1 tyco2
     \<and> list_all2 eq_class.eq tys1 tys2"
  by (auto simp add: equals_eq [symmetric] list_all2_eq [symmetric])

code_type typerep
  (Eval "Term.typ")

code_const Typerep
  (Eval "Term.Type/ (_, _)")

code_reserved Eval Term

hide (open) const typerep Typerep

end
