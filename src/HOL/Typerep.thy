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

syntax
  "_TYPEREP" :: "type => logic"  ("(1TYPEREP/(1'(_')))")

parse_translation {*
let
  fun typerep_tr (*"_TYPEREP"*) [ty] =
        Syntax.const @{const_syntax typerep} $
          (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "TYPE"} $
            (Syntax.const @{type_syntax itself} $ ty))
    | typerep_tr (*"_TYPEREP"*) ts = raise TERM ("typerep_tr", ts);
in [(@{syntax_const "_TYPEREP"}, typerep_tr)] end
*}

typed_print_translation (advanced) {*
let
  fun typerep_tr' ctxt (*"typerep"*)
          (Type (@{type_name fun}, [Type (@{type_name itself}, [T]), _]))
          (Const (@{const_syntax TYPE}, _) :: ts) =
        Term.list_comb
          (Syntax.const @{syntax_const "_TYPEREP"} $ Syntax_Phases.term_of_typ ctxt T, ts)
    | typerep_tr' _ T ts = raise Match;
in [(@{const_syntax typerep}, typerep_tr')] end
*}

setup {*
let

fun add_typerep tyco thy =
  let
    val sorts = replicate (Sign.arity_number thy tyco) @{sort typerep};
    val vs = Name.invent_names Name.context "'a" sorts;
    val ty = Type (tyco, map TFree vs);
    val lhs = Const (@{const_name typerep}, Term.itselfT ty --> @{typ typerep})
      $ Free ("T", Term.itselfT ty);
    val rhs = @{term Typerep} $ HOLogic.mk_literal tyco
      $ HOLogic.mk_list @{typ typerep} (map (HOLogic.mk_typerep o TFree) vs);
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in
    thy
    |> Class.instantiation ([tyco], vs, @{sort typerep})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (Attrib.empty_binding, eq)))
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun ensure_typerep tyco thy =
  if not (can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort typerep})
    andalso can (Sorts.mg_domain (Sign.classes_of thy) tyco) @{sort type}
  then add_typerep tyco thy else thy;

in

add_typerep @{type_name fun}
#> Typedef.interpretation ensure_typerep
#> Code.datatype_interpretation (ensure_typerep o fst)
#> Code.abstype_interpretation (ensure_typerep o fst)

end
*}

lemma [code]:
  "HOL.equal (Typerep tyco1 tys1) (Typerep tyco2 tys2) \<longleftrightarrow> HOL.equal tyco1 tyco2
     \<and> list_all2 HOL.equal tys1 tys2"
  by (auto simp add: eq_equal [symmetric] list_all2_eq [symmetric])

lemma [code nbe]:
  "HOL.equal (x :: typerep) x \<longleftrightarrow> True"
  by (fact equal_refl)

code_type typerep
  (Eval "Term.typ")

code_const Typerep
  (Eval "Term.Type/ (_, _)")

code_reserved Eval Term

hide_const (open) typerep Typerep

end
