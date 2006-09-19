(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Operational equality for code generation *}

theory OperationalEquality
imports HOL
begin

section {* Operational equality for code generation *}

subsection {* eq class *}

class eq =
  fixes eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

defs
  eq_def: "eq x y \<equiv> (x = y)"

ML {*
local
  val thy = the_context ();
  val const_eq = Sign.intern_const thy "eq";
  val type_bool = Type (Sign.intern_type thy "bool", []);
in
  val eq_def_sym = Thm.symmetric (thm "eq_def");
  val class_eq = Sign.intern_class thy "eq";
end
*}


subsection {* bool type *}

instance bool :: eq ..

lemma [code func]:
  "eq True p = p" unfolding eq_def by auto

lemma [code func]:
  "eq False p = (\<not> p)" unfolding eq_def by auto

lemma [code func]:
  "eq p True = p" unfolding eq_def by auto

lemma [code func]:
  "eq p False = (\<not> p)" unfolding eq_def by auto


subsection {* preprocessor *}

ML {*
fun constrain_op_eq thy thms =
  let
    fun add_eq (Const ("op =", ty)) =
          fold (insert (eq_fst (op = : indexname * indexname -> bool)))
            (Term.add_tvarsT ty [])
      | add_eq _ =
          I
    val eqs = fold (fold_aterms add_eq o Thm.prop_of) thms [];
    val instT = map (fn (v_i, sort) =>
      (Thm.ctyp_of thy (TVar (v_i, sort)),
         Thm.ctyp_of thy (TVar (v_i, Sorts.inter_sort (Sign.classes_of thy) (sort, [class_eq]))))) eqs;
  in
    thms
    |> map (Thm.instantiate (instT, []))
  end;
*}


subsection {* codegenerator setup *}

setup {*
  CodegenData.add_preproc constrain_op_eq
*}

declare eq_def [symmetric, code inline]

code_constname
  "eq \<Colon> bool \<Rightarrow> bool \<Rightarrow> bool" "HOL.eq_bool"


subsection {* haskell setup *}

code_class eq
  (Haskell "Eq" where eq \<equiv> "(==)")

code_const eq
  (Haskell infixl 4 "==")

code_instance bool :: eq
  (Haskell -)

code_const "eq \<Colon> bool \<Rightarrow> bool \<Rightarrow> bool"
  (Haskell infixl 4 "==")


subsection {* nbe setup *}

lemma eq_refl: "eq x x"
  unfolding eq_def ..

setup {*
let

val eq_refl = thm "eq_refl";

fun Trueprop_conv conv ct = (case term_of ct of
    Const ("Trueprop", _) $ _ =>
      let val (ct1, ct2) = Thm.dest_comb ct
      in Thm.combination (Thm.reflexive ct1) (conv ct2) end
  | _ => raise TERM ("Trueprop_conv", []));

fun normalization_tac i = Tactical.PRIMITIVE (Drule.fconv_rule
  (Drule.goals_conv (equal i) (Trueprop_conv NBE.normalization_conv)));

val normalization_meth =
  Method.no_args (Method.METHOD (fn _ => normalization_tac 1 THEN resolve_tac [TrueI, refl, eq_refl] 1));

in

Method.add_method ("normalization", normalization_meth, "solve goal by normalization")

end;
*}


hide (open) const eq

end