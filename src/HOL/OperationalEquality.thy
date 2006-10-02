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


subsection {* code generator setup *}

subsubsection {* preprocessor *}

setup {*
let
  val class_eq = "OperationalEquality.eq";
  fun constrain_op_eq thy ts =
    let
      fun add_eq (Const ("op =", ty)) =
            fold (insert (eq_fst (op = : indexname * indexname -> bool)))
              (Term.add_tvarsT ty [])
        | add_eq _ =
            I
      val eqs = (fold o fold_aterms) add_eq ts [];
      val inst = map (fn (v_i, _) => (v_i, [class_eq])) eqs;
    in inst end;
in CodegenData.add_constrains constrain_op_eq end
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