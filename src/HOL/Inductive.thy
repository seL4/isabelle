(*  Title:      HOL/Inductive.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Support for inductive sets and types *}

theory Inductive = Gfp + Sum_Type + Relation
files
  ("Tools/inductive_package.ML")
  ("Tools/datatype_aux.ML")
  ("Tools/datatype_prop.ML")
  ("Tools/datatype_rep_proofs.ML")
  ("Tools/datatype_abs_proofs.ML")
  ("Tools/datatype_package.ML")
  ("Tools/primrec_package.ML"):


subsection {* Proof by cases and induction *}

text {* Proper handling of non-atomic rule statements. *}

constdefs
  forall :: "('a => bool) => bool"
  "forall P == \<forall>x. P x"
  implies :: "bool => bool => bool"
  "implies A B == A --> B"
  equal :: "'a => 'a => bool"
  "equal x y == x = y"
  conj :: "bool => bool => bool"
  "conj A B == A & B"

lemma forall_eq: "(!!x. P x) == Trueprop (forall (\<lambda>x. P x))"
  by (simp only: atomize_all forall_def)

lemma implies_eq: "(A ==> B) == Trueprop (implies A B)"
  by (simp only: atomize_imp implies_def)

lemma equal_eq: "(x == y) == Trueprop (equal x y)"
  by (simp only: atomize_eq equal_def)

lemma forall_conj: "forall (\<lambda>x. conj (A x) (B x)) = conj (forall A) (forall B)"
  by (unfold forall_def conj_def) blast

lemma implies_conj: "implies C (conj A B) = conj (implies C A) (implies C B)"
  by (unfold implies_def conj_def) blast

lemma conj_curry: "(conj A B ==> C) == (A ==> B ==> C)"
  by (simp only: atomize_imp atomize_eq conj_def) (rule equal_intr_rule, blast+)

lemmas inductive_atomize = forall_eq implies_eq equal_eq
lemmas inductive_rulify1 = inductive_atomize [symmetric, standard]
lemmas inductive_rulify2 = forall_def implies_def equal_def conj_def
lemmas inductive_conj = forall_conj implies_conj conj_curry

hide const forall implies equal conj


text {* Method setup. *}

ML {*
  structure InductMethod = InductMethodFun
  (struct
    val dest_concls = HOLogic.dest_concls;
    val cases_default = thm "case_split";
    val conjI = thm "conjI";
    val atomize = thms "inductive_atomize";
    val rulify1 = thms "inductive_rulify1";
    val rulify2 = thms "inductive_rulify2";
  end);
*}

setup InductMethod.setup


subsection {* Inductive sets *}

text {* Inversion of injective functions. *}

constdefs
  myinv :: "('a => 'b) => ('b => 'a)"
  "myinv (f :: 'a => 'b) == \<lambda>y. THE x. f x = y"

lemma myinv_f_f: "inj f ==> myinv f (f x) = x"
proof -
  assume "inj f"
  hence "(THE x'. f x' = f x) = (THE x'. x' = x)"
    by (simp only: inj_eq)
  also have "... = x" by (rule the_eq_trivial)
  finally show ?thesis by (unfold myinv_def)
qed

lemma f_myinv_f: "inj f ==> y \<in> range f ==> f (myinv f y) = y"
proof (unfold myinv_def)
  assume inj: "inj f"
  assume "y \<in> range f"
  then obtain x where "y = f x" ..
  hence x: "f x = y" ..
  thus "f (THE x. f x = y) = y"
  proof (rule theI)
    fix x' assume "f x' = y"
    with x have "f x' = f x" by simp
    with inj show "x' = x" by (rule injD)
  qed
qed

hide const myinv


text {* Package setup. *}

use "Tools/inductive_package.ML"
setup InductivePackage.setup

theorems basic_monos [mono] =
  subset_refl imp_refl disj_mono conj_mono ex_mono all_mono if_def2
  Collect_mono in_mono vimage_mono
  imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
  not_all not_ex
  Ball_def Bex_def
  inductive_rulify2


subsubsection {* Inductive datatypes and primitive recursion *}

use "Tools/datatype_aux.ML"
use "Tools/datatype_prop.ML"
use "Tools/datatype_rep_proofs.ML"
use "Tools/datatype_abs_proofs.ML"
use "Tools/datatype_package.ML"
setup DatatypePackage.setup

use "Tools/primrec_package.ML"
setup PrimrecPackage.setup

end
