(*  Title:      FOL/FOL.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel
*)

header {* Classical first-order logic *}

theory FOL
imports IFOL
uses ("FOL_lemmas1.ML") ("cladata.ML") ("blastdata.ML") ("simpdata.ML")
      ("eqrule_FOL_data.ML")
      ("~~/src/Provers/eqsubst.ML")
begin


subsection {* The classical axiom *}

axioms
  classical: "(~P ==> P) ==> P"


subsection {* Lemmas and proof tools *}

use "FOL_lemmas1.ML"
theorems case_split = case_split_thm [case_names True False, cases type: o]

use "cladata.ML"
setup Cla.setup
setup cla_setup
setup case_setup

use "blastdata.ML"
setup Blast.setup


lemma ex1_functional: "[| EX! z. P(a,z);  P(a,b);  P(a,c) |] ==> b = c"
by blast

ML {*
val ex1_functional = thm "ex1_functional";
*}

use "simpdata.ML"
setup simpsetup
setup "Simplifier.method_setup Splitter.split_modifiers"
setup Splitter.setup
setup Clasimp.setup


subsection {* Lucas Dixon's eqstep tactic *}

use "~~/src/Provers/eqsubst.ML";
use "eqrule_FOL_data.ML";

setup EQSubstTac.setup


subsection {* Other simple lemmas *}

lemma [simp]: "((P-->R) <-> (Q-->R)) <-> ((P<->Q) | R)"
by blast

lemma [simp]: "((P-->Q) <-> (P-->R)) <-> (P --> (Q<->R))"
by blast

lemma not_disj_iff_imp: "~P | Q <-> (P-->Q)"
by blast

(** Monotonicity of implications **)

lemma conj_mono: "[| P1-->Q1; P2-->Q2 |] ==> (P1&P2) --> (Q1&Q2)"
by fast (*or (IntPr.fast_tac 1)*)

lemma disj_mono: "[| P1-->Q1; P2-->Q2 |] ==> (P1|P2) --> (Q1|Q2)"
by fast (*or (IntPr.fast_tac 1)*)

lemma imp_mono: "[| Q1-->P1; P2-->Q2 |] ==> (P1-->P2)-->(Q1-->Q2)"
by fast (*or (IntPr.fast_tac 1)*)

lemma imp_refl: "P-->P"
by (rule impI, assumption)

(*The quantifier monotonicity rules are also intuitionistically valid*)
lemma ex_mono: "(!!x. P(x) --> Q(x)) ==> (EX x. P(x)) --> (EX x. Q(x))"
by blast

lemma all_mono: "(!!x. P(x) --> Q(x)) ==> (ALL x. P(x)) --> (ALL x. Q(x))"
by blast


subsection {* Proof by cases and induction *}

text {* Proper handling of non-atomic rule statements. *}

constdefs
  induct_forall where "induct_forall(P) == \<forall>x. P(x)"
  induct_implies where "induct_implies(A, B) == A \<longrightarrow> B"
  induct_equal where "induct_equal(x, y) == x = y"
  induct_conj where "induct_conj(A, B) == A \<and> B"

lemma induct_forall_eq: "(!!x. P(x)) == Trueprop(induct_forall(\<lambda>x. P(x)))"
  by (unfold atomize_all induct_forall_def)

lemma induct_implies_eq: "(A ==> B) == Trueprop(induct_implies(A, B))"
  by (unfold atomize_imp induct_implies_def)

lemma induct_equal_eq: "(x == y) == Trueprop(induct_equal(x, y))"
  by (unfold atomize_eq induct_equal_def)

lemma induct_conj_eq:
  includes meta_conjunction_syntax
  shows "(A && B) == Trueprop(induct_conj(A, B))"
  by (unfold atomize_conj induct_conj_def)

lemmas induct_atomize_old = induct_forall_eq induct_implies_eq induct_equal_eq atomize_conj
lemmas induct_atomize = induct_forall_eq induct_implies_eq induct_equal_eq induct_conj_eq
lemmas induct_rulify [symmetric, standard] = induct_atomize
lemmas induct_rulify_fallback =
  induct_forall_def induct_implies_def induct_equal_def induct_conj_def

hide const induct_forall induct_implies induct_equal induct_conj


text {* Method setup. *}

ML {*
  structure InductMethod = InductMethodFun
  (struct
    val cases_default = thm "case_split";
    val atomize_old = thms "induct_atomize_old";
    val atomize = thms "induct_atomize";
    val rulify = thms "induct_rulify";
    val rulify_fallback = thms "induct_rulify_fallback";
  end);
*}

setup InductMethod.setup

end
