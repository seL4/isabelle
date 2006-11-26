(*  Title:      FOL/FOL.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel
*)

header {* Classical first-order logic *}

theory FOL
imports IFOL
uses ("cladata.ML") ("blastdata.ML") ("simpdata.ML")
begin


subsection {* The classical axiom *}

axioms
  classical: "(~P ==> P) ==> P"


subsection {* Lemmas and proof tools *}

lemma ccontr: "(\<not> P \<Longrightarrow> False) \<Longrightarrow> P"
  by (erule FalseE [THEN classical])

(*** Classical introduction rules for | and EX ***)

lemma disjCI: "(~Q ==> P) ==> P|Q"
  apply (rule classical)
  apply (assumption | erule meta_mp | rule disjI1 notI)+
  apply (erule notE disjI2)+
  done

(*introduction rule involving only EX*)
lemma ex_classical:
  assumes r: "~(EX x. P(x)) ==> P(a)"
  shows "EX x. P(x)"
  apply (rule classical)
  apply (rule exI, erule r)
  done

(*version of above, simplifying ~EX to ALL~ *)
lemma exCI:
  assumes r: "ALL x. ~P(x) ==> P(a)"
  shows "EX x. P(x)"
  apply (rule ex_classical)
  apply (rule notI [THEN allI, THEN r])
  apply (erule notE)
  apply (erule exI)
  done

lemma excluded_middle: "~P | P"
  apply (rule disjCI)
  apply assumption
  done

(*For disjunctive case analysis*)
ML {*
  local
    val excluded_middle = thm "excluded_middle"
    val disjE = thm "disjE"
  in
    fun excluded_middle_tac sP =
      res_inst_tac [("Q",sP)] (excluded_middle RS disjE)
  end
*}

lemma case_split_thm:
  assumes r1: "P ==> Q"
    and r2: "~P ==> Q"
  shows Q
  apply (rule excluded_middle [THEN disjE])
  apply (erule r2)
  apply (erule r1)
  done

lemmas case_split = case_split_thm [case_names True False, cases type: o]

(*HOL's more natural case analysis tactic*)
ML {*
  local
    val case_split_thm = thm "case_split_thm"
  in
    fun case_tac a = res_inst_tac [("P",a)] case_split_thm
  end
*}


(*** Special elimination rules *)


(*Classical implies (-->) elimination. *)
lemma impCE:
  assumes major: "P-->Q"
    and r1: "~P ==> R"
    and r2: "Q ==> R"
  shows R
  apply (rule excluded_middle [THEN disjE])
   apply (erule r1)
  apply (rule r2)
  apply (erule major [THEN mp])
  done

(*This version of --> elimination works on Q before P.  It works best for
  those cases in which P holds "almost everywhere".  Can't install as
  default: would break old proofs.*)
lemma impCE':
  assumes major: "P-->Q"
    and r1: "Q ==> R"
    and r2: "~P ==> R"
  shows R
  apply (rule excluded_middle [THEN disjE])
   apply (erule r2)
  apply (rule r1)
  apply (erule major [THEN mp])
  done

(*Double negation law*)
lemma notnotD: "~~P ==> P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma contrapos2:  "[| Q; ~ P ==> ~ Q |] ==> P"
  apply (rule classical)
  apply (drule (1) meta_mp)
  apply (erule (1) notE)
  done

(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in 
    ~P ==> ~Q    and    P ==> Q  *)
lemma iffCE:
  assumes major: "P<->Q"
    and r1: "[| P; Q |] ==> R"
    and r2: "[| ~P; ~Q |] ==> R"
  shows R
  apply (rule major [unfolded iff_def, THEN conjE])
  apply (elim impCE)
     apply (erule (1) r2)
    apply (erule (1) notE)+
  apply (erule (1) r1)
  done


(*Better for fast_tac: needs no quantifier duplication!*)
lemma alt_ex1E:
  assumes major: "EX! x. P(x)"
    and r: "!!x. [| P(x);  ALL y y'. P(y) & P(y') --> y=y' |] ==> R"
  shows R
  using major
proof (rule ex1E)
  fix x
  assume * : "\<forall>y. P(y) \<longrightarrow> y = x"
  assume "P(x)"
  then show R
  proof (rule r)
    { fix y y'
      assume "P(y)" and "P(y')"
      with * have "x = y" and "x = y'" by - (tactic "IntPr.fast_tac 1")+
      then have "y = y'" by (rule subst)
    } note r' = this
    show "\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y = y'" by (intro strip, elim conjE) (rule r')
  qed
qed

use "cladata.ML"
setup Cla.setup
setup cla_setup
setup case_setup

use "blastdata.ML"
setup Blast.setup


lemma ex1_functional: "[| EX! z. P(a,z);  P(a,b);  P(a,c) |] ==> b = c"
  by blast

(* Elimination of True from asumptions: *)
lemma True_implies_equals: "(True ==> PROP P) == PROP P"
proof
  assume "True \<Longrightarrow> PROP P"
  from this and TrueI show "PROP P" .
next
  assume "PROP P"
  then show "PROP P" .
qed

lemma uncurry: "P --> Q --> R ==> P & Q --> R"
  by blast

lemma iff_allI: "(!!x. P(x) <-> Q(x)) ==> (ALL x. P(x)) <-> (ALL x. Q(x))"
  by blast

lemma iff_exI: "(!!x. P(x) <-> Q(x)) ==> (EX x. P(x)) <-> (EX x. Q(x))"
  by blast

lemma all_comm: "(ALL x y. P(x,y)) <-> (ALL y x. P(x,y))" by blast

lemma ex_comm: "(EX x y. P(x,y)) <-> (EX y x. P(x,y))" by blast

use "simpdata.ML"
setup simpsetup
setup "Simplifier.method_setup Splitter.split_modifiers"
setup Splitter.setup
setup Clasimp.setup
setup EqSubst.setup


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
  unfolding atomize_all induct_forall_def .

lemma induct_implies_eq: "(A ==> B) == Trueprop(induct_implies(A, B))"
  unfolding atomize_imp induct_implies_def .

lemma induct_equal_eq: "(x == y) == Trueprop(induct_equal(x, y))"
  unfolding atomize_eq induct_equal_def .

lemma induct_conj_eq:
  includes meta_conjunction_syntax
  shows "(A && B) == Trueprop(induct_conj(A, B))"
  unfolding atomize_conj induct_conj_def .

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
    val atomize = thms "induct_atomize";
    val rulify = thms "induct_rulify";
    val rulify_fallback = thms "induct_rulify_fallback";
  end);
*}

setup InductMethod.setup

end
