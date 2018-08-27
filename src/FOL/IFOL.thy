(*  Title:      FOL/IFOL.thy
    Author:     Lawrence C Paulson and Markus Wenzel
*)

section \<open>Intuitionistic first-order logic\<close>

theory IFOL
imports Pure
begin

ML \<open>\<^assert> (not (can ML \<open>open RunCall\<close>))\<close>
ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Provers/splitter.ML"
ML_file "~~/src/Provers/hypsubst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Provers/quantifier1.ML"
ML_file "~~/src/Tools/intuitionistic.ML"
ML_file "~~/src/Tools/project_rule.ML"
ML_file "~~/src/Tools/atomize_elim.ML"


subsection \<open>Syntax and axiomatic basis\<close>

setup Pure_Thy.old_appl_syntax_setup

class "term"
default_sort "term"

typedecl o

judgment
  Trueprop :: "o \<Rightarrow> prop"  ("(_)" 5)


subsubsection \<open>Equality\<close>

axiomatization
  eq :: "['a, 'a] \<Rightarrow> o"  (infixl "=" 50)
where
  refl: "a = a" and
  subst: "a = b \<Longrightarrow> P(a) \<Longrightarrow> P(b)"


subsubsection \<open>Propositional logic\<close>

axiomatization
  False :: o and
  conj :: "[o, o] => o"  (infixr "\<and>" 35) and
  disj :: "[o, o] => o"  (infixr "\<or>" 30) and
  imp :: "[o, o] => o"  (infixr "\<longrightarrow>" 25)
where
  conjI: "\<lbrakk>P;  Q\<rbrakk> \<Longrightarrow> P \<and> Q" and
  conjunct1: "P \<and> Q \<Longrightarrow> P" and
  conjunct2: "P \<and> Q \<Longrightarrow> Q" and

  disjI1: "P \<Longrightarrow> P \<or> Q" and
  disjI2: "Q \<Longrightarrow> P \<or> Q" and
  disjE: "\<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and

  impI: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q" and
  mp: "\<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q" and

  FalseE: "False \<Longrightarrow> P"


subsubsection \<open>Quantifiers\<close>

axiomatization
  All :: "('a \<Rightarrow> o) \<Rightarrow> o"  (binder "\<forall>" 10) and
  Ex :: "('a \<Rightarrow> o) \<Rightarrow> o"  (binder "\<exists>" 10)
where
  allI: "(\<And>x. P(x)) \<Longrightarrow> (\<forall>x. P(x))" and
  spec: "(\<forall>x. P(x)) \<Longrightarrow> P(x)" and
  exI: "P(x) \<Longrightarrow> (\<exists>x. P(x))" and
  exE: "\<lbrakk>\<exists>x. P(x); \<And>x. P(x) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"


subsubsection \<open>Definitions\<close>

definition "True \<equiv> False \<longrightarrow> False"

definition Not ("\<not> _" [40] 40)
  where not_def: "\<not> P \<equiv> P \<longrightarrow> False"

definition iff  (infixr "\<longleftrightarrow>" 25)
  where "P \<longleftrightarrow> Q \<equiv> (P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)"

definition Ex1 :: "('a \<Rightarrow> o) \<Rightarrow> o"  (binder "\<exists>!" 10)
  where ex1_def: "\<exists>!x. P(x) \<equiv> \<exists>x. P(x) \<and> (\<forall>y. P(y) \<longrightarrow> y = x)"

axiomatization where  \<comment> \<open>Reflection, admissible\<close>
  eq_reflection: "(x = y) \<Longrightarrow> (x \<equiv> y)" and
  iff_reflection: "(P \<longleftrightarrow> Q) \<Longrightarrow> (P \<equiv> Q)"

abbreviation not_equal :: "['a, 'a] \<Rightarrow> o"  (infixl "\<noteq>" 50)
  where "x \<noteq> y \<equiv> \<not> (x = y)"


subsubsection \<open>Old-style ASCII syntax\<close>

notation (ASCII)
  not_equal  (infixl "~=" 50) and
  Not  ("~ _" [40] 40) and
  conj  (infixr "&" 35) and
  disj  (infixr "|" 30) and
  All  (binder "ALL " 10) and
  Ex  (binder "EX " 10) and
  Ex1  (binder "EX! " 10) and
  imp  (infixr "-->" 25) and
  iff  (infixr "<->" 25)


subsection \<open>Lemmas and proof tools\<close>

lemmas strip = impI allI

lemma TrueI: True
  unfolding True_def by (rule impI)


subsubsection \<open>Sequent-style elimination rules for \<open>\<and>\<close> \<open>\<longrightarrow>\<close> and \<open>\<forall>\<close>\<close>

lemma conjE:
  assumes major: "P \<and> Q"
    and r: "\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R"
  shows R
  apply (rule r)
   apply (rule major [THEN conjunct1])
  apply (rule major [THEN conjunct2])
  done

lemma impE:
  assumes major: "P \<longrightarrow> Q"
    and P
  and r: "Q \<Longrightarrow> R"
  shows R
  apply (rule r)
  apply (rule major [THEN mp])
  apply (rule \<open>P\<close>)
  done

lemma allE:
  assumes major: "\<forall>x. P(x)"
    and r: "P(x) \<Longrightarrow> R"
  shows R
  apply (rule r)
  apply (rule major [THEN spec])
  done

text \<open>Duplicates the quantifier; for use with @{ML eresolve_tac}.\<close>
lemma all_dupE:
  assumes major: "\<forall>x. P(x)"
    and r: "\<lbrakk>P(x); \<forall>x. P(x)\<rbrakk> \<Longrightarrow> R"
  shows R
  apply (rule r)
   apply (rule major [THEN spec])
  apply (rule major)
  done


subsubsection \<open>Negation rules, which translate between \<open>\<not> P\<close> and \<open>P \<longrightarrow> False\<close>\<close>

lemma notI: "(P \<Longrightarrow> False) \<Longrightarrow> \<not> P"
  unfolding not_def by (erule impI)

lemma notE: "\<lbrakk>\<not> P; P\<rbrakk> \<Longrightarrow> R"
  unfolding not_def by (erule mp [THEN FalseE])

lemma rev_notE: "\<lbrakk>P; \<not> P\<rbrakk> \<Longrightarrow> R"
  by (erule notE)

text \<open>This is useful with the special implication rules for each kind of \<open>P\<close>.\<close>
lemma not_to_imp:
  assumes "\<not> P"
    and r: "P \<longrightarrow> False \<Longrightarrow> Q"
  shows Q
  apply (rule r)
  apply (rule impI)
  apply (erule notE [OF \<open>\<not> P\<close>])
  done

text \<open>
  For substitution into an assumption \<open>P\<close>, reduce \<open>Q\<close> to \<open>P \<longrightarrow> Q\<close>, substitute into this implication, then apply \<open>impI\<close> to
  move \<open>P\<close> back into the assumptions.
\<close>
lemma rev_mp: "\<lbrakk>P; P \<longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (erule mp)

text \<open>Contrapositive of an inference rule.\<close>
lemma contrapos:
  assumes major: "\<not> Q"
    and minor: "P \<Longrightarrow> Q"
  shows "\<not> P"
  apply (rule major [THEN notE, THEN notI])
  apply (erule minor)
  done


subsubsection \<open>Modus Ponens Tactics\<close>

text \<open>
  Finds \<open>P \<longrightarrow> Q\<close> and P in the assumptions, replaces implication by
  \<open>Q\<close>.
\<close>
ML \<open>
  fun mp_tac ctxt i =
    eresolve_tac ctxt @{thms notE impE} i THEN assume_tac ctxt i;
  fun eq_mp_tac ctxt i =
    eresolve_tac ctxt @{thms notE impE} i THEN eq_assume_tac i;
\<close>


subsection \<open>If-and-only-if\<close>

lemma iffI: "\<lbrakk>P \<Longrightarrow> Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P \<longleftrightarrow> Q"
  apply (unfold iff_def)
  apply (rule conjI)
   apply (erule impI)
  apply (erule impI)
  done

lemma iffE:
  assumes major: "P \<longleftrightarrow> Q"
    and r: "P \<longrightarrow> Q \<Longrightarrow> Q \<longrightarrow> P \<Longrightarrow> R"
  shows R
  apply (insert major, unfold iff_def)
  apply (erule conjE)
  apply (erule r)
  apply assumption
  done


subsubsection \<open>Destruct rules for \<open>\<longleftrightarrow>\<close> similar to Modus Ponens\<close>

lemma iffD1: "\<lbrakk>P \<longleftrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q"
  apply (unfold iff_def)
  apply (erule conjunct1 [THEN mp])
  apply assumption
  done

lemma iffD2: "\<lbrakk>P \<longleftrightarrow> Q; Q\<rbrakk> \<Longrightarrow> P"
  apply (unfold iff_def)
  apply (erule conjunct2 [THEN mp])
  apply assumption
  done

lemma rev_iffD1: "\<lbrakk>P; P \<longleftrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  apply (erule iffD1)
  apply assumption
  done

lemma rev_iffD2: "\<lbrakk>Q; P \<longleftrightarrow> Q\<rbrakk> \<Longrightarrow> P"
  apply (erule iffD2)
  apply assumption
  done

lemma iff_refl: "P \<longleftrightarrow> P"
  by (rule iffI)

lemma iff_sym: "Q \<longleftrightarrow> P \<Longrightarrow> P \<longleftrightarrow> Q"
  apply (erule iffE)
  apply (rule iffI)
  apply (assumption | erule mp)+
  done

lemma iff_trans: "\<lbrakk>P \<longleftrightarrow> Q; Q \<longleftrightarrow> R\<rbrakk> \<Longrightarrow> P \<longleftrightarrow> R"
  apply (rule iffI)
  apply (assumption | erule iffE | erule (1) notE impE)+
  done


subsection \<open>Unique existence\<close>

text \<open>
  NOTE THAT the following 2 quantifications:

    \<^item> \<open>\<exists>!x\<close> such that [\<open>\<exists>!y\<close> such that P(x,y)]   (sequential)
    \<^item> \<open>\<exists>!x,y\<close> such that P(x,y)                   (simultaneous)

  do NOT mean the same thing. The parser treats \<open>\<exists>!x y.P(x,y)\<close> as sequential.
\<close>

lemma ex1I: "P(a) \<Longrightarrow> (\<And>x. P(x) \<Longrightarrow> x = a) \<Longrightarrow> \<exists>!x. P(x)"
  apply (unfold ex1_def)
  apply (assumption | rule exI conjI allI impI)+
  done

text \<open>Sometimes easier to use: the premises have no shared variables. Safe!\<close>
lemma ex_ex1I: "\<exists>x. P(x) \<Longrightarrow> (\<And>x y. \<lbrakk>P(x); P(y)\<rbrakk> \<Longrightarrow> x = y) \<Longrightarrow> \<exists>!x. P(x)"
  apply (erule exE)
  apply (rule ex1I)
   apply assumption
  apply assumption
  done

lemma ex1E: "\<exists>! x. P(x) \<Longrightarrow> (\<And>x. \<lbrakk>P(x); \<forall>y. P(y) \<longrightarrow> y = x\<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
  apply (unfold ex1_def)
  apply (assumption | erule exE conjE)+
  done


subsubsection \<open>\<open>\<longleftrightarrow>\<close> congruence rules for simplification\<close>

text \<open>Use \<open>iffE\<close> on a premise. For \<open>conj_cong\<close>, \<open>imp_cong\<close>, \<open>all_cong\<close>, \<open>ex_cong\<close>.\<close>
ML \<open>
  fun iff_tac ctxt prems i =
    resolve_tac ctxt (prems RL @{thms iffE}) i THEN
    REPEAT1 (eresolve_tac ctxt @{thms asm_rl mp} i);
\<close>

method_setup iff =
  \<open>Attrib.thms >>
    (fn prems => fn ctxt => SIMPLE_METHOD' (iff_tac ctxt prems))\<close>

lemma conj_cong:
  assumes "P \<longleftrightarrow> P'"
    and "P' \<Longrightarrow> Q \<longleftrightarrow> Q'"
  shows "(P \<and> Q) \<longleftrightarrow> (P' \<and> Q')"
  apply (insert assms)
  apply (assumption | rule iffI conjI | erule iffE conjE mp | iff assms)+
  done

text \<open>Reversed congruence rule!  Used in ZF/Order.\<close>
lemma conj_cong2:
  assumes "P \<longleftrightarrow> P'"
    and "P' \<Longrightarrow> Q \<longleftrightarrow> Q'"
  shows "(Q \<and> P) \<longleftrightarrow> (Q' \<and> P')"
  apply (insert assms)
  apply (assumption | rule iffI conjI | erule iffE conjE mp | iff assms)+
  done

lemma disj_cong:
  assumes "P \<longleftrightarrow> P'" and "Q \<longleftrightarrow> Q'"
  shows "(P \<or> Q) \<longleftrightarrow> (P' \<or> Q')"
  apply (insert assms)
  apply (erule iffE disjE disjI1 disjI2 |
    assumption | rule iffI | erule (1) notE impE)+
  done

lemma imp_cong:
  assumes "P \<longleftrightarrow> P'"
    and "P' \<Longrightarrow> Q \<longleftrightarrow> Q'"
  shows "(P \<longrightarrow> Q) \<longleftrightarrow> (P' \<longrightarrow> Q')"
  apply (insert assms)
  apply (assumption | rule iffI impI | erule iffE | erule (1) notE impE | iff assms)+
  done

lemma iff_cong: "\<lbrakk>P \<longleftrightarrow> P'; Q \<longleftrightarrow> Q'\<rbrakk> \<Longrightarrow> (P \<longleftrightarrow> Q) \<longleftrightarrow> (P' \<longleftrightarrow> Q')"
  apply (erule iffE | assumption | rule iffI | erule (1) notE impE)+
  done

lemma not_cong: "P \<longleftrightarrow> P' \<Longrightarrow> \<not> P \<longleftrightarrow> \<not> P'"
  apply (assumption | rule iffI notI | erule (1) notE impE | erule iffE notE)+
  done

lemma all_cong:
  assumes "\<And>x. P(x) \<longleftrightarrow> Q(x)"
  shows "(\<forall>x. P(x)) \<longleftrightarrow> (\<forall>x. Q(x))"
  apply (assumption | rule iffI allI | erule (1) notE impE | erule allE | iff assms)+
  done

lemma ex_cong:
  assumes "\<And>x. P(x) \<longleftrightarrow> Q(x)"
  shows "(\<exists>x. P(x)) \<longleftrightarrow> (\<exists>x. Q(x))"
  apply (erule exE | assumption | rule iffI exI | erule (1) notE impE | iff assms)+
  done

lemma ex1_cong:
  assumes "\<And>x. P(x) \<longleftrightarrow> Q(x)"
  shows "(\<exists>!x. P(x)) \<longleftrightarrow> (\<exists>!x. Q(x))"
  apply (erule ex1E spec [THEN mp] | assumption | rule iffI ex1I | erule (1) notE impE | iff assms)+
  done


subsection \<open>Equality rules\<close>

lemma sym: "a = b \<Longrightarrow> b = a"
  apply (erule subst)
  apply (rule refl)
  done

lemma trans: "\<lbrakk>a = b; b = c\<rbrakk> \<Longrightarrow> a = c"
  apply (erule subst, assumption)
  done

lemma not_sym: "b \<noteq> a \<Longrightarrow> a \<noteq> b"
  apply (erule contrapos)
  apply (erule sym)
  done

text \<open>
  Two theorems for rewriting only one instance of a definition:
  the first for definitions of formulae and the second for terms.
\<close>

lemma def_imp_iff: "(A \<equiv> B) \<Longrightarrow> A \<longleftrightarrow> B"
  apply unfold
  apply (rule iff_refl)
  done

lemma meta_eq_to_obj_eq: "(A \<equiv> B) \<Longrightarrow> A = B"
  apply unfold
  apply (rule refl)
  done

lemma meta_eq_to_iff: "x \<equiv> y \<Longrightarrow> x \<longleftrightarrow> y"
  by unfold (rule iff_refl)

text \<open>Substitution.\<close>
lemma ssubst: "\<lbrakk>b = a; P(a)\<rbrakk> \<Longrightarrow> P(b)"
  apply (drule sym)
  apply (erule (1) subst)
  done

text \<open>A special case of \<open>ex1E\<close> that would otherwise need quantifier
  expansion.\<close>
lemma ex1_equalsE: "\<lbrakk>\<exists>!x. P(x); P(a); P(b)\<rbrakk> \<Longrightarrow> a = b"
  apply (erule ex1E)
  apply (rule trans)
   apply (rule_tac [2] sym)
   apply (assumption | erule spec [THEN mp])+
  done


subsubsection \<open>Polymorphic congruence rules\<close>

lemma subst_context: "a = b \<Longrightarrow> t(a) = t(b)"
  apply (erule ssubst)
  apply (rule refl)
  done

lemma subst_context2: "\<lbrakk>a = b; c = d\<rbrakk> \<Longrightarrow> t(a,c) = t(b,d)"
  apply (erule ssubst)+
  apply (rule refl)
  done

lemma subst_context3: "\<lbrakk>a = b; c = d; e = f\<rbrakk> \<Longrightarrow> t(a,c,e) = t(b,d,f)"
  apply (erule ssubst)+
  apply (rule refl)
  done

text \<open>
  Useful with @{ML eresolve_tac} for proving equalities from known
  equalities.

        a = b
        |   |
        c = d
\<close>
lemma box_equals: "\<lbrakk>a = b; a = c; b = d\<rbrakk> \<Longrightarrow> c = d"
  apply (rule trans)
   apply (rule trans)
    apply (rule sym)
    apply assumption+
  done

text \<open>Dual of \<open>box_equals\<close>: for proving equalities backwards.\<close>
lemma simp_equals: "\<lbrakk>a = c; b = d; c = d\<rbrakk> \<Longrightarrow> a = b"
  apply (rule trans)
   apply (rule trans)
    apply assumption+
  apply (erule sym)
  done


subsubsection \<open>Congruence rules for predicate letters\<close>

lemma pred1_cong: "a = a' \<Longrightarrow> P(a) \<longleftrightarrow> P(a')"
  apply (rule iffI)
   apply (erule (1) subst)
  apply (erule (1) ssubst)
  done

lemma pred2_cong: "\<lbrakk>a = a'; b = b'\<rbrakk> \<Longrightarrow> P(a,b) \<longleftrightarrow> P(a',b')"
  apply (rule iffI)
   apply (erule subst)+
   apply assumption
  apply (erule ssubst)+
  apply assumption
  done

lemma pred3_cong: "\<lbrakk>a = a'; b = b'; c = c'\<rbrakk> \<Longrightarrow> P(a,b,c) \<longleftrightarrow> P(a',b',c')"
  apply (rule iffI)
   apply (erule subst)+
   apply assumption
  apply (erule ssubst)+
  apply assumption
  done

text \<open>Special case for the equality predicate!\<close>
lemma eq_cong: "\<lbrakk>a = a'; b = b'\<rbrakk> \<Longrightarrow> a = b \<longleftrightarrow> a' = b'"
  apply (erule (1) pred2_cong)
  done


subsection \<open>Simplifications of assumed implications\<close>

text \<open>
  Roy Dyckhoff has proved that \<open>conj_impE\<close>, \<open>disj_impE\<close>, and
  \<open>imp_impE\<close> used with @{ML mp_tac} (restricted to atomic formulae) is
  COMPLETE for intuitionistic propositional logic.

  See R. Dyckhoff, Contraction-free sequent calculi for intuitionistic logic
  (preprint, University of St Andrews, 1991).
\<close>

lemma conj_impE:
  assumes major: "(P \<and> Q) \<longrightarrow> S"
    and r: "P \<longrightarrow> (Q \<longrightarrow> S) \<Longrightarrow> R"
  shows R
  by (assumption | rule conjI impI major [THEN mp] r)+

lemma disj_impE:
  assumes major: "(P \<or> Q) \<longrightarrow> S"
    and r: "\<lbrakk>P \<longrightarrow> S; Q \<longrightarrow> S\<rbrakk> \<Longrightarrow> R"
  shows R
  by (assumption | rule disjI1 disjI2 impI major [THEN mp] r)+

text \<open>Simplifies the implication.  Classical version is stronger.
  Still UNSAFE since Q must be provable -- backtracking needed.\<close>
lemma imp_impE:
  assumes major: "(P \<longrightarrow> Q) \<longrightarrow> S"
    and r1: "\<lbrakk>P; Q \<longrightarrow> S\<rbrakk> \<Longrightarrow> Q"
    and r2: "S \<Longrightarrow> R"
  shows R
  by (assumption | rule impI major [THEN mp] r1 r2)+

text \<open>Simplifies the implication.  Classical version is stronger.
  Still UNSAFE since ~P must be provable -- backtracking needed.\<close>
lemma not_impE: "\<not> P \<longrightarrow> S \<Longrightarrow> (P \<Longrightarrow> False) \<Longrightarrow> (S \<Longrightarrow> R) \<Longrightarrow> R"
  apply (drule mp)
   apply (rule notI)
   apply assumption
  apply assumption
  done

text \<open>Simplifies the implication. UNSAFE.\<close>
lemma iff_impE:
  assumes major: "(P \<longleftrightarrow> Q) \<longrightarrow> S"
    and r1: "\<lbrakk>P; Q \<longrightarrow> S\<rbrakk> \<Longrightarrow> Q"
    and r2: "\<lbrakk>Q; P \<longrightarrow> S\<rbrakk> \<Longrightarrow> P"
    and r3: "S \<Longrightarrow> R"
  shows R
  apply (assumption | rule iffI impI major [THEN mp] r1 r2 r3)+
  done

text \<open>What if \<open>(\<forall>x. \<not> \<not> P(x)) \<longrightarrow> \<not> \<not> (\<forall>x. P(x))\<close> is an assumption?
  UNSAFE.\<close>
lemma all_impE:
  assumes major: "(\<forall>x. P(x)) \<longrightarrow> S"
    and r1: "\<And>x. P(x)"
    and r2: "S \<Longrightarrow> R"
  shows R
  apply (rule allI impI major [THEN mp] r1 r2)+
  done

text \<open>
  Unsafe: \<open>\<exists>x. P(x)) \<longrightarrow> S\<close> is equivalent
  to \<open>\<forall>x. P(x) \<longrightarrow> S\<close>.\<close>
lemma ex_impE:
  assumes major: "(\<exists>x. P(x)) \<longrightarrow> S"
    and r: "P(x) \<longrightarrow> S \<Longrightarrow> R"
  shows R
  apply (assumption | rule exI impI major [THEN mp] r)+
  done

text \<open>Courtesy of Krzysztof Grabczewski.\<close>
lemma disj_imp_disj: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> S) \<Longrightarrow> R \<or> S"
  apply (erule disjE)
  apply (rule disjI1) apply assumption
  apply (rule disjI2) apply assumption
  done

ML \<open>
structure Project_Rule = Project_Rule
(
  val conjunct1 = @{thm conjunct1}
  val conjunct2 = @{thm conjunct2}
  val mp = @{thm mp}
)
\<close>

ML_file "fologic.ML"

lemma thin_refl: "\<lbrakk>x = x; PROP W\<rbrakk> \<Longrightarrow> PROP W" .

ML \<open>
structure Hypsubst = Hypsubst
(
  val dest_eq = FOLogic.dest_eq
  val dest_Trueprop = FOLogic.dest_Trueprop
  val dest_imp = FOLogic.dest_imp
  val eq_reflection = @{thm eq_reflection}
  val rev_eq_reflection = @{thm meta_eq_to_obj_eq}
  val imp_intr = @{thm impI}
  val rev_mp = @{thm rev_mp}
  val subst = @{thm subst}
  val sym = @{thm sym}
  val thin_refl = @{thm thin_refl}
);
open Hypsubst;
\<close>

ML_file "intprover.ML"


subsection \<open>Intuitionistic Reasoning\<close>

setup \<open>Intuitionistic.method_setup @{binding iprover}\<close>

lemma impE':
  assumes 1: "P \<longrightarrow> Q"
    and 2: "Q \<Longrightarrow> R"
    and 3: "P \<longrightarrow> Q \<Longrightarrow> P"
  shows R
proof -
  from 3 and 1 have P .
  with 1 have Q by (rule impE)
  with 2 show R .
qed

lemma allE':
  assumes 1: "\<forall>x. P(x)"
    and 2: "P(x) \<Longrightarrow> \<forall>x. P(x) \<Longrightarrow> Q"
  shows Q
proof -
  from 1 have "P(x)" by (rule spec)
  from this and 1 show Q by (rule 2)
qed

lemma notE':
  assumes 1: "\<not> P"
    and 2: "\<not> P \<Longrightarrow> P"
  shows R
proof -
  from 2 and 1 have P .
  with 1 show R by (rule notE)
qed

lemmas [Pure.elim!] = disjE iffE FalseE conjE exE
  and [Pure.intro!] = iffI conjI impI TrueI notI allI refl
  and [Pure.elim 2] = allE notE' impE'
  and [Pure.intro] = exI disjI2 disjI1

setup \<open>
  Context_Rules.addSWrapper
    (fn ctxt => fn tac => hyp_subst_tac ctxt ORELSE' tac)
\<close>


lemma iff_not_sym: "\<not> (Q \<longleftrightarrow> P) \<Longrightarrow> \<not> (P \<longleftrightarrow> Q)"
  by iprover

lemmas [sym] = sym iff_sym not_sym iff_not_sym
  and [Pure.elim?] = iffD1 iffD2 impE


lemma eq_commute: "a = b \<longleftrightarrow> b = a"
  apply (rule iffI)
  apply (erule sym)+
  done


subsection \<open>Atomizing meta-level rules\<close>

lemma atomize_all [atomize]: "(\<And>x. P(x)) \<equiv> Trueprop (\<forall>x. P(x))"
proof
  assume "\<And>x. P(x)"
  then show "\<forall>x. P(x)" ..
next
  assume "\<forall>x. P(x)"
  then show "\<And>x. P(x)" ..
qed

lemma atomize_imp [atomize]: "(A \<Longrightarrow> B) \<equiv> Trueprop (A \<longrightarrow> B)"
proof
  assume "A \<Longrightarrow> B"
  then show "A \<longrightarrow> B" ..
next
  assume "A \<longrightarrow> B" and A
  then show B by (rule mp)
qed

lemma atomize_eq [atomize]: "(x \<equiv> y) \<equiv> Trueprop (x = y)"
proof
  assume "x \<equiv> y"
  show "x = y" unfolding \<open>x \<equiv> y\<close> by (rule refl)
next
  assume "x = y"
  then show "x \<equiv> y" by (rule eq_reflection)
qed

lemma atomize_iff [atomize]: "(A \<equiv> B) \<equiv> Trueprop (A \<longleftrightarrow> B)"
proof
  assume "A \<equiv> B"
  show "A \<longleftrightarrow> B" unfolding \<open>A \<equiv> B\<close> by (rule iff_refl)
next
  assume "A \<longleftrightarrow> B"
  then show "A \<equiv> B" by (rule iff_reflection)
qed

lemma atomize_conj [atomize]: "(A &&& B) \<equiv> Trueprop (A \<and> B)"
proof
  assume conj: "A &&& B"
  show "A \<and> B"
  proof (rule conjI)
    from conj show A by (rule conjunctionD1)
    from conj show B by (rule conjunctionD2)
  qed
next
  assume conj: "A \<and> B"
  show "A &&& B"
  proof -
    from conj show A ..
    from conj show B ..
  qed
qed

lemmas [symmetric, rulify] = atomize_all atomize_imp
  and [symmetric, defn] = atomize_all atomize_imp atomize_eq atomize_iff


subsection \<open>Atomizing elimination rules\<close>

lemma atomize_exL[atomize_elim]: "(\<And>x. P(x) \<Longrightarrow> Q) \<equiv> ((\<exists>x. P(x)) \<Longrightarrow> Q)"
  by rule iprover+

lemma atomize_conjL[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (A \<and> B \<Longrightarrow> C)"
  by rule iprover+

lemma atomize_disjL[atomize_elim]: "((A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C) \<equiv> ((A \<or> B \<Longrightarrow> C) \<Longrightarrow> C)"
  by rule iprover+

lemma atomize_elimL[atomize_elim]: "(\<And>B. (A \<Longrightarrow> B) \<Longrightarrow> B) \<equiv> Trueprop(A)" ..


subsection \<open>Calculational rules\<close>

lemma forw_subst: "a = b \<Longrightarrow> P(b) \<Longrightarrow> P(a)"
  by (rule ssubst)

lemma back_subst: "P(a) \<Longrightarrow> a = b \<Longrightarrow> P(b)"
  by (rule subst)

text \<open>
  Note that this list of rules is in reverse order of priorities.
\<close>

lemmas basic_trans_rules [trans] =
  forw_subst
  back_subst
  rev_mp
  mp
  trans


subsection \<open>``Let'' declarations\<close>

nonterminal letbinds and letbind

definition Let :: "['a::{}, 'a => 'b] \<Rightarrow> ('b::{})"
  where "Let(s, f) \<equiv> f(s)"

syntax
  "_bind"       :: "[pttrn, 'a] => letbind"           ("(2_ =/ _)" 10)
  ""            :: "letbind => letbinds"              ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"  ("_;/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"             ("(let (_)/ in (_))" 10)

translations
  "_Let(_binds(b, bs), e)"  == "_Let(b, _Let(bs, e))"
  "let x = a in e"          == "CONST Let(a, \<lambda>x. e)"

lemma LetI:
  assumes "\<And>x. x = t \<Longrightarrow> P(u(x))"
  shows "P(let x = t in u(x))"
  apply (unfold Let_def)
  apply (rule refl [THEN assms])
  done


subsection \<open>Intuitionistic simplification rules\<close>

lemma conj_simps:
  "P \<and> True \<longleftrightarrow> P"
  "True \<and> P \<longleftrightarrow> P"
  "P \<and> False \<longleftrightarrow> False"
  "False \<and> P \<longleftrightarrow> False"
  "P \<and> P \<longleftrightarrow> P"
  "P \<and> P \<and> Q \<longleftrightarrow> P \<and> Q"
  "P \<and> \<not> P \<longleftrightarrow> False"
  "\<not> P \<and> P \<longleftrightarrow> False"
  "(P \<and> Q) \<and> R \<longleftrightarrow> P \<and> (Q \<and> R)"
  by iprover+

lemma disj_simps:
  "P \<or> True \<longleftrightarrow> True"
  "True \<or> P \<longleftrightarrow> True"
  "P \<or> False \<longleftrightarrow> P"
  "False \<or> P \<longleftrightarrow> P"
  "P \<or> P \<longleftrightarrow> P"
  "P \<or> P \<or> Q \<longleftrightarrow> P \<or> Q"
  "(P \<or> Q) \<or> R \<longleftrightarrow> P \<or> (Q \<or> R)"
  by iprover+

lemma not_simps:
  "\<not> (P \<or> Q) \<longleftrightarrow> \<not> P \<and> \<not> Q"
  "\<not> False \<longleftrightarrow> True"
  "\<not> True \<longleftrightarrow> False"
  by iprover+

lemma imp_simps:
  "(P \<longrightarrow> False) \<longleftrightarrow> \<not> P"
  "(P \<longrightarrow> True) \<longleftrightarrow> True"
  "(False \<longrightarrow> P) \<longleftrightarrow> True"
  "(True \<longrightarrow> P) \<longleftrightarrow> P"
  "(P \<longrightarrow> P) \<longleftrightarrow> True"
  "(P \<longrightarrow> \<not> P) \<longleftrightarrow> \<not> P"
  by iprover+

lemma iff_simps:
  "(True \<longleftrightarrow> P) \<longleftrightarrow> P"
  "(P \<longleftrightarrow> True) \<longleftrightarrow> P"
  "(P \<longleftrightarrow> P) \<longleftrightarrow> True"
  "(False \<longleftrightarrow> P) \<longleftrightarrow> \<not> P"
  "(P \<longleftrightarrow> False) \<longleftrightarrow> \<not> P"
  by iprover+

text \<open>The \<open>x = t\<close> versions are needed for the simplification
  procedures.\<close>
lemma quant_simps:
  "\<And>P. (\<forall>x. P) \<longleftrightarrow> P"
  "(\<forall>x. x = t \<longrightarrow> P(x)) \<longleftrightarrow> P(t)"
  "(\<forall>x. t = x \<longrightarrow> P(x)) \<longleftrightarrow> P(t)"
  "\<And>P. (\<exists>x. P) \<longleftrightarrow> P"
  "\<exists>x. x = t"
  "\<exists>x. t = x"
  "(\<exists>x. x = t \<and> P(x)) \<longleftrightarrow> P(t)"
  "(\<exists>x. t = x \<and> P(x)) \<longleftrightarrow> P(t)"
  by iprover+

text \<open>These are NOT supplied by default!\<close>
lemma distrib_simps:
  "P \<and> (Q \<or> R) \<longleftrightarrow> P \<and> Q \<or> P \<and> R"
  "(Q \<or> R) \<and> P \<longleftrightarrow> Q \<and> P \<or> R \<and> P"
  "(P \<or> Q \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)"
  by iprover+


subsubsection \<open>Conversion into rewrite rules\<close>

lemma P_iff_F: "\<not> P \<Longrightarrow> (P \<longleftrightarrow> False)"
  by iprover
lemma iff_reflection_F: "\<not> P \<Longrightarrow> (P \<equiv> False)"
  by (rule P_iff_F [THEN iff_reflection])

lemma P_iff_T: "P \<Longrightarrow> (P \<longleftrightarrow> True)"
  by iprover
lemma iff_reflection_T: "P \<Longrightarrow> (P \<equiv> True)"
  by (rule P_iff_T [THEN iff_reflection])


subsubsection \<open>More rewrite rules\<close>

lemma conj_commute: "P \<and> Q \<longleftrightarrow> Q \<and> P" by iprover
lemma conj_left_commute: "P \<and> (Q \<and> R) \<longleftrightarrow> Q \<and> (P \<and> R)" by iprover
lemmas conj_comms = conj_commute conj_left_commute

lemma disj_commute: "P \<or> Q \<longleftrightarrow> Q \<or> P" by iprover
lemma disj_left_commute: "P \<or> (Q \<or> R) \<longleftrightarrow> Q \<or> (P \<or> R)" by iprover
lemmas disj_comms = disj_commute disj_left_commute

lemma conj_disj_distribL: "P \<and> (Q \<or> R) \<longleftrightarrow> (P \<and> Q \<or> P \<and> R)" by iprover
lemma conj_disj_distribR: "(P \<or> Q) \<and> R \<longleftrightarrow> (P \<and> R \<or> Q \<and> R)" by iprover

lemma disj_conj_distribL: "P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)" by iprover
lemma disj_conj_distribR: "(P \<and> Q) \<or> R \<longleftrightarrow> (P \<or> R) \<and> (Q \<or> R)" by iprover

lemma imp_conj_distrib: "(P \<longrightarrow> (Q \<and> R)) \<longleftrightarrow> (P \<longrightarrow> Q) \<and> (P \<longrightarrow> R)" by iprover
lemma imp_conj: "((P \<and> Q) \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> (Q \<longrightarrow> R))" by iprover
lemma imp_disj: "(P \<or> Q \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)" by iprover

lemma de_Morgan_disj: "(\<not> (P \<or> Q)) \<longleftrightarrow> (\<not> P \<and> \<not> Q)" by iprover

lemma not_ex: "(\<not> (\<exists>x. P(x))) \<longleftrightarrow> (\<forall>x. \<not> P(x))" by iprover
lemma imp_ex: "((\<exists>x. P(x)) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P(x) \<longrightarrow> Q)" by iprover

lemma ex_disj_distrib: "(\<exists>x. P(x) \<or> Q(x)) \<longleftrightarrow> ((\<exists>x. P(x)) \<or> (\<exists>x. Q(x)))"
  by iprover

lemma all_conj_distrib: "(\<forall>x. P(x) \<and> Q(x)) \<longleftrightarrow> ((\<forall>x. P(x)) \<and> (\<forall>x. Q(x)))"
  by iprover

end
