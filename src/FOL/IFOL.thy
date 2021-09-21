(*  Title:      FOL/IFOL.thy
    Author:     Lawrence C Paulson and Markus Wenzel
*)

section \<open>Intuitionistic first-order logic\<close>

theory IFOL
  imports Pure
  abbrevs "?<" = "\<exists>\<^sub>\<le>\<^sub>1"
begin

ML_file \<open>~~/src/Tools/misc_legacy.ML\<close>
ML_file \<open>~~/src/Provers/splitter.ML\<close>
ML_file \<open>~~/src/Provers/hypsubst.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/zipper.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/isand.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/rw_inst.ML\<close>
ML_file \<open>~~/src/Provers/quantifier1.ML\<close>
ML_file \<open>~~/src/Tools/intuitionistic.ML\<close>
ML_file \<open>~~/src/Tools/project_rule.ML\<close>
ML_file \<open>~~/src/Tools/atomize_elim.ML\<close>


subsection \<open>Syntax and axiomatic basis\<close>

setup Pure_Thy.old_appl_syntax_setup
setup \<open>Proofterm.set_preproc (Proof_Rewrite_Rules.standard_preproc [])\<close>

class "term"
default_sort \<open>term\<close>

typedecl o

judgment
  Trueprop :: \<open>o \<Rightarrow> prop\<close>  (\<open>(_)\<close> 5)


subsubsection \<open>Equality\<close>

axiomatization
  eq :: \<open>['a, 'a] \<Rightarrow> o\<close>  (infixl \<open>=\<close> 50)
where
  refl: \<open>a = a\<close> and
  subst: \<open>a = b \<Longrightarrow> P(a) \<Longrightarrow> P(b)\<close>


subsubsection \<open>Propositional logic\<close>

axiomatization
  False :: \<open>o\<close> and
  conj :: \<open>[o, o] => o\<close>  (infixr \<open>\<and>\<close> 35) and
  disj :: \<open>[o, o] => o\<close>  (infixr \<open>\<or>\<close> 30) and
  imp :: \<open>[o, o] => o\<close>  (infixr \<open>\<longrightarrow>\<close> 25)
where
  conjI: \<open>\<lbrakk>P;  Q\<rbrakk> \<Longrightarrow> P \<and> Q\<close> and
  conjunct1: \<open>P \<and> Q \<Longrightarrow> P\<close> and
  conjunct2: \<open>P \<and> Q \<Longrightarrow> Q\<close> and

  disjI1: \<open>P \<Longrightarrow> P \<or> Q\<close> and
  disjI2: \<open>Q \<Longrightarrow> P \<or> Q\<close> and
  disjE: \<open>\<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close> and

  impI: \<open>(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q\<close> and
  mp: \<open>\<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q\<close> and

  FalseE: \<open>False \<Longrightarrow> P\<close>


subsubsection \<open>Quantifiers\<close>

axiomatization
  All :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>\<forall>\<close> 10) and
  Ex :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>\<exists>\<close> 10)
where
  allI: \<open>(\<And>x. P(x)) \<Longrightarrow> (\<forall>x. P(x))\<close> and
  spec: \<open>(\<forall>x. P(x)) \<Longrightarrow> P(x)\<close> and
  exI: \<open>P(x) \<Longrightarrow> (\<exists>x. P(x))\<close> and
  exE: \<open>\<lbrakk>\<exists>x. P(x); \<And>x. P(x) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close>


subsubsection \<open>Definitions\<close>

definition \<open>True \<equiv> False \<longrightarrow> False\<close>

definition Not (\<open>\<not> _\<close> [40] 40)
  where not_def: \<open>\<not> P \<equiv> P \<longrightarrow> False\<close>

definition iff  (infixr \<open>\<longleftrightarrow>\<close> 25)
  where \<open>P \<longleftrightarrow> Q \<equiv> (P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)\<close>

definition Uniq :: "('a \<Rightarrow> o) \<Rightarrow> o"
  where \<open>Uniq(P) \<equiv> (\<forall>x y. P(x) \<longrightarrow> P(y) \<longrightarrow> y = x)\<close>

definition Ex1 :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>\<exists>!\<close> 10)
  where ex1_def: \<open>\<exists>!x. P(x) \<equiv> \<exists>x. P(x) \<and> (\<forall>y. P(y) \<longrightarrow> y = x)\<close>

axiomatization where  \<comment> \<open>Reflection, admissible\<close>
  eq_reflection: \<open>(x = y) \<Longrightarrow> (x \<equiv> y)\<close> and
  iff_reflection: \<open>(P \<longleftrightarrow> Q) \<Longrightarrow> (P \<equiv> Q)\<close>

abbreviation not_equal :: \<open>['a, 'a] \<Rightarrow> o\<close>  (infixl \<open>\<noteq>\<close> 50)
  where \<open>x \<noteq> y \<equiv> \<not> (x = y)\<close>

syntax "_Uniq" :: "pttrn \<Rightarrow> o \<Rightarrow> o"  ("(2\<exists>\<^sub>\<le>\<^sub>1 _./ _)" [0, 10] 10)
translations "\<exists>\<^sub>\<le>\<^sub>1x. P" \<rightleftharpoons> "CONST Uniq (\<lambda>x. P)"

print_translation \<open>
 [Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>Uniq\<close> \<^syntax_const>\<open>_Uniq\<close>]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>


subsubsection \<open>Old-style ASCII syntax\<close>

notation (ASCII)
  not_equal  (infixl \<open>~=\<close> 50) and
  Not  (\<open>~ _\<close> [40] 40) and
  conj  (infixr \<open>&\<close> 35) and
  disj  (infixr \<open>|\<close> 30) and
  All  (binder \<open>ALL \<close> 10) and
  Ex  (binder \<open>EX \<close> 10) and
  Ex1  (binder \<open>EX! \<close> 10) and
  imp  (infixr \<open>-->\<close> 25) and
  iff  (infixr \<open><->\<close> 25)


subsection \<open>Lemmas and proof tools\<close>

lemmas strip = impI allI

lemma TrueI: \<open>True\<close>
  unfolding True_def by (rule impI)


subsubsection \<open>Sequent-style elimination rules for \<open>\<and>\<close> \<open>\<longrightarrow>\<close> and \<open>\<forall>\<close>\<close>

lemma conjE:
  assumes major: \<open>P \<and> Q\<close>
    and r: \<open>\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
proof (rule r)
  show "P"
    by (rule major [THEN conjunct1])
  show "Q"
    by (rule major [THEN conjunct2])
qed

lemma impE:
  assumes major: \<open>P \<longrightarrow> Q\<close>
    and \<open>P\<close>
  and r: \<open>Q \<Longrightarrow> R\<close>
  shows \<open>R\<close>
proof (rule r)
  show "Q"
    by (rule mp [OF major \<open>P\<close>])
qed

lemma allE:
  assumes major: \<open>\<forall>x. P(x)\<close>
    and r: \<open>P(x) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
proof (rule r)
  show "P(x)"
    by (rule major [THEN spec])
qed

text \<open>Duplicates the quantifier; for use with \<^ML>\<open>eresolve_tac\<close>.\<close>
lemma all_dupE:
  assumes major: \<open>\<forall>x. P(x)\<close>
    and r: \<open>\<lbrakk>P(x); \<forall>x. P(x)\<rbrakk> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
proof (rule r)
  show "P(x)"
    by (rule major [THEN spec])
qed (rule major)



subsubsection \<open>Negation rules, which translate between \<open>\<not> P\<close> and \<open>P \<longrightarrow> False\<close>\<close>

lemma notI: \<open>(P \<Longrightarrow> False) \<Longrightarrow> \<not> P\<close>
  unfolding not_def by (erule impI)

lemma notE: \<open>\<lbrakk>\<not> P; P\<rbrakk> \<Longrightarrow> R\<close>
  unfolding not_def by (erule mp [THEN FalseE])

lemma rev_notE: \<open>\<lbrakk>P; \<not> P\<rbrakk> \<Longrightarrow> R\<close>
  by (erule notE)

text \<open>This is useful with the special implication rules for each kind of \<open>P\<close>.\<close>
lemma not_to_imp:
  assumes \<open>\<not> P\<close>
    and r: \<open>P \<longrightarrow> False \<Longrightarrow> Q\<close>
  shows \<open>Q\<close>
  apply (rule r)
  apply (rule impI)
  apply (erule notE [OF \<open>\<not> P\<close>])
  done

text \<open>
  For substitution into an assumption \<open>P\<close>, reduce \<open>Q\<close> to \<open>P \<longrightarrow> Q\<close>, substitute into this implication, then apply \<open>impI\<close> to
  move \<open>P\<close> back into the assumptions.
\<close>
lemma rev_mp: \<open>\<lbrakk>P; P \<longrightarrow> Q\<rbrakk> \<Longrightarrow> Q\<close>
  by (erule mp)

text \<open>Contrapositive of an inference rule.\<close>
lemma contrapos:
  assumes major: \<open>\<not> Q\<close>
    and minor: \<open>P \<Longrightarrow> Q\<close>
  shows \<open>\<not> P\<close>
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

lemma iffI: \<open>\<lbrakk>P \<Longrightarrow> Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P \<longleftrightarrow> Q\<close>
  unfolding iff_def
  by (rule conjI; erule impI)

lemma iffE:
  assumes major: \<open>P \<longleftrightarrow> Q\<close>
    and r: \<open>\<lbrakk>P \<longrightarrow> Q; Q \<longrightarrow> P\<rbrakk> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using major
  unfolding iff_def
  apply (rule conjE)
  apply (erule r)
  apply assumption
  done


subsubsection \<open>Destruct rules for \<open>\<longleftrightarrow>\<close> similar to Modus Ponens\<close>

lemma iffD1: \<open>\<lbrakk>P \<longleftrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q\<close>
  unfolding iff_def
  apply (erule conjunct1 [THEN mp])
  apply assumption
  done

lemma iffD2: \<open>\<lbrakk>P \<longleftrightarrow> Q; Q\<rbrakk> \<Longrightarrow> P\<close>
  unfolding iff_def
  apply (erule conjunct2 [THEN mp])
  apply assumption
  done

lemma rev_iffD1: \<open>\<lbrakk>P; P \<longleftrightarrow> Q\<rbrakk> \<Longrightarrow> Q\<close>
  apply (erule iffD1)
  apply assumption
  done

lemma rev_iffD2: \<open>\<lbrakk>Q; P \<longleftrightarrow> Q\<rbrakk> \<Longrightarrow> P\<close>
  apply (erule iffD2)
  apply assumption
  done

lemma iff_refl: \<open>P \<longleftrightarrow> P\<close>
  by (rule iffI)

lemma iff_sym: \<open>Q \<longleftrightarrow> P \<Longrightarrow> P \<longleftrightarrow> Q\<close>
  apply (erule iffE)
  apply (rule iffI)
  apply (assumption | erule mp)+
  done

lemma iff_trans: \<open>\<lbrakk>P \<longleftrightarrow> Q; Q \<longleftrightarrow> R\<rbrakk> \<Longrightarrow> P \<longleftrightarrow> R\<close>
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

lemma ex1I: \<open>P(a) \<Longrightarrow> (\<And>x. P(x) \<Longrightarrow> x = a) \<Longrightarrow> \<exists>!x. P(x)\<close>
  unfolding ex1_def
  apply (assumption | rule exI conjI allI impI)+
  done

text \<open>Sometimes easier to use: the premises have no shared variables. Safe!\<close>
lemma ex_ex1I: \<open>\<exists>x. P(x) \<Longrightarrow> (\<And>x y. \<lbrakk>P(x); P(y)\<rbrakk> \<Longrightarrow> x = y) \<Longrightarrow> \<exists>!x. P(x)\<close>
  apply (erule exE)
  apply (rule ex1I)
   apply assumption
  apply assumption
  done

lemma ex1E: \<open>\<exists>! x. P(x) \<Longrightarrow> (\<And>x. \<lbrakk>P(x); \<forall>y. P(y) \<longrightarrow> y = x\<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R\<close>
  unfolding ex1_def
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
  assumes \<open>P \<longleftrightarrow> P'\<close>
    and \<open>P' \<Longrightarrow> Q \<longleftrightarrow> Q'\<close>
  shows \<open>(P \<and> Q) \<longleftrightarrow> (P' \<and> Q')\<close>
  apply (insert assms)
  apply (assumption | rule iffI conjI | erule iffE conjE mp | iff assms)+
  done

text \<open>Reversed congruence rule!  Used in ZF/Order.\<close>
lemma conj_cong2:
  assumes \<open>P \<longleftrightarrow> P'\<close>
    and \<open>P' \<Longrightarrow> Q \<longleftrightarrow> Q'\<close>
  shows \<open>(Q \<and> P) \<longleftrightarrow> (Q' \<and> P')\<close>
  apply (insert assms)
  apply (assumption | rule iffI conjI | erule iffE conjE mp | iff assms)+
  done

lemma disj_cong:
  assumes \<open>P \<longleftrightarrow> P'\<close> and \<open>Q \<longleftrightarrow> Q'\<close>
  shows \<open>(P \<or> Q) \<longleftrightarrow> (P' \<or> Q')\<close>
  apply (insert assms)
  apply (erule iffE disjE disjI1 disjI2 |
    assumption | rule iffI | erule (1) notE impE)+
  done

lemma imp_cong:
  assumes \<open>P \<longleftrightarrow> P'\<close>
    and \<open>P' \<Longrightarrow> Q \<longleftrightarrow> Q'\<close>
  shows \<open>(P \<longrightarrow> Q) \<longleftrightarrow> (P' \<longrightarrow> Q')\<close>
  apply (insert assms)
  apply (assumption | rule iffI impI | erule iffE | erule (1) notE impE | iff assms)+
  done

lemma iff_cong: \<open>\<lbrakk>P \<longleftrightarrow> P'; Q \<longleftrightarrow> Q'\<rbrakk> \<Longrightarrow> (P \<longleftrightarrow> Q) \<longleftrightarrow> (P' \<longleftrightarrow> Q')\<close>
  apply (erule iffE | assumption | rule iffI | erule (1) notE impE)+
  done

lemma not_cong: \<open>P \<longleftrightarrow> P' \<Longrightarrow> \<not> P \<longleftrightarrow> \<not> P'\<close>
  apply (assumption | rule iffI notI | erule (1) notE impE | erule iffE notE)+
  done

lemma all_cong:
  assumes \<open>\<And>x. P(x) \<longleftrightarrow> Q(x)\<close>
  shows \<open>(\<forall>x. P(x)) \<longleftrightarrow> (\<forall>x. Q(x))\<close>
  apply (assumption | rule iffI allI | erule (1) notE impE | erule allE | iff assms)+
  done

lemma ex_cong:
  assumes \<open>\<And>x. P(x) \<longleftrightarrow> Q(x)\<close>
  shows \<open>(\<exists>x. P(x)) \<longleftrightarrow> (\<exists>x. Q(x))\<close>
  apply (erule exE | assumption | rule iffI exI | erule (1) notE impE | iff assms)+
  done

lemma ex1_cong:
  assumes \<open>\<And>x. P(x) \<longleftrightarrow> Q(x)\<close>
  shows \<open>(\<exists>!x. P(x)) \<longleftrightarrow> (\<exists>!x. Q(x))\<close>
  apply (erule ex1E spec [THEN mp] | assumption | rule iffI ex1I | erule (1) notE impE | iff assms)+
  done


subsection \<open>Equality rules\<close>

lemma sym: \<open>a = b \<Longrightarrow> b = a\<close>
  apply (erule subst)
  apply (rule refl)
  done

lemma trans: \<open>\<lbrakk>a = b; b = c\<rbrakk> \<Longrightarrow> a = c\<close>
  apply (erule subst, assumption)
  done

lemma not_sym: \<open>b \<noteq> a \<Longrightarrow> a \<noteq> b\<close>
  apply (erule contrapos)
  apply (erule sym)
  done

text \<open>
  Two theorems for rewriting only one instance of a definition:
  the first for definitions of formulae and the second for terms.
\<close>

lemma def_imp_iff: \<open>(A \<equiv> B) \<Longrightarrow> A \<longleftrightarrow> B\<close>
  apply unfold
  apply (rule iff_refl)
  done

lemma meta_eq_to_obj_eq: \<open>(A \<equiv> B) \<Longrightarrow> A = B\<close>
  apply unfold
  apply (rule refl)
  done

lemma meta_eq_to_iff: \<open>x \<equiv> y \<Longrightarrow> x \<longleftrightarrow> y\<close>
  by unfold (rule iff_refl)

text \<open>Substitution.\<close>
lemma ssubst: \<open>\<lbrakk>b = a; P(a)\<rbrakk> \<Longrightarrow> P(b)\<close>
  apply (drule sym)
  apply (erule (1) subst)
  done

text \<open>A special case of \<open>ex1E\<close> that would otherwise need quantifier
  expansion.\<close>
lemma ex1_equalsE: \<open>\<lbrakk>\<exists>!x. P(x); P(a); P(b)\<rbrakk> \<Longrightarrow> a = b\<close>
  apply (erule ex1E)
  apply (rule trans)
   apply (rule_tac [2] sym)
   apply (assumption | erule spec [THEN mp])+
  done


subsection \<open>Simplifications of assumed implications\<close>

text \<open>
  Roy Dyckhoff has proved that \<open>conj_impE\<close>, \<open>disj_impE\<close>, and
  \<open>imp_impE\<close> used with \<^ML>\<open>mp_tac\<close> (restricted to atomic formulae) is
  COMPLETE for intuitionistic propositional logic.

  See R. Dyckhoff, Contraction-free sequent calculi for intuitionistic logic
  (preprint, University of St Andrews, 1991).
\<close>

lemma conj_impE:
  assumes major: \<open>(P \<and> Q) \<longrightarrow> S\<close>
    and r: \<open>P \<longrightarrow> (Q \<longrightarrow> S) \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  by (assumption | rule conjI impI major [THEN mp] r)+

lemma disj_impE:
  assumes major: \<open>(P \<or> Q) \<longrightarrow> S\<close>
    and r: \<open>\<lbrakk>P \<longrightarrow> S; Q \<longrightarrow> S\<rbrakk> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  by (assumption | rule disjI1 disjI2 impI major [THEN mp] r)+

text \<open>Simplifies the implication.  Classical version is stronger.
  Still UNSAFE since Q must be provable -- backtracking needed.\<close>
lemma imp_impE:
  assumes major: \<open>(P \<longrightarrow> Q) \<longrightarrow> S\<close>
    and r1: \<open>\<lbrakk>P; Q \<longrightarrow> S\<rbrakk> \<Longrightarrow> Q\<close>
    and r2: \<open>S \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  by (assumption | rule impI major [THEN mp] r1 r2)+

text \<open>Simplifies the implication.  Classical version is stronger.
  Still UNSAFE since ~P must be provable -- backtracking needed.\<close>
lemma not_impE: \<open>\<not> P \<longrightarrow> S \<Longrightarrow> (P \<Longrightarrow> False) \<Longrightarrow> (S \<Longrightarrow> R) \<Longrightarrow> R\<close>
  apply (drule mp)
   apply (rule notI | assumption)+
  done

text \<open>Simplifies the implication. UNSAFE.\<close>
lemma iff_impE:
  assumes major: \<open>(P \<longleftrightarrow> Q) \<longrightarrow> S\<close>
    and r1: \<open>\<lbrakk>P; Q \<longrightarrow> S\<rbrakk> \<Longrightarrow> Q\<close>
    and r2: \<open>\<lbrakk>Q; P \<longrightarrow> S\<rbrakk> \<Longrightarrow> P\<close>
    and r3: \<open>S \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  by (assumption | rule iffI impI major [THEN mp] r1 r2 r3)+

text \<open>What if \<open>(\<forall>x. \<not> \<not> P(x)) \<longrightarrow> \<not> \<not> (\<forall>x. P(x))\<close> is an assumption?
  UNSAFE.\<close>
lemma all_impE:
  assumes major: \<open>(\<forall>x. P(x)) \<longrightarrow> S\<close>
    and r1: \<open>\<And>x. P(x)\<close>
    and r2: \<open>S \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  by (rule allI impI major [THEN mp] r1 r2)+

text \<open>
  Unsafe: \<open>\<exists>x. P(x)) \<longrightarrow> S\<close> is equivalent
  to \<open>\<forall>x. P(x) \<longrightarrow> S\<close>.\<close>
lemma ex_impE:
  assumes major: \<open>(\<exists>x. P(x)) \<longrightarrow> S\<close>
    and r: \<open>P(x) \<longrightarrow> S \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  by (assumption | rule exI impI major [THEN mp] r)+

text \<open>Courtesy of Krzysztof Grabczewski.\<close>
lemma disj_imp_disj: \<open>P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> S) \<Longrightarrow> R \<or> S\<close>
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

ML_file \<open>fologic.ML\<close>

lemma thin_refl: \<open>\<lbrakk>x = x; PROP W\<rbrakk> \<Longrightarrow> PROP W\<close> .

ML \<open>
structure Hypsubst = Hypsubst
(
  val dest_eq = FOLogic.dest_eq
  val dest_Trueprop = \<^dest_judgment>
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

ML_file \<open>intprover.ML\<close>


subsection \<open>Intuitionistic Reasoning\<close>

setup \<open>Intuitionistic.method_setup \<^binding>\<open>iprover\<close>\<close>

lemma impE':
  assumes 1: \<open>P \<longrightarrow> Q\<close>
    and 2: \<open>Q \<Longrightarrow> R\<close>
    and 3: \<open>P \<longrightarrow> Q \<Longrightarrow> P\<close>
  shows \<open>R\<close>
proof -
  from 3 and 1 have \<open>P\<close> .
  with 1 have \<open>Q\<close> by (rule impE)
  with 2 show \<open>R\<close> .
qed

lemma allE':
  assumes 1: \<open>\<forall>x. P(x)\<close>
    and 2: \<open>P(x) \<Longrightarrow> \<forall>x. P(x) \<Longrightarrow> Q\<close>
  shows \<open>Q\<close>
proof -
  from 1 have \<open>P(x)\<close> by (rule spec)
  from this and 1 show \<open>Q\<close> by (rule 2)
qed

lemma notE':
  assumes 1: \<open>\<not> P\<close>
    and 2: \<open>\<not> P \<Longrightarrow> P\<close>
  shows \<open>R\<close>
proof -
  from 2 and 1 have \<open>P\<close> .
  with 1 show \<open>R\<close> by (rule notE)
qed

lemmas [Pure.elim!] = disjE iffE FalseE conjE exE
  and [Pure.intro!] = iffI conjI impI TrueI notI allI refl
  and [Pure.elim 2] = allE notE' impE'
  and [Pure.intro] = exI disjI2 disjI1

setup \<open>
  Context_Rules.addSWrapper
    (fn ctxt => fn tac => hyp_subst_tac ctxt ORELSE' tac)
\<close>


lemma iff_not_sym: \<open>\<not> (Q \<longleftrightarrow> P) \<Longrightarrow> \<not> (P \<longleftrightarrow> Q)\<close>
  by iprover

lemmas [sym] = sym iff_sym not_sym iff_not_sym
  and [Pure.elim?] = iffD1 iffD2 impE


lemma eq_commute: \<open>a = b \<longleftrightarrow> b = a\<close>
  by iprover


subsection \<open>Polymorphic congruence rules\<close>

lemma subst_context: \<open>a = b \<Longrightarrow> t(a) = t(b)\<close>
  by iprover

lemma subst_context2: \<open>\<lbrakk>a = b; c = d\<rbrakk> \<Longrightarrow> t(a,c) = t(b,d)\<close>
  by iprover

lemma subst_context3: \<open>\<lbrakk>a = b; c = d; e = f\<rbrakk> \<Longrightarrow> t(a,c,e) = t(b,d,f)\<close>
  by iprover

text \<open>
  Useful with \<^ML>\<open>eresolve_tac\<close> for proving equalities from known
  equalities.

        a = b
        |   |
        c = d
\<close>
lemma box_equals: \<open>\<lbrakk>a = b; a = c; b = d\<rbrakk> \<Longrightarrow> c = d\<close>
  by iprover

text \<open>Dual of \<open>box_equals\<close>: for proving equalities backwards.\<close>
lemma simp_equals: \<open>\<lbrakk>a = c; b = d; c = d\<rbrakk> \<Longrightarrow> a = b\<close>
  by iprover


subsubsection \<open>Congruence rules for predicate letters\<close>

lemma pred1_cong: \<open>a = a' \<Longrightarrow> P(a) \<longleftrightarrow> P(a')\<close>
  by iprover

lemma pred2_cong: \<open>\<lbrakk>a = a'; b = b'\<rbrakk> \<Longrightarrow> P(a,b) \<longleftrightarrow> P(a',b')\<close>
  by iprover

lemma pred3_cong: \<open>\<lbrakk>a = a'; b = b'; c = c'\<rbrakk> \<Longrightarrow> P(a,b,c) \<longleftrightarrow> P(a',b',c')\<close>
  by iprover

text \<open>Special case for the equality predicate!\<close>
lemma eq_cong: \<open>\<lbrakk>a = a'; b = b'\<rbrakk> \<Longrightarrow> a = b \<longleftrightarrow> a' = b'\<close>
  by iprover


subsection \<open>Atomizing meta-level rules\<close>

lemma atomize_all [atomize]: \<open>(\<And>x. P(x)) \<equiv> Trueprop (\<forall>x. P(x))\<close>
proof
  assume \<open>\<And>x. P(x)\<close>
  then show \<open>\<forall>x. P(x)\<close> ..
next
  assume \<open>\<forall>x. P(x)\<close>
  then show \<open>\<And>x. P(x)\<close> ..
qed

lemma atomize_imp [atomize]: \<open>(A \<Longrightarrow> B) \<equiv> Trueprop (A \<longrightarrow> B)\<close>
proof
  assume \<open>A \<Longrightarrow> B\<close>
  then show \<open>A \<longrightarrow> B\<close> ..
next
  assume \<open>A \<longrightarrow> B\<close> and \<open>A\<close>
  then show \<open>B\<close> by (rule mp)
qed

lemma atomize_eq [atomize]: \<open>(x \<equiv> y) \<equiv> Trueprop (x = y)\<close>
proof
  assume \<open>x \<equiv> y\<close>
  show \<open>x = y\<close> unfolding \<open>x \<equiv> y\<close> by (rule refl)
next
  assume \<open>x = y\<close>
  then show \<open>x \<equiv> y\<close> by (rule eq_reflection)
qed

lemma atomize_iff [atomize]: \<open>(A \<equiv> B) \<equiv> Trueprop (A \<longleftrightarrow> B)\<close>
proof
  assume \<open>A \<equiv> B\<close>
  show \<open>A \<longleftrightarrow> B\<close> unfolding \<open>A \<equiv> B\<close> by (rule iff_refl)
next
  assume \<open>A \<longleftrightarrow> B\<close>
  then show \<open>A \<equiv> B\<close> by (rule iff_reflection)
qed

lemma atomize_conj [atomize]: \<open>(A &&& B) \<equiv> Trueprop (A \<and> B)\<close>
proof
  assume conj: \<open>A &&& B\<close>
  show \<open>A \<and> B\<close>
  proof (rule conjI)
    from conj show \<open>A\<close> by (rule conjunctionD1)
    from conj show \<open>B\<close> by (rule conjunctionD2)
  qed
next
  assume conj: \<open>A \<and> B\<close>
  show \<open>A &&& B\<close>
  proof -
    from conj show \<open>A\<close> ..
    from conj show \<open>B\<close> ..
  qed
qed

lemmas [symmetric, rulify] = atomize_all atomize_imp
  and [symmetric, defn] = atomize_all atomize_imp atomize_eq atomize_iff


subsection \<open>Atomizing elimination rules\<close>

lemma atomize_exL[atomize_elim]: \<open>(\<And>x. P(x) \<Longrightarrow> Q) \<equiv> ((\<exists>x. P(x)) \<Longrightarrow> Q)\<close>
  by rule iprover+

lemma atomize_conjL[atomize_elim]: \<open>(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (A \<and> B \<Longrightarrow> C)\<close>
  by rule iprover+

lemma atomize_disjL[atomize_elim]: \<open>((A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C) \<equiv> ((A \<or> B \<Longrightarrow> C) \<Longrightarrow> C)\<close>
  by rule iprover+

lemma atomize_elimL[atomize_elim]: \<open>(\<And>B. (A \<Longrightarrow> B) \<Longrightarrow> B) \<equiv> Trueprop(A)\<close> ..


subsection \<open>Calculational rules\<close>

lemma forw_subst: \<open>a = b \<Longrightarrow> P(b) \<Longrightarrow> P(a)\<close>
  by (rule ssubst)

lemma back_subst: \<open>P(a) \<Longrightarrow> a = b \<Longrightarrow> P(b)\<close>
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

definition Let :: \<open>['a::{}, 'a => 'b] \<Rightarrow> ('b::{})\<close>
  where \<open>Let(s, f) \<equiv> f(s)\<close>

syntax
  "_bind"       :: \<open>[pttrn, 'a] => letbind\<close>           (\<open>(2_ =/ _)\<close> 10)
  ""            :: \<open>letbind => letbinds\<close>              (\<open>_\<close>)
  "_binds"      :: \<open>[letbind, letbinds] => letbinds\<close>  (\<open>_;/ _\<close>)
  "_Let"        :: \<open>[letbinds, 'a] => 'a\<close>             (\<open>(let (_)/ in (_))\<close> 10)

translations
  "_Let(_binds(b, bs), e)"  == "_Let(b, _Let(bs, e))"
  "let x = a in e"          == "CONST Let(a, \<lambda>x. e)"

lemma LetI:
  assumes \<open>\<And>x. x = t \<Longrightarrow> P(u(x))\<close>
  shows \<open>P(let x = t in u(x))\<close>
  unfolding Let_def
  apply (rule refl [THEN assms])
  done


subsection \<open>Intuitionistic simplification rules\<close>

lemma conj_simps:
  \<open>P \<and> True \<longleftrightarrow> P\<close>
  \<open>True \<and> P \<longleftrightarrow> P\<close>
  \<open>P \<and> False \<longleftrightarrow> False\<close>
  \<open>False \<and> P \<longleftrightarrow> False\<close>
  \<open>P \<and> P \<longleftrightarrow> P\<close>
  \<open>P \<and> P \<and> Q \<longleftrightarrow> P \<and> Q\<close>
  \<open>P \<and> \<not> P \<longleftrightarrow> False\<close>
  \<open>\<not> P \<and> P \<longleftrightarrow> False\<close>
  \<open>(P \<and> Q) \<and> R \<longleftrightarrow> P \<and> (Q \<and> R)\<close>
  by iprover+

lemma disj_simps:
  \<open>P \<or> True \<longleftrightarrow> True\<close>
  \<open>True \<or> P \<longleftrightarrow> True\<close>
  \<open>P \<or> False \<longleftrightarrow> P\<close>
  \<open>False \<or> P \<longleftrightarrow> P\<close>
  \<open>P \<or> P \<longleftrightarrow> P\<close>
  \<open>P \<or> P \<or> Q \<longleftrightarrow> P \<or> Q\<close>
  \<open>(P \<or> Q) \<or> R \<longleftrightarrow> P \<or> (Q \<or> R)\<close>
  by iprover+

lemma not_simps:
  \<open>\<not> (P \<or> Q) \<longleftrightarrow> \<not> P \<and> \<not> Q\<close>
  \<open>\<not> False \<longleftrightarrow> True\<close>
  \<open>\<not> True \<longleftrightarrow> False\<close>
  by iprover+

lemma imp_simps:
  \<open>(P \<longrightarrow> False) \<longleftrightarrow> \<not> P\<close>
  \<open>(P \<longrightarrow> True) \<longleftrightarrow> True\<close>
  \<open>(False \<longrightarrow> P) \<longleftrightarrow> True\<close>
  \<open>(True \<longrightarrow> P) \<longleftrightarrow> P\<close>
  \<open>(P \<longrightarrow> P) \<longleftrightarrow> True\<close>
  \<open>(P \<longrightarrow> \<not> P) \<longleftrightarrow> \<not> P\<close>
  by iprover+

lemma iff_simps:
  \<open>(True \<longleftrightarrow> P) \<longleftrightarrow> P\<close>
  \<open>(P \<longleftrightarrow> True) \<longleftrightarrow> P\<close>
  \<open>(P \<longleftrightarrow> P) \<longleftrightarrow> True\<close>
  \<open>(False \<longleftrightarrow> P) \<longleftrightarrow> \<not> P\<close>
  \<open>(P \<longleftrightarrow> False) \<longleftrightarrow> \<not> P\<close>
  by iprover+

text \<open>The \<open>x = t\<close> versions are needed for the simplification
  procedures.\<close>
lemma quant_simps:
  \<open>\<And>P. (\<forall>x. P) \<longleftrightarrow> P\<close>
  \<open>(\<forall>x. x = t \<longrightarrow> P(x)) \<longleftrightarrow> P(t)\<close>
  \<open>(\<forall>x. t = x \<longrightarrow> P(x)) \<longleftrightarrow> P(t)\<close>
  \<open>\<And>P. (\<exists>x. P) \<longleftrightarrow> P\<close>
  \<open>\<exists>x. x = t\<close>
  \<open>\<exists>x. t = x\<close>
  \<open>(\<exists>x. x = t \<and> P(x)) \<longleftrightarrow> P(t)\<close>
  \<open>(\<exists>x. t = x \<and> P(x)) \<longleftrightarrow> P(t)\<close>
  by iprover+

text \<open>These are NOT supplied by default!\<close>
lemma distrib_simps:
  \<open>P \<and> (Q \<or> R) \<longleftrightarrow> P \<and> Q \<or> P \<and> R\<close>
  \<open>(Q \<or> R) \<and> P \<longleftrightarrow> Q \<and> P \<or> R \<and> P\<close>
  \<open>(P \<or> Q \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)\<close>
  by iprover+

lemma subst_all:
  \<open>(\<And>x. x = a \<Longrightarrow> PROP P(x)) \<equiv> PROP P(a)\<close>
  \<open>(\<And>x. a = x \<Longrightarrow> PROP P(x)) \<equiv> PROP P(a)\<close>
proof -
  show \<open>(\<And>x. x = a \<Longrightarrow> PROP P(x)) \<equiv> PROP P(a)\<close>
  proof (rule equal_intr_rule)
    assume *: \<open>\<And>x. x = a \<Longrightarrow> PROP P(x)\<close>
    show \<open>PROP P(a)\<close>
      by (rule *) (rule refl)
  next
    fix x
    assume \<open>PROP P(a)\<close> and \<open>x = a\<close>
    from \<open>x = a\<close> have \<open>x \<equiv> a\<close>
      by (rule eq_reflection)
    with \<open>PROP P(a)\<close> show \<open>PROP P(x)\<close>
      by simp
  qed
  show \<open>(\<And>x. a = x \<Longrightarrow> PROP P(x)) \<equiv> PROP P(a)\<close>
  proof (rule equal_intr_rule)
    assume *: \<open>\<And>x. a = x \<Longrightarrow> PROP P(x)\<close>
    show \<open>PROP P(a)\<close>
      by (rule *) (rule refl)
  next
    fix x
    assume \<open>PROP P(a)\<close> and \<open>a = x\<close>
    from \<open>a = x\<close> have \<open>a \<equiv> x\<close>
      by (rule eq_reflection)
    with \<open>PROP P(a)\<close> show \<open>PROP P(x)\<close>
      by simp
  qed
qed


subsubsection \<open>Conversion into rewrite rules\<close>

lemma P_iff_F: \<open>\<not> P \<Longrightarrow> (P \<longleftrightarrow> False)\<close>
  by iprover
lemma iff_reflection_F: \<open>\<not> P \<Longrightarrow> (P \<equiv> False)\<close>
  by (rule P_iff_F [THEN iff_reflection])

lemma P_iff_T: \<open>P \<Longrightarrow> (P \<longleftrightarrow> True)\<close>
  by iprover
lemma iff_reflection_T: \<open>P \<Longrightarrow> (P \<equiv> True)\<close>
  by (rule P_iff_T [THEN iff_reflection])


subsubsection \<open>More rewrite rules\<close>

lemma conj_commute: \<open>P \<and> Q \<longleftrightarrow> Q \<and> P\<close> by iprover
lemma conj_left_commute: \<open>P \<and> (Q \<and> R) \<longleftrightarrow> Q \<and> (P \<and> R)\<close> by iprover
lemmas conj_comms = conj_commute conj_left_commute

lemma disj_commute: \<open>P \<or> Q \<longleftrightarrow> Q \<or> P\<close> by iprover
lemma disj_left_commute: \<open>P \<or> (Q \<or> R) \<longleftrightarrow> Q \<or> (P \<or> R)\<close> by iprover
lemmas disj_comms = disj_commute disj_left_commute

lemma conj_disj_distribL: \<open>P \<and> (Q \<or> R) \<longleftrightarrow> (P \<and> Q \<or> P \<and> R)\<close> by iprover
lemma conj_disj_distribR: \<open>(P \<or> Q) \<and> R \<longleftrightarrow> (P \<and> R \<or> Q \<and> R)\<close> by iprover

lemma disj_conj_distribL: \<open>P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)\<close> by iprover
lemma disj_conj_distribR: \<open>(P \<and> Q) \<or> R \<longleftrightarrow> (P \<or> R) \<and> (Q \<or> R)\<close> by iprover

lemma imp_conj_distrib: \<open>(P \<longrightarrow> (Q \<and> R)) \<longleftrightarrow> (P \<longrightarrow> Q) \<and> (P \<longrightarrow> R)\<close> by iprover
lemma imp_conj: \<open>((P \<and> Q) \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> (Q \<longrightarrow> R))\<close> by iprover
lemma imp_disj: \<open>(P \<or> Q \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)\<close> by iprover

lemma de_Morgan_disj: \<open>(\<not> (P \<or> Q)) \<longleftrightarrow> (\<not> P \<and> \<not> Q)\<close> by iprover

lemma not_ex: \<open>(\<not> (\<exists>x. P(x))) \<longleftrightarrow> (\<forall>x. \<not> P(x))\<close> by iprover
lemma imp_ex: \<open>((\<exists>x. P(x)) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P(x) \<longrightarrow> Q)\<close> by iprover

lemma ex_disj_distrib: \<open>(\<exists>x. P(x) \<or> Q(x)) \<longleftrightarrow> ((\<exists>x. P(x)) \<or> (\<exists>x. Q(x)))\<close>
  by iprover

lemma all_conj_distrib: \<open>(\<forall>x. P(x) \<and> Q(x)) \<longleftrightarrow> ((\<forall>x. P(x)) \<and> (\<forall>x. Q(x)))\<close>
  by iprover

end
