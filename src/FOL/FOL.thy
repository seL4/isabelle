(*  Title:      FOL/FOL.thy
    Author:     Lawrence C Paulson and Markus Wenzel
*)

section \<open>Classical first-order logic\<close>

theory FOL
  imports IFOL
  keywords "print_claset" "print_induct_rules" :: diag
begin

ML_file \<open>~~/src/Provers/classical.ML\<close>
ML_file \<open>~~/src/Provers/blast.ML\<close>
ML_file \<open>~~/src/Provers/clasimp.ML\<close>


subsection \<open>The classical axiom\<close>

axiomatization where
  classical: \<open>(\<not> P \<Longrightarrow> P) \<Longrightarrow> P\<close>


subsection \<open>Lemmas and proof tools\<close>

lemma ccontr: \<open>(\<not> P \<Longrightarrow> False) \<Longrightarrow> P\<close>
  by (erule FalseE [THEN classical])


subsubsection \<open>Classical introduction rules for \<open>\<or>\<close> and \<open>\<exists>\<close>\<close>

lemma disjCI: \<open>(\<not> Q \<Longrightarrow> P) \<Longrightarrow> P \<or> Q\<close>
  apply (rule classical)
  apply (assumption | erule meta_mp | rule disjI1 notI)+
  apply (erule notE disjI2)+
  done

text \<open>Introduction rule involving only \<open>\<exists>\<close>\<close>
lemma ex_classical:
  assumes r: \<open>\<not> (\<exists>x. P(x)) \<Longrightarrow> P(a)\<close>
  shows \<open>\<exists>x. P(x)\<close>
  apply (rule classical)
  apply (rule exI, erule r)
  done

text \<open>Version of above, simplifying \<open>\<not>\<exists>\<close> to \<open>\<forall>\<not>\<close>.\<close>
lemma exCI:
  assumes r: \<open>\<forall>x. \<not> P(x) \<Longrightarrow> P(a)\<close>
  shows \<open>\<exists>x. P(x)\<close>
  apply (rule ex_classical)
  apply (rule notI [THEN allI, THEN r])
  apply (erule notE)
  apply (erule exI)
  done

lemma excluded_middle: \<open>\<not> P \<or> P\<close>
  apply (rule disjCI)
  apply assumption
  done

lemma case_split [case_names True False]:
  assumes r1: \<open>P \<Longrightarrow> Q\<close>
    and r2: \<open>\<not> P \<Longrightarrow> Q\<close>
  shows \<open>Q\<close>
  apply (rule excluded_middle [THEN disjE])
  apply (erule r2)
  apply (erule r1)
  done

ML \<open>
  fun case_tac ctxt a fixes =
    Rule_Insts.res_inst_tac ctxt [((("P", 0), Position.none), a)] fixes @{thm case_split};
\<close>

method_setup case_tac = \<open>
  Args.goal_spec -- Scan.lift (Args.embedded_inner_syntax -- Parse.for_fixes) >>
    (fn (quant, (s, fixes)) => fn ctxt => SIMPLE_METHOD'' quant (case_tac ctxt s fixes))
\<close> "case_tac emulation (dynamic instantiation!)"


subsection \<open>Special elimination rules\<close>

text \<open>Classical implies (\<open>\<longrightarrow>\<close>) elimination.\<close>
lemma impCE:
  assumes major: \<open>P \<longrightarrow> Q\<close>
    and r1: \<open>\<not> P \<Longrightarrow> R\<close>
    and r2: \<open>Q \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  apply (rule excluded_middle [THEN disjE])
   apply (erule r1)
  apply (rule r2)
  apply (erule major [THEN mp])
  done

text \<open>
  This version of \<open>\<longrightarrow>\<close> elimination works on \<open>Q\<close> before \<open>P\<close>. It works best for those cases in which P holds ``almost everywhere''.
  Can't install as default: would break old proofs.
\<close>
lemma impCE':
  assumes major: \<open>P \<longrightarrow> Q\<close>
    and r1: \<open>Q \<Longrightarrow> R\<close>
    and r2: \<open>\<not> P \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  apply (rule excluded_middle [THEN disjE])
   apply (erule r2)
  apply (rule r1)
  apply (erule major [THEN mp])
  done

text \<open>Double negation law.\<close>
lemma notnotD: \<open>\<not> \<not> P \<Longrightarrow> P\<close>
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma contrapos2:  \<open>\<lbrakk>Q; \<not> P \<Longrightarrow> \<not> Q\<rbrakk> \<Longrightarrow> P\<close>
  apply (rule classical)
  apply (drule (1) meta_mp)
  apply (erule (1) notE)
  done


subsubsection \<open>Tactics for implication and contradiction\<close>

text \<open>
  Classical \<open>\<longleftrightarrow>\<close> elimination. Proof substitutes \<open>P = Q\<close> in
  \<open>\<not> P \<Longrightarrow> \<not> Q\<close> and \<open>P \<Longrightarrow> Q\<close>.
\<close>
lemma iffCE:
  assumes major: \<open>P \<longleftrightarrow> Q\<close>
    and r1: \<open>\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<close>
    and r2: \<open>\<lbrakk>\<not> P; \<not> Q\<rbrakk> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  apply (rule major [unfolded iff_def, THEN conjE])
  apply (elim impCE)
     apply (erule (1) r2)
    apply (erule (1) notE)+
  apply (erule (1) r1)
  done


(*Better for fast_tac: needs no quantifier duplication!*)
lemma alt_ex1E:
  assumes major: \<open>\<exists>! x. P(x)\<close>
    and r: \<open>\<And>x. \<lbrakk>P(x);  \<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y = y'\<rbrakk> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using major
proof (rule ex1E)
  fix x
  assume * : \<open>\<forall>y. P(y) \<longrightarrow> y = x\<close>
  assume \<open>P(x)\<close>
  then show \<open>R\<close>
  proof (rule r)
    {
      fix y y'
      assume \<open>P(y)\<close> and \<open>P(y')\<close>
      with * have \<open>x = y\<close> and \<open>x = y'\<close>
        by - (tactic "IntPr.fast_tac \<^context> 1")+
      then have \<open>y = y'\<close> by (rule subst)
    } note r' = this
    show \<open>\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y = y'\<close>
      by (intro strip, elim conjE) (rule r')
  qed
qed

lemma imp_elim: \<open>P \<longrightarrow> Q \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R\<close>
  by (rule classical) iprover

lemma swap: \<open>\<not> P \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> R\<close>
  by (rule classical) iprover


section \<open>Classical Reasoner\<close>

ML \<open>
structure Cla = Classical
(
  val imp_elim = @{thm imp_elim}
  val not_elim = @{thm notE}
  val swap = @{thm swap}
  val classical = @{thm classical}
  val sizef = size_of_thm
  val hyp_subst_tacs = [hyp_subst_tac]
);

structure Basic_Classical: BASIC_CLASSICAL = Cla;
open Basic_Classical;
\<close>

(*Propositional rules*)
lemmas [intro!] = refl TrueI conjI disjCI impI notI iffI
  and [elim!] = conjE disjE impCE FalseE iffCE
ML \<open>val prop_cs = claset_of \<^context>\<close>

(*Quantifier rules*)
lemmas [intro!] = allI ex_ex1I
  and [intro] = exI
  and [elim!] = exE alt_ex1E
  and [elim] = allE
ML \<open>val FOL_cs = claset_of \<^context>\<close>

ML \<open>
  structure Blast = Blast
  (
    structure Classical = Cla
    val Trueprop_const = dest_Const \<^Const>\<open>Trueprop\<close>
    val equality_name = \<^const_name>\<open>eq\<close>
    val not_name = \<^const_name>\<open>Not\<close>
    val notE = @{thm notE}
    val ccontr = @{thm ccontr}
    val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  );
  val blast_tac = Blast.blast_tac;
\<close>


lemma ex1_functional: \<open>\<lbrakk>\<exists>! z. P(a,z); P(a,b); P(a,c)\<rbrakk> \<Longrightarrow> b = c\<close>
  by blast

text \<open>Elimination of \<open>True\<close> from assumptions:\<close>
lemma True_implies_equals: \<open>(True \<Longrightarrow> PROP P) \<equiv> PROP P\<close>
proof
  assume \<open>True \<Longrightarrow> PROP P\<close>
  from this and TrueI show \<open>PROP P\<close> .
next
  assume \<open>PROP P\<close>
  then show \<open>PROP P\<close> .
qed

lemma uncurry: \<open>P \<longrightarrow> Q \<longrightarrow> R \<Longrightarrow> P \<and> Q \<longrightarrow> R\<close>
  by blast

lemma iff_allI: \<open>(\<And>x. P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> (\<forall>x. P(x)) \<longleftrightarrow> (\<forall>x. Q(x))\<close>
  by blast

lemma iff_exI: \<open>(\<And>x. P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> (\<exists>x. P(x)) \<longleftrightarrow> (\<exists>x. Q(x))\<close>
  by blast

lemma all_comm: \<open>(\<forall>x y. P(x,y)) \<longleftrightarrow> (\<forall>y x. P(x,y))\<close>
  by blast

lemma ex_comm: \<open>(\<exists>x y. P(x,y)) \<longleftrightarrow> (\<exists>y x. P(x,y))\<close>
  by blast



subsection \<open>Classical simplification rules\<close>

text \<open>
  Avoids duplication of subgoals after \<open>expand_if\<close>, when the true and
  false cases boil down to the same thing.
\<close>

lemma cases_simp: \<open>(P \<longrightarrow> Q) \<and> (\<not> P \<longrightarrow> Q) \<longleftrightarrow> Q\<close>
  by blast


subsubsection \<open>Miniscoping: pushing quantifiers in\<close>

text \<open>
  We do NOT distribute of \<open>\<forall>\<close> over \<open>\<and>\<close>, or dually that of
  \<open>\<exists>\<close> over \<open>\<or>\<close>.

  Baaz and Leitsch, On Skolemization and Proof Complexity (1994) show that
  this step can increase proof length!
\<close>

text \<open>Existential miniscoping.\<close>
lemma int_ex_simps:
  \<open>\<And>P Q. (\<exists>x. P(x) \<and> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<and> Q\<close>
  \<open>\<And>P Q. (\<exists>x. P \<and> Q(x)) \<longleftrightarrow> P \<and> (\<exists>x. Q(x))\<close>
  \<open>\<And>P Q. (\<exists>x. P(x) \<or> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<or> Q\<close>
  \<open>\<And>P Q. (\<exists>x. P \<or> Q(x)) \<longleftrightarrow> P \<or> (\<exists>x. Q(x))\<close>
  by iprover+

text \<open>Classical rules.\<close>
lemma cla_ex_simps:
  \<open>\<And>P Q. (\<exists>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<longrightarrow> Q\<close>
  \<open>\<And>P Q. (\<exists>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> P \<longrightarrow> (\<exists>x. Q(x))\<close>
  by blast+

lemmas ex_simps = int_ex_simps cla_ex_simps

text \<open>Universal miniscoping.\<close>
lemma int_all_simps:
  \<open>\<And>P Q. (\<forall>x. P(x) \<and> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<and> Q\<close>
  \<open>\<And>P Q. (\<forall>x. P \<and> Q(x)) \<longleftrightarrow> P \<and> (\<forall>x. Q(x))\<close>
  \<open>\<And>P Q. (\<forall>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<exists> x. P(x)) \<longrightarrow> Q\<close>
  \<open>\<And>P Q. (\<forall>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> P \<longrightarrow> (\<forall>x. Q(x))\<close>
  by iprover+

text \<open>Classical rules.\<close>
lemma cla_all_simps:
  \<open>\<And>P Q. (\<forall>x. P(x) \<or> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<or> Q\<close>
  \<open>\<And>P Q. (\<forall>x. P \<or> Q(x)) \<longleftrightarrow> P \<or> (\<forall>x. Q(x))\<close>
  by blast+

lemmas all_simps = int_all_simps cla_all_simps


subsubsection \<open>Named rewrite rules proved for IFOL\<close>

lemma imp_disj1: \<open>(P \<longrightarrow> Q) \<or> R \<longleftrightarrow> (P \<longrightarrow> Q \<or> R)\<close> by blast
lemma imp_disj2: \<open>Q \<or> (P \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> Q \<or> R)\<close> by blast

lemma de_Morgan_conj: \<open>(\<not> (P \<and> Q)) \<longleftrightarrow> (\<not> P \<or> \<not> Q)\<close> by blast

lemma not_imp: \<open>\<not> (P \<longrightarrow> Q) \<longleftrightarrow> (P \<and> \<not> Q)\<close> by blast
lemma not_iff: \<open>\<not> (P \<longleftrightarrow> Q) \<longleftrightarrow> (P \<longleftrightarrow> \<not> Q)\<close> by blast

lemma not_all: \<open>(\<not> (\<forall>x. P(x))) \<longleftrightarrow> (\<exists>x. \<not> P(x))\<close> by blast
lemma imp_all: \<open>((\<forall>x. P(x)) \<longrightarrow> Q) \<longleftrightarrow> (\<exists>x. P(x) \<longrightarrow> Q)\<close> by blast


lemmas meta_simps =
  triv_forall_equality  \<comment> \<open>prunes params\<close>
  True_implies_equals  \<comment> \<open>prune asms \<open>True\<close>\<close>

lemmas IFOL_simps =
  refl [THEN P_iff_T] conj_simps disj_simps not_simps
  imp_simps iff_simps quant_simps

lemma notFalseI: \<open>\<not> False\<close> by iprover

lemma cla_simps_misc:
  \<open>\<not> (P \<and> Q) \<longleftrightarrow> \<not> P \<or> \<not> Q\<close>
  \<open>P \<or> \<not> P\<close>
  \<open>\<not> P \<or> P\<close>
  \<open>\<not> \<not> P \<longleftrightarrow> P\<close>
  \<open>(\<not> P \<longrightarrow> P) \<longleftrightarrow> P\<close>
  \<open>(\<not> P \<longleftrightarrow> \<not> Q) \<longleftrightarrow> (P \<longleftrightarrow> Q)\<close> by blast+

lemmas cla_simps =
  de_Morgan_conj de_Morgan_disj imp_disj1 imp_disj2
  not_imp not_all not_ex cases_simp cla_simps_misc


ML_file \<open>simpdata.ML\<close>

simproc_setup defined_Ex (\<open>\<exists>x. P(x)\<close>) = \<open>K Quantifier1.rearrange_Ex\<close>
simproc_setup defined_All (\<open>\<forall>x. P(x)\<close>) = \<open>K Quantifier1.rearrange_All\<close>
simproc_setup defined_all("\<And>x. PROP P(x)") = \<open>K Quantifier1.rearrange_all\<close>

ML \<open>
(*intuitionistic simprules only*)
val IFOL_ss =
  put_simpset FOL_basic_ss \<^context>
  addsimps @{thms meta_simps IFOL_simps int_ex_simps int_all_simps subst_all}
  addsimprocs [\<^simproc>\<open>defined_All\<close>, \<^simproc>\<open>defined_Ex\<close>]
  |> Simplifier.add_cong @{thm imp_cong}
  |> simpset_of;

(*classical simprules too*)
val FOL_ss =
  put_simpset IFOL_ss \<^context>
  addsimps @{thms cla_simps cla_ex_simps cla_all_simps}
  |> simpset_of;
\<close>

setup \<open>
  map_theory_simpset (put_simpset FOL_ss) #>
  Simplifier.method_setup Splitter.split_modifiers
\<close>

ML_file \<open>~~/src/Tools/eqsubst.ML\<close>


subsection \<open>Other simple lemmas\<close>

lemma [simp]: \<open>((P \<longrightarrow> R) \<longleftrightarrow> (Q \<longrightarrow> R)) \<longleftrightarrow> ((P \<longleftrightarrow> Q) \<or> R)\<close>
  by blast

lemma [simp]: \<open>((P \<longrightarrow> Q) \<longleftrightarrow> (P \<longrightarrow> R)) \<longleftrightarrow> (P \<longrightarrow> (Q \<longleftrightarrow> R))\<close>
  by blast

lemma not_disj_iff_imp: \<open>\<not> P \<or> Q \<longleftrightarrow> (P \<longrightarrow> Q)\<close>
  by blast


subsubsection \<open>Monotonicity of implications\<close>

lemma conj_mono: \<open>\<lbrakk>P1 \<longrightarrow> Q1; P2 \<longrightarrow> Q2\<rbrakk> \<Longrightarrow> (P1 \<and> P2) \<longrightarrow> (Q1 \<and> Q2)\<close>
  by fast (*or (IntPr.fast_tac 1)*)

lemma disj_mono: \<open>\<lbrakk>P1 \<longrightarrow> Q1; P2 \<longrightarrow> Q2\<rbrakk> \<Longrightarrow> (P1 \<or> P2) \<longrightarrow> (Q1 \<or> Q2)\<close>
  by fast (*or (IntPr.fast_tac 1)*)

lemma imp_mono: \<open>\<lbrakk>Q1 \<longrightarrow> P1; P2 \<longrightarrow> Q2\<rbrakk> \<Longrightarrow> (P1 \<longrightarrow> P2) \<longrightarrow> (Q1 \<longrightarrow> Q2)\<close>
  by fast (*or (IntPr.fast_tac 1)*)

lemma imp_refl: \<open>P \<longrightarrow> P\<close>
  by (rule impI)

text \<open>The quantifier monotonicity rules are also intuitionistically valid.\<close>
lemma ex_mono: \<open>(\<And>x. P(x) \<longrightarrow> Q(x)) \<Longrightarrow> (\<exists>x. P(x)) \<longrightarrow> (\<exists>x. Q(x))\<close>
  by blast

lemma all_mono: \<open>(\<And>x. P(x) \<longrightarrow> Q(x)) \<Longrightarrow> (\<forall>x. P(x)) \<longrightarrow> (\<forall>x. Q(x))\<close>
  by blast


subsection \<open>Proof by cases and induction\<close>

text \<open>Proper handling of non-atomic rule statements.\<close>

context
begin

qualified definition \<open>induct_forall(P) \<equiv> \<forall>x. P(x)\<close>
qualified definition \<open>induct_implies(A, B) \<equiv> A \<longrightarrow> B\<close>
qualified definition \<open>induct_equal(x, y) \<equiv> x = y\<close>
qualified definition \<open>induct_conj(A, B) \<equiv> A \<and> B\<close>

lemma induct_forall_eq: \<open>(\<And>x. P(x)) \<equiv> Trueprop(induct_forall(\<lambda>x. P(x)))\<close>
  unfolding atomize_all induct_forall_def .

lemma induct_implies_eq: \<open>(A \<Longrightarrow> B) \<equiv> Trueprop(induct_implies(A, B))\<close>
  unfolding atomize_imp induct_implies_def .

lemma induct_equal_eq: \<open>(x \<equiv> y) \<equiv> Trueprop(induct_equal(x, y))\<close>
  unfolding atomize_eq induct_equal_def .

lemma induct_conj_eq: \<open>(A &&& B) \<equiv> Trueprop(induct_conj(A, B))\<close>
  unfolding atomize_conj induct_conj_def .

lemmas induct_atomize = induct_forall_eq induct_implies_eq induct_equal_eq induct_conj_eq
lemmas induct_rulify [symmetric] = induct_atomize
lemmas induct_rulify_fallback =
  induct_forall_def induct_implies_def induct_equal_def induct_conj_def

text \<open>Method setup.\<close>

ML_file \<open>~~/src/Tools/induct.ML\<close>
ML \<open>
  structure Induct = Induct
  (
    val cases_default = @{thm case_split}
    val atomize = @{thms induct_atomize}
    val rulify = @{thms induct_rulify}
    val rulify_fallback = @{thms induct_rulify_fallback}
    val equal_def = @{thm induct_equal_def}
    fun dest_def _ = NONE
    fun trivial_tac _ _ = no_tac
  );
\<close>

declare case_split [cases type: o]

end

ML_file \<open>~~/src/Tools/case_product.ML\<close>


hide_const (open) eq

end
