(*  Title:      FOL/FOL.thy
    Author:     Lawrence C Paulson and Markus Wenzel
*)

section \<open>Classical first-order logic\<close>

theory FOL
imports IFOL
keywords "print_claset" "print_induct_rules" :: diag
begin

ML_file "~~/src/Provers/classical.ML"
ML_file "~~/src/Provers/blast.ML"
ML_file "~~/src/Provers/clasimp.ML"


subsection \<open>The classical axiom\<close>

axiomatization where
  classical: "(\<not> P \<Longrightarrow> P) \<Longrightarrow> P"


subsection \<open>Lemmas and proof tools\<close>

lemma ccontr: "(\<not> P \<Longrightarrow> False) \<Longrightarrow> P"
  by (erule FalseE [THEN classical])


subsubsection \<open>Classical introduction rules for \<open>\<or>\<close> and \<open>\<exists>\<close>\<close>

lemma disjCI: "(\<not> Q \<Longrightarrow> P) \<Longrightarrow> P \<or> Q"
  apply (rule classical)
  apply (assumption | erule meta_mp | rule disjI1 notI)+
  apply (erule notE disjI2)+
  done

text \<open>Introduction rule involving only \<open>\<exists>\<close>\<close>
lemma ex_classical:
  assumes r: "\<not> (\<exists>x. P(x)) \<Longrightarrow> P(a)"
  shows "\<exists>x. P(x)"
  apply (rule classical)
  apply (rule exI, erule r)
  done

text \<open>Version of above, simplifying \<open>\<not>\<exists>\<close> to \<open>\<forall>\<not>\<close>.\<close>
lemma exCI:
  assumes r: "\<forall>x. \<not> P(x) \<Longrightarrow> P(a)"
  shows "\<exists>x. P(x)"
  apply (rule ex_classical)
  apply (rule notI [THEN allI, THEN r])
  apply (erule notE)
  apply (erule exI)
  done

lemma excluded_middle: "\<not> P \<or> P"
  apply (rule disjCI)
  apply assumption
  done

lemma case_split [case_names True False]:
  assumes r1: "P \<Longrightarrow> Q"
    and r2: "\<not> P \<Longrightarrow> Q"
  shows Q
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
  assumes major: "P \<longrightarrow> Q"
    and r1: "\<not> P \<Longrightarrow> R"
    and r2: "Q \<Longrightarrow> R"
  shows R
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
  assumes major: "P \<longrightarrow> Q"
    and r1: "Q \<Longrightarrow> R"
    and r2: "\<not> P \<Longrightarrow> R"
  shows R
  apply (rule excluded_middle [THEN disjE])
   apply (erule r2)
  apply (rule r1)
  apply (erule major [THEN mp])
  done

text \<open>Double negation law.\<close>
lemma notnotD: "\<not> \<not> P \<Longrightarrow> P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma contrapos2:  "\<lbrakk>Q; \<not> P \<Longrightarrow> \<not> Q\<rbrakk> \<Longrightarrow> P"
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
  assumes major: "P \<longleftrightarrow> Q"
    and r1: "\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R"
    and r2: "\<lbrakk>\<not> P; \<not> Q\<rbrakk> \<Longrightarrow> R"
  shows R
  apply (rule major [unfolded iff_def, THEN conjE])
  apply (elim impCE)
     apply (erule (1) r2)
    apply (erule (1) notE)+
  apply (erule (1) r1)
  done


(*Better for fast_tac: needs no quantifier duplication!*)
lemma alt_ex1E:
  assumes major: "\<exists>! x. P(x)"
    and r: "\<And>x. \<lbrakk>P(x);  \<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y = y'\<rbrakk> \<Longrightarrow> R"
  shows R
  using major
proof (rule ex1E)
  fix x
  assume * : "\<forall>y. P(y) \<longrightarrow> y = x"
  assume "P(x)"
  then show R
  proof (rule r)
    {
      fix y y'
      assume "P(y)" and "P(y')"
      with * have "x = y" and "x = y'"
        by - (tactic "IntPr.fast_tac @{context} 1")+
      then have "y = y'" by (rule subst)
    } note r' = this
    show "\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y = y'"
      by (intro strip, elim conjE) (rule r')
  qed
qed

lemma imp_elim: "P \<longrightarrow> Q \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"
  by (rule classical) iprover

lemma swap: "\<not> P \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> R"
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
ML \<open>val prop_cs = claset_of @{context}\<close>

(*Quantifier rules*)
lemmas [intro!] = allI ex_ex1I
  and [intro] = exI
  and [elim!] = exE alt_ex1E
  and [elim] = allE
ML \<open>val FOL_cs = claset_of @{context}\<close>

ML \<open>
  structure Blast = Blast
  (
    structure Classical = Cla
    val Trueprop_const = dest_Const @{const Trueprop}
    val equality_name = @{const_name eq}
    val not_name = @{const_name Not}
    val notE = @{thm notE}
    val ccontr = @{thm ccontr}
    val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  );
  val blast_tac = Blast.blast_tac;
\<close>


lemma ex1_functional: "\<lbrakk>\<exists>! z. P(a,z); P(a,b); P(a,c)\<rbrakk> \<Longrightarrow> b = c"
  by blast

text \<open>Elimination of \<open>True\<close> from assumptions:\<close>
lemma True_implies_equals: "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
proof
  assume "True \<Longrightarrow> PROP P"
  from this and TrueI show "PROP P" .
next
  assume "PROP P"
  then show "PROP P" .
qed

lemma uncurry: "P \<longrightarrow> Q \<longrightarrow> R \<Longrightarrow> P \<and> Q \<longrightarrow> R"
  by blast

lemma iff_allI: "(\<And>x. P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> (\<forall>x. P(x)) \<longleftrightarrow> (\<forall>x. Q(x))"
  by blast

lemma iff_exI: "(\<And>x. P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> (\<exists>x. P(x)) \<longleftrightarrow> (\<exists>x. Q(x))"
  by blast

lemma all_comm: "(\<forall>x y. P(x,y)) \<longleftrightarrow> (\<forall>y x. P(x,y))"
  by blast

lemma ex_comm: "(\<exists>x y. P(x,y)) \<longleftrightarrow> (\<exists>y x. P(x,y))"
  by blast



subsection \<open>Classical simplification rules\<close>

text \<open>
  Avoids duplication of subgoals after \<open>expand_if\<close>, when the true and
  false cases boil down to the same thing.
\<close>

lemma cases_simp: "(P \<longrightarrow> Q) \<and> (\<not> P \<longrightarrow> Q) \<longleftrightarrow> Q"
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
  "\<And>P Q. (\<exists>x. P(x) \<and> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<and> Q"
  "\<And>P Q. (\<exists>x. P \<and> Q(x)) \<longleftrightarrow> P \<and> (\<exists>x. Q(x))"
  "\<And>P Q. (\<exists>x. P(x) \<or> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<or> Q"
  "\<And>P Q. (\<exists>x. P \<or> Q(x)) \<longleftrightarrow> P \<or> (\<exists>x. Q(x))"
  by iprover+

text \<open>Classical rules.\<close>
lemma cla_ex_simps:
  "\<And>P Q. (\<exists>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<longrightarrow> Q"
  "\<And>P Q. (\<exists>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> P \<longrightarrow> (\<exists>x. Q(x))"
  by blast+

lemmas ex_simps = int_ex_simps cla_ex_simps

text \<open>Universal miniscoping.\<close>
lemma int_all_simps:
  "\<And>P Q. (\<forall>x. P(x) \<and> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<and> Q"
  "\<And>P Q. (\<forall>x. P \<and> Q(x)) \<longleftrightarrow> P \<and> (\<forall>x. Q(x))"
  "\<And>P Q. (\<forall>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<exists> x. P(x)) \<longrightarrow> Q"
  "\<And>P Q. (\<forall>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> P \<longrightarrow> (\<forall>x. Q(x))"
  by iprover+

text \<open>Classical rules.\<close>
lemma cla_all_simps:
  "\<And>P Q. (\<forall>x. P(x) \<or> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<or> Q"
  "\<And>P Q. (\<forall>x. P \<or> Q(x)) \<longleftrightarrow> P \<or> (\<forall>x. Q(x))"
  by blast+

lemmas all_simps = int_all_simps cla_all_simps


subsubsection \<open>Named rewrite rules proved for IFOL\<close>

lemma imp_disj1: "(P \<longrightarrow> Q) \<or> R \<longleftrightarrow> (P \<longrightarrow> Q \<or> R)" by blast
lemma imp_disj2: "Q \<or> (P \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> Q \<or> R)" by blast

lemma de_Morgan_conj: "(\<not> (P \<and> Q)) \<longleftrightarrow> (\<not> P \<or> \<not> Q)" by blast

lemma not_imp: "\<not> (P \<longrightarrow> Q) \<longleftrightarrow> (P \<and> \<not> Q)" by blast
lemma not_iff: "\<not> (P \<longleftrightarrow> Q) \<longleftrightarrow> (P \<longleftrightarrow> \<not> Q)" by blast

lemma not_all: "(\<not> (\<forall>x. P(x))) \<longleftrightarrow> (\<exists>x. \<not> P(x))" by blast
lemma imp_all: "((\<forall>x. P(x)) \<longrightarrow> Q) \<longleftrightarrow> (\<exists>x. P(x) \<longrightarrow> Q)" by blast


lemmas meta_simps =
  triv_forall_equality  \<comment> \<open>prunes params\<close>
  True_implies_equals  \<comment> \<open>prune asms \<open>True\<close>\<close>

lemmas IFOL_simps =
  refl [THEN P_iff_T] conj_simps disj_simps not_simps
  imp_simps iff_simps quant_simps

lemma notFalseI: "\<not> False" by iprover

lemma cla_simps_misc:
  "\<not> (P \<and> Q) \<longleftrightarrow> \<not> P \<or> \<not> Q"
  "P \<or> \<not> P"
  "\<not> P \<or> P"
  "\<not> \<not> P \<longleftrightarrow> P"
  "(\<not> P \<longrightarrow> P) \<longleftrightarrow> P"
  "(\<not> P \<longleftrightarrow> \<not> Q) \<longleftrightarrow> (P \<longleftrightarrow> Q)" by blast+

lemmas cla_simps =
  de_Morgan_conj de_Morgan_disj imp_disj1 imp_disj2
  not_imp not_all not_ex cases_simp cla_simps_misc


ML_file "simpdata.ML"

simproc_setup defined_Ex ("\<exists>x. P(x)") = \<open>fn _ => Quantifier1.rearrange_ex\<close>
simproc_setup defined_All ("\<forall>x. P(x)") = \<open>fn _ => Quantifier1.rearrange_all\<close>

ML \<open>
(*intuitionistic simprules only*)
val IFOL_ss =
  put_simpset FOL_basic_ss @{context}
  addsimps @{thms meta_simps IFOL_simps int_ex_simps int_all_simps}
  addsimprocs [@{simproc defined_All}, @{simproc defined_Ex}]
  |> Simplifier.add_cong @{thm imp_cong}
  |> simpset_of;

(*classical simprules too*)
val FOL_ss =
  put_simpset IFOL_ss @{context}
  addsimps @{thms cla_simps cla_ex_simps cla_all_simps}
  |> simpset_of;
\<close>

setup \<open>
  map_theory_simpset (put_simpset FOL_ss) #>
  Simplifier.method_setup Splitter.split_modifiers
\<close>

ML_file "~~/src/Tools/eqsubst.ML"


subsection \<open>Other simple lemmas\<close>

lemma [simp]: "((P \<longrightarrow> R) \<longleftrightarrow> (Q \<longrightarrow> R)) \<longleftrightarrow> ((P \<longleftrightarrow> Q) \<or> R)"
  by blast

lemma [simp]: "((P \<longrightarrow> Q) \<longleftrightarrow> (P \<longrightarrow> R)) \<longleftrightarrow> (P \<longrightarrow> (Q \<longleftrightarrow> R))"
  by blast

lemma not_disj_iff_imp: "\<not> P \<or> Q \<longleftrightarrow> (P \<longrightarrow> Q)"
  by blast


subsubsection \<open>Monotonicity of implications\<close>

lemma conj_mono: "\<lbrakk>P1 \<longrightarrow> Q1; P2 \<longrightarrow> Q2\<rbrakk> \<Longrightarrow> (P1 \<and> P2) \<longrightarrow> (Q1 \<and> Q2)"
  by fast (*or (IntPr.fast_tac 1)*)

lemma disj_mono: "\<lbrakk>P1 \<longrightarrow> Q1; P2 \<longrightarrow> Q2\<rbrakk> \<Longrightarrow> (P1 \<or> P2) \<longrightarrow> (Q1 \<or> Q2)"
  by fast (*or (IntPr.fast_tac 1)*)

lemma imp_mono: "\<lbrakk>Q1 \<longrightarrow> P1; P2 \<longrightarrow> Q2\<rbrakk> \<Longrightarrow> (P1 \<longrightarrow> P2) \<longrightarrow> (Q1 \<longrightarrow> Q2)"
  by fast (*or (IntPr.fast_tac 1)*)

lemma imp_refl: "P \<longrightarrow> P"
  by (rule impI)

text \<open>The quantifier monotonicity rules are also intuitionistically valid.\<close>
lemma ex_mono: "(\<And>x. P(x) \<longrightarrow> Q(x)) \<Longrightarrow> (\<exists>x. P(x)) \<longrightarrow> (\<exists>x. Q(x))"
  by blast

lemma all_mono: "(\<And>x. P(x) \<longrightarrow> Q(x)) \<Longrightarrow> (\<forall>x. P(x)) \<longrightarrow> (\<forall>x. Q(x))"
  by blast


subsection \<open>Proof by cases and induction\<close>

text \<open>Proper handling of non-atomic rule statements.\<close>

context
begin

qualified definition "induct_forall(P) \<equiv> \<forall>x. P(x)"
qualified definition "induct_implies(A, B) \<equiv> A \<longrightarrow> B"
qualified definition "induct_equal(x, y) \<equiv> x = y"
qualified definition "induct_conj(A, B) \<equiv> A \<and> B"

lemma induct_forall_eq: "(\<And>x. P(x)) \<equiv> Trueprop(induct_forall(\<lambda>x. P(x)))"
  unfolding atomize_all induct_forall_def .

lemma induct_implies_eq: "(A \<Longrightarrow> B) \<equiv> Trueprop(induct_implies(A, B))"
  unfolding atomize_imp induct_implies_def .

lemma induct_equal_eq: "(x \<equiv> y) \<equiv> Trueprop(induct_equal(x, y))"
  unfolding atomize_eq induct_equal_def .

lemma induct_conj_eq: "(A &&& B) \<equiv> Trueprop(induct_conj(A, B))"
  unfolding atomize_conj induct_conj_def .

lemmas induct_atomize = induct_forall_eq induct_implies_eq induct_equal_eq induct_conj_eq
lemmas induct_rulify [symmetric] = induct_atomize
lemmas induct_rulify_fallback =
  induct_forall_def induct_implies_def induct_equal_def induct_conj_def

text \<open>Method setup.\<close>

ML_file "~~/src/Tools/induct.ML"
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

ML_file "~~/src/Tools/case_product.ML"


hide_const (open) eq

end
