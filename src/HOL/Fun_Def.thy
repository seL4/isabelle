(*  Title:      HOL/Fun_Def.thy
    Author:     Alexander Krauss, TU Muenchen
*)

section \<open>Function Definitions and Termination Proofs\<close>

theory Fun_Def
  imports Basic_BNF_LFPs Partial_Function SAT
  keywords
    "function" "termination" :: thy_goal_defn and
    "fun" "fun_cases" :: thy_defn
begin

subsection \<open>Definitions with default value\<close>

definition THE_default :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a"
  where "THE_default d P = (if (\<exists>!x. P x) then (THE x. P x) else d)"

lemma THE_defaultI': "\<exists>!x. P x \<Longrightarrow> P (THE_default d P)"
  by (simp add: theI' THE_default_def)

lemma THE_default1_equality: "\<exists>!x. P x \<Longrightarrow> P a \<Longrightarrow> THE_default d P = a"
  by (simp add: the1_equality THE_default_def)

lemma THE_default_none: "\<not> (\<exists>!x. P x) \<Longrightarrow> THE_default d P = d"
  by (simp add: THE_default_def)


lemma fundef_ex1_existence:
  assumes f_def: "f \<equiv> (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  shows "G x (f x)"
  apply (simp only: f_def)
  apply (rule THE_defaultI')
  apply (rule ex1)
  done

lemma fundef_ex1_uniqueness:
  assumes f_def: "f \<equiv> (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  assumes elm: "G x (h x)"
  shows "h x = f x"
  by (auto simp add: f_def ex1 elm THE_default1_equality[symmetric])

lemma fundef_ex1_iff:
  assumes f_def: "f \<equiv> (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  shows "(G x y) = (f x = y)"
  by (auto simp add: ex1 f_def THE_default1_equality THE_defaultI')


lemma fundef_default_value:
  assumes f_def: "f \<equiv> (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes graph: "\<And>x y. G x y \<Longrightarrow> D x"
  assumes "\<not> D x"
  shows "f x = d x"
proof -
  have "\<not>(\<exists>y. G x y)"
  proof
    assume "\<exists>y. G x y"
    then have "D x" using graph ..
    with \<open>\<not> D x\<close> show False ..
  qed
  then have "\<not>(\<exists>!y. G x y)" by blast
  then show ?thesis
    unfolding f_def by (rule THE_default_none)
qed

definition in_rel_def[simp]: "in_rel R x y \<equiv> (x, y) \<in> R"

lemma wf_in_rel: "wf R \<Longrightarrow> wfp (in_rel R)"
  by (simp add: wfp_def)

ML_file \<open>Tools/Function/function_core.ML\<close>
ML_file \<open>Tools/Function/mutual.ML\<close>
ML_file \<open>Tools/Function/pattern_split.ML\<close>
ML_file \<open>Tools/Function/relation.ML\<close>
ML_file \<open>Tools/Function/function_elims.ML\<close>

method_setup relation = \<open>
  Args.term >> (fn t => fn ctxt => SIMPLE_METHOD' (Function_Relation.relation_infer_tac ctxt t))
\<close> "prove termination using a user-specified wellfounded relation"

ML_file \<open>Tools/Function/function.ML\<close>
ML_file \<open>Tools/Function/pat_completeness.ML\<close>

method_setup pat_completeness = \<open>
  Scan.succeed (SIMPLE_METHOD' o Pat_Completeness.pat_completeness_tac)
\<close> "prove completeness of (co)datatype patterns"

ML_file \<open>Tools/Function/fun.ML\<close>
ML_file \<open>Tools/Function/induction_schema.ML\<close>

method_setup induction_schema = \<open>
  Scan.succeed (CONTEXT_TACTIC oo Induction_Schema.induction_schema_tac)
\<close> "prove an induction principle"


subsection \<open>Measure functions\<close>

inductive is_measure :: "('a \<Rightarrow> nat) \<Rightarrow> bool"
  where is_measure_trivial: "is_measure f"

named_theorems measure_function "rules that guide the heuristic generation of measure functions"
ML_file \<open>Tools/Function/measure_functions.ML\<close>

lemma measure_size[measure_function]: "is_measure size"
  by (rule is_measure_trivial)

lemma measure_fst[measure_function]: "is_measure f \<Longrightarrow> is_measure (\<lambda>p. f (fst p))"
  by (rule is_measure_trivial)

lemma measure_snd[measure_function]: "is_measure f \<Longrightarrow> is_measure (\<lambda>p. f (snd p))"
  by (rule is_measure_trivial)

ML_file \<open>Tools/Function/lexicographic_order.ML\<close>

method_setup lexicographic_order = \<open>
  Method.sections clasimp_modifiers >>
  (K (SIMPLE_METHOD o Lexicographic_Order.lexicographic_order_tac false))
\<close> "termination prover for lexicographic orderings"


subsection \<open>Congruence rules\<close>

lemma let_cong [fundef_cong]: "M = N \<Longrightarrow> (\<And>x. x = N \<Longrightarrow> f x = g x) \<Longrightarrow> Let M f = Let N g"
  unfolding Let_def by blast

lemmas [fundef_cong] =
  if_cong image_cong
  bex_cong ball_cong imp_cong map_option_cong Option.bind_cong

lemma split_cong [fundef_cong]:
  "(\<And>x y. (x, y) = q \<Longrightarrow> f x y = g x y) \<Longrightarrow> p = q \<Longrightarrow> case_prod f p = case_prod g q"
  by (auto simp: split_def)

lemma comp_cong [fundef_cong]: "f (g x) = f' (g' x') \<Longrightarrow> (f \<circ> g) x = (f' \<circ> g') x'"
  by (simp only: o_apply)


subsection \<open>Simp rules for termination proofs\<close>

declare
  trans_less_add1[termination_simp]
  trans_less_add2[termination_simp]
  trans_le_add1[termination_simp]
  trans_le_add2[termination_simp]
  less_imp_le_nat[termination_simp]
  le_imp_less_Suc[termination_simp]

lemma size_prod_simp[termination_simp]: "size_prod f g p = f (fst p) + g (snd p) + Suc 0"
  by (induct p) auto


subsection \<open>Decomposition\<close>

lemma less_by_empty: "A = {} \<Longrightarrow> A \<subseteq> B"
  and union_comp_emptyL: "A O C = {} \<Longrightarrow> B O C = {} \<Longrightarrow> (A \<union> B) O C = {}"
  and union_comp_emptyR: "A O B = {} \<Longrightarrow> A O C = {} \<Longrightarrow> A O (B \<union> C) = {}"
  and wf_no_loop: "R O R = {} \<Longrightarrow> wf R"
  by (auto simp add: wf_comp_self [of R])


subsection \<open>Reduction pairs\<close>

definition "reduction_pair P \<longleftrightarrow> wf (fst P) \<and> fst P O snd P \<subseteq> fst P"

lemma reduction_pairI[intro]: "wf R \<Longrightarrow> R O S \<subseteq> R \<Longrightarrow> reduction_pair (R, S)"
  by (auto simp: reduction_pair_def)

lemma reduction_pair_lemma:
  assumes rp: "reduction_pair P"
  assumes "R \<subseteq> fst P"
  assumes "S \<subseteq> snd P"
  assumes "wf S"
  shows "wf (R \<union> S)"
proof -
  from rp \<open>S \<subseteq> snd P\<close> have "wf (fst P)" "fst P O S \<subseteq> fst P"
    unfolding reduction_pair_def by auto
  with \<open>wf S\<close> have "wf (fst P \<union> S)"
    by (auto intro: wf_union_compatible)
  moreover from \<open>R \<subseteq> fst P\<close> have "R \<union> S \<subseteq> fst P \<union> S" by auto
  ultimately show ?thesis by (rule wf_subset)
qed

definition "rp_inv_image = (\<lambda>(R,S) f. (inv_image R f, inv_image S f))"

lemma rp_inv_image_rp: "reduction_pair P \<Longrightarrow> reduction_pair (rp_inv_image P f)"
  unfolding reduction_pair_def rp_inv_image_def split_def by force


subsection \<open>Concrete orders for SCNP termination proofs\<close>

definition "pair_less = less_than <*lex*> less_than"
definition "pair_leq = pair_less\<^sup>="
definition "max_strict = max_ext pair_less"
definition "max_weak = max_ext pair_leq \<union> {({}, {})}"
definition "min_strict = min_ext pair_less"
definition "min_weak = min_ext pair_leq \<union> {({}, {})}"

lemma wf_pair_less[simp]: "wf pair_less"
  by (auto simp: pair_less_def)

lemma total_pair_less [iff]: "total_on A pair_less" and trans_pair_less [iff]: "trans pair_less"
  by (auto simp: total_on_def pair_less_def)

text \<open>Introduction rules for \<open>pair_less\<close>/\<open>pair_leq\<close>\<close>
lemma pair_leqI1: "a < b \<Longrightarrow> ((a, s), (b, t)) \<in> pair_leq"
  and pair_leqI2: "a \<le> b \<Longrightarrow> s \<le> t \<Longrightarrow> ((a, s), (b, t)) \<in> pair_leq"
  and pair_lessI1: "a < b  \<Longrightarrow> ((a, s), (b, t)) \<in> pair_less"
  and pair_lessI2: "a \<le> b \<Longrightarrow> s < t \<Longrightarrow> ((a, s), (b, t)) \<in> pair_less"
  by (auto simp: pair_leq_def pair_less_def)

lemma pair_less_iff1 [simp]: "((x,y), (x,z)) \<in> pair_less \<longleftrightarrow> y<z"
  by (simp add: pair_less_def)

text \<open>Introduction rules for max\<close>
lemma smax_emptyI: "finite Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> ({}, Y) \<in> max_strict"
  and smax_insertI:
    "y \<in> Y \<Longrightarrow> (x, y) \<in> pair_less \<Longrightarrow> (X, Y) \<in> max_strict \<Longrightarrow> (insert x X, Y) \<in> max_strict"
  and wmax_emptyI: "finite X \<Longrightarrow> ({}, X) \<in> max_weak"
  and wmax_insertI:
    "y \<in> YS \<Longrightarrow> (x, y) \<in> pair_leq \<Longrightarrow> (XS, YS) \<in> max_weak \<Longrightarrow> (insert x XS, YS) \<in> max_weak"
  by (auto simp: max_strict_def max_weak_def elim!: max_ext.cases)

text \<open>Introduction rules for min\<close>
lemma smin_emptyI: "X \<noteq> {} \<Longrightarrow> (X, {}) \<in> min_strict"
  and smin_insertI:
    "x \<in> XS \<Longrightarrow> (x, y) \<in> pair_less \<Longrightarrow> (XS, YS) \<in> min_strict \<Longrightarrow> (XS, insert y YS) \<in> min_strict"
  and wmin_emptyI: "(X, {}) \<in> min_weak"
  and wmin_insertI:
    "x \<in> XS \<Longrightarrow> (x, y) \<in> pair_leq \<Longrightarrow> (XS, YS) \<in> min_weak \<Longrightarrow> (XS, insert y YS) \<in> min_weak"
  by (auto simp: min_strict_def min_weak_def min_ext_def)

text \<open>Reduction Pairs.\<close>

lemma max_ext_compat:
  assumes "R O S \<subseteq> R"
  shows "max_ext R O (max_ext S \<union> {({}, {})}) \<subseteq> max_ext R"
proof -
  have "\<And>X Y Z. (X, Y) \<in> max_ext R \<Longrightarrow> (Y, Z) \<in> max_ext S \<Longrightarrow> (X, Z) \<in> max_ext R"
  proof -
    fix X Y Z
    assume "(X,Y)\<in>max_ext R"
      "(Y, Z)\<in>max_ext S"
    then have *: "finite X" "finite Y" "finite Z" "Y\<noteq>{}" "Z\<noteq>{}"
      "(\<And>x. x\<in>X \<Longrightarrow> \<exists>y\<in>Y. (x, y)\<in>R)"
      "(\<And>y. y\<in>Y \<Longrightarrow> \<exists>z\<in>Z. (y, z)\<in>S)"
      by (auto elim: max_ext.cases)
    moreover have "\<And>x. x\<in>X \<Longrightarrow> \<exists>z\<in>Z. (x, z)\<in>R"
    proof -
      fix x
      assume "x\<in>X"
      then obtain y where 1: "y\<in>Y" "(x, y)\<in>R"
        using * by auto
      then obtain z where "z\<in>Z" "(y, z)\<in>S"
        using * by auto
      then show "\<exists>z\<in>Z. (x, z)\<in>R"
        using assms 1 by (auto elim: max_ext.cases)
    qed
    ultimately show "(X,Z)\<in>max_ext R"
      by auto
  qed
  then show "max_ext R O (max_ext S \<union> {({}, {})}) \<subseteq> max_ext R"
    by auto
qed

lemma max_rpair_set: "reduction_pair (max_strict, max_weak)"
  unfolding max_strict_def max_weak_def
  apply (intro reduction_pairI max_ext_wf)
   apply simp
  apply (rule max_ext_compat)
  apply (auto simp: pair_less_def pair_leq_def)
  done

lemma min_ext_compat:
  assumes "R O S \<subseteq> R"
  shows "min_ext R O (min_ext S \<union> {({},{})}) \<subseteq> min_ext R"
proof -
  have "\<And>X Y Z z. \<forall>y\<in>Y. \<exists>x\<in>X. (x, y) \<in> R \<Longrightarrow> \<forall>z\<in>Z. \<exists>y\<in>Y. (y, z) \<in> S
  \<Longrightarrow> z \<in> Z \<Longrightarrow> \<exists>x\<in>X. (x, z) \<in> R"
  proof -
    fix X Y Z z
    assume *: "\<forall>y\<in>Y. \<exists>x\<in>X. (x, y) \<in> R"
      "\<forall>z\<in>Z. \<exists>y\<in>Y. (y, z) \<in> S"
      "z\<in>Z"
    then obtain y' where 1: "y'\<in>Y" "(y', z) \<in> S"
      by auto
    then obtain x' where 2: "x'\<in>X" "(x', y') \<in> R"
      using * by auto
    show "\<exists>x\<in>X. (x, z) \<in> R"
      using 1 2 assms by auto
  qed
  then show ?thesis
    using assms by (auto simp: min_ext_def)
qed

lemma min_rpair_set: "reduction_pair (min_strict, min_weak)"
  unfolding min_strict_def min_weak_def
  apply (intro reduction_pairI min_ext_wf)
   apply simp
  apply (rule min_ext_compat)
  apply (auto simp: pair_less_def pair_leq_def)
  done


subsection \<open>Yet more induction principles on the natural numbers\<close>

lemma nat_descend_induct [case_names base descend]:
  fixes P :: "nat \<Rightarrow> bool"
  assumes H1: "\<And>k. k > n \<Longrightarrow> P k"
  assumes H2: "\<And>k. k \<le> n \<Longrightarrow> (\<And>i. i > k \<Longrightarrow> P i) \<Longrightarrow> P k"
  shows "P m"
  using assms by induction_schema (force intro!: wf_measure [of "\<lambda>k. Suc n - k"])+

lemma induct_nat_012[case_names 0 1 ge2]:
  "P 0 \<Longrightarrow> P (Suc 0) \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (Suc n) \<Longrightarrow> P (Suc (Suc n))) \<Longrightarrow> P n"
proof (induction_schema, pat_completeness)
  show "wf (Wellfounded.measure id)"
    by simp
qed auto


subsection \<open>Tool setup\<close>

ML_file \<open>Tools/Function/termination.ML\<close>
ML_file \<open>Tools/Function/scnp_solve.ML\<close>
ML_file \<open>Tools/Function/scnp_reconstruct.ML\<close>
ML_file \<open>Tools/Function/fun_cases.ML\<close>

ML_val \<comment> \<open>setup inactive\<close>
\<open>
  Context.theory_map (Function_Common.set_termination_prover
    (K (ScnpReconstruct.decomp_scnp_tac [ScnpSolve.MAX, ScnpSolve.MIN, ScnpSolve.MS])))
\<close>

end
