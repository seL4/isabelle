(*  Title:      HOL/FunDef.thy
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Function Definitions and Termination Proofs *}

theory FunDef
imports Partial_Function Wellfounded
uses
  "Tools/prop_logic.ML"
  "Tools/sat_solver.ML"
  ("Tools/Function/function_common.ML")
  ("Tools/Function/context_tree.ML")
  ("Tools/Function/function_core.ML")
  ("Tools/Function/sum_tree.ML")
  ("Tools/Function/mutual.ML")
  ("Tools/Function/pattern_split.ML")
  ("Tools/Function/function.ML")
  ("Tools/Function/relation.ML")
  ("Tools/Function/measure_functions.ML")
  ("Tools/Function/lexicographic_order.ML")
  ("Tools/Function/pat_completeness.ML")
  ("Tools/Function/fun.ML")
  ("Tools/Function/induction_schema.ML")
  ("Tools/Function/termination.ML")
  ("Tools/Function/scnp_solve.ML")
  ("Tools/Function/scnp_reconstruct.ML")
begin

subsection {* Definitions with default value. *}

definition
  THE_default :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "THE_default d P = (if (\<exists>!x. P x) then (THE x. P x) else d)"

lemma THE_defaultI': "\<exists>!x. P x \<Longrightarrow> P (THE_default d P)"
  by (simp add: theI' THE_default_def)

lemma THE_default1_equality:
    "\<lbrakk>\<exists>!x. P x; P a\<rbrakk> \<Longrightarrow> THE_default d P = a"
  by (simp add: the1_equality THE_default_def)

lemma THE_default_none:
    "\<not>(\<exists>!x. P x) \<Longrightarrow> THE_default d P = d"
  by (simp add:THE_default_def)


lemma fundef_ex1_existence:
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  shows "G x (f x)"
  apply (simp only: f_def)
  apply (rule THE_defaultI')
  apply (rule ex1)
  done

lemma fundef_ex1_uniqueness:
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  assumes elm: "G x (h x)"
  shows "h x = f x"
  apply (simp only: f_def)
  apply (rule THE_default1_equality [symmetric])
   apply (rule ex1)
  apply (rule elm)
  done

lemma fundef_ex1_iff:
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes ex1: "\<exists>!y. G x y"
  shows "(G x y) = (f x = y)"
  apply (auto simp:ex1 f_def THE_default1_equality)
  apply (rule THE_defaultI')
  apply (rule ex1)
  done

lemma fundef_default_value:
  assumes f_def: "f == (\<lambda>x::'a. THE_default (d x) (\<lambda>y. G x y))"
  assumes graph: "\<And>x y. G x y \<Longrightarrow> D x"
  assumes "\<not> D x"
  shows "f x = d x"
proof -
  have "\<not>(\<exists>y. G x y)"
  proof
    assume "\<exists>y. G x y"
    hence "D x" using graph ..
    with `\<not> D x` show False ..
  qed
  hence "\<not>(\<exists>!y. G x y)" by blast

  thus ?thesis
    unfolding f_def
    by (rule THE_default_none)
qed

definition in_rel_def[simp]:
  "in_rel R x y == (x, y) \<in> R"

lemma wf_in_rel:
  "wf R \<Longrightarrow> wfP (in_rel R)"
  by (simp add: wfP_def)

use "Tools/Function/function_common.ML"
use "Tools/Function/context_tree.ML"
use "Tools/Function/function_core.ML"
use "Tools/Function/sum_tree.ML"
use "Tools/Function/mutual.ML"
use "Tools/Function/pattern_split.ML"
use "Tools/Function/relation.ML"
use "Tools/Function/function.ML"
use "Tools/Function/pat_completeness.ML"
use "Tools/Function/fun.ML"
use "Tools/Function/induction_schema.ML"

setup {* 
  Function.setup
  #> Pat_Completeness.setup
  #> Function_Fun.setup
  #> Induction_Schema.setup
*}

subsection {* Measure Functions *}

inductive is_measure :: "('a \<Rightarrow> nat) \<Rightarrow> bool"
where is_measure_trivial: "is_measure f"

use "Tools/Function/measure_functions.ML"
setup MeasureFunctions.setup

lemma measure_size[measure_function]: "is_measure size"
by (rule is_measure_trivial)

lemma measure_fst[measure_function]: "is_measure f \<Longrightarrow> is_measure (\<lambda>p. f (fst p))"
by (rule is_measure_trivial)
lemma measure_snd[measure_function]: "is_measure f \<Longrightarrow> is_measure (\<lambda>p. f (snd p))"
by (rule is_measure_trivial)

use "Tools/Function/lexicographic_order.ML"
setup Lexicographic_Order.setup 


subsection {* Congruence Rules *}

lemma let_cong [fundef_cong]:
  "M = N \<Longrightarrow> (\<And>x. x = N \<Longrightarrow> f x = g x) \<Longrightarrow> Let M f = Let N g"
  unfolding Let_def by blast

lemmas [fundef_cong] =
  if_cong image_cong INT_cong UN_cong
  bex_cong ball_cong imp_cong Option.map_cong Option.bind_cong

lemma split_cong [fundef_cong]:
  "(\<And>x y. (x, y) = q \<Longrightarrow> f x y = g x y) \<Longrightarrow> p = q
    \<Longrightarrow> split f p = split g q"
  by (auto simp: split_def)

lemma comp_cong [fundef_cong]:
  "f (g x) = f' (g' x') \<Longrightarrow> (f o g) x = (f' o g') x'"
  unfolding o_apply .

subsection {* Simp rules for termination proofs *}

lemma termination_basic_simps[termination_simp]:
  "x < (y::nat) \<Longrightarrow> x < y + z" 
  "x < z \<Longrightarrow> x < y + z"
  "x \<le> y \<Longrightarrow> x \<le> y + (z::nat)"
  "x \<le> z \<Longrightarrow> x \<le> y + (z::nat)"
  "x < y \<Longrightarrow> x \<le> (y::nat)"
by arith+

declare le_imp_less_Suc[termination_simp]

lemma prod_size_simp[termination_simp]:
  "prod_size f g p = f (fst p) + g (snd p) + Suc 0"
by (induct p) auto

subsection {* Decomposition *}

lemma less_by_empty: 
  "A = {} \<Longrightarrow> A \<subseteq> B"
and  union_comp_emptyL:
  "\<lbrakk> A O C = {}; B O C = {} \<rbrakk> \<Longrightarrow> (A \<union> B) O C = {}"
and union_comp_emptyR:
  "\<lbrakk> A O B = {}; A O C = {} \<rbrakk> \<Longrightarrow> A O (B \<union> C) = {}"
and wf_no_loop: 
  "R O R = {} \<Longrightarrow> wf R"
by (auto simp add: wf_comp_self[of R])


subsection {* Reduction Pairs *}

definition
  "reduction_pair P = (wf (fst P) \<and> fst P O snd P \<subseteq> fst P)"

lemma reduction_pairI[intro]: "wf R \<Longrightarrow> R O S \<subseteq> R \<Longrightarrow> reduction_pair (R, S)"
unfolding reduction_pair_def by auto

lemma reduction_pair_lemma:
  assumes rp: "reduction_pair P"
  assumes "R \<subseteq> fst P"
  assumes "S \<subseteq> snd P"
  assumes "wf S"
  shows "wf (R \<union> S)"
proof -
  from rp `S \<subseteq> snd P` have "wf (fst P)" "fst P O S \<subseteq> fst P"
    unfolding reduction_pair_def by auto
  with `wf S` have "wf (fst P \<union> S)" 
    by (auto intro: wf_union_compatible)
  moreover from `R \<subseteq> fst P` have "R \<union> S \<subseteq> fst P \<union> S" by auto
  ultimately show ?thesis by (rule wf_subset) 
qed

definition
  "rp_inv_image = (\<lambda>(R,S) f. (inv_image R f, inv_image S f))"

lemma rp_inv_image_rp:
  "reduction_pair P \<Longrightarrow> reduction_pair (rp_inv_image P f)"
  unfolding reduction_pair_def rp_inv_image_def split_def
  by force


subsection {* Concrete orders for SCNP termination proofs *}

definition "pair_less = less_than <*lex*> less_than"
definition "pair_leq = pair_less^="
definition "max_strict = max_ext pair_less"
definition "max_weak = max_ext pair_leq \<union> {({}, {})}"
definition "min_strict = min_ext pair_less"
definition "min_weak = min_ext pair_leq \<union> {({}, {})}"

lemma wf_pair_less[simp]: "wf pair_less"
  by (auto simp: pair_less_def)

text {* Introduction rules for @{text pair_less}/@{text pair_leq} *}
lemma pair_leqI1: "a < b \<Longrightarrow> ((a, s), (b, t)) \<in> pair_leq"
  and pair_leqI2: "a \<le> b \<Longrightarrow> s \<le> t \<Longrightarrow> ((a, s), (b, t)) \<in> pair_leq"
  and pair_lessI1: "a < b  \<Longrightarrow> ((a, s), (b, t)) \<in> pair_less"
  and pair_lessI2: "a \<le> b \<Longrightarrow> s < t \<Longrightarrow> ((a, s), (b, t)) \<in> pair_less"
  unfolding pair_leq_def pair_less_def by auto

text {* Introduction rules for max *}
lemma smax_emptyI: 
  "finite Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> ({}, Y) \<in> max_strict" 
  and smax_insertI: 
  "\<lbrakk>y \<in> Y; (x, y) \<in> pair_less; (X, Y) \<in> max_strict\<rbrakk> \<Longrightarrow> (insert x X, Y) \<in> max_strict"
  and wmax_emptyI: 
  "finite X \<Longrightarrow> ({}, X) \<in> max_weak" 
  and wmax_insertI:
  "\<lbrakk>y \<in> YS; (x, y) \<in> pair_leq; (XS, YS) \<in> max_weak\<rbrakk> \<Longrightarrow> (insert x XS, YS) \<in> max_weak" 
unfolding max_strict_def max_weak_def by (auto elim!: max_ext.cases)

text {* Introduction rules for min *}
lemma smin_emptyI: 
  "X \<noteq> {} \<Longrightarrow> (X, {}) \<in> min_strict" 
  and smin_insertI: 
  "\<lbrakk>x \<in> XS; (x, y) \<in> pair_less; (XS, YS) \<in> min_strict\<rbrakk> \<Longrightarrow> (XS, insert y YS) \<in> min_strict"
  and wmin_emptyI: 
  "(X, {}) \<in> min_weak" 
  and wmin_insertI: 
  "\<lbrakk>x \<in> XS; (x, y) \<in> pair_leq; (XS, YS) \<in> min_weak\<rbrakk> \<Longrightarrow> (XS, insert y YS) \<in> min_weak" 
by (auto simp: min_strict_def min_weak_def min_ext_def)

text {* Reduction Pairs *}

lemma max_ext_compat: 
  assumes "R O S \<subseteq> R"
  shows "max_ext R O (max_ext S \<union> {({},{})}) \<subseteq> max_ext R"
using assms 
apply auto
apply (elim max_ext.cases)
apply rule
apply auto[3]
apply (drule_tac x=xa in meta_spec)
apply simp
apply (erule bexE)
apply (drule_tac x=xb in meta_spec)
by auto

lemma max_rpair_set: "reduction_pair (max_strict, max_weak)"
  unfolding max_strict_def max_weak_def 
apply (intro reduction_pairI max_ext_wf)
apply simp
apply (rule max_ext_compat)
by (auto simp: pair_less_def pair_leq_def)

lemma min_ext_compat: 
  assumes "R O S \<subseteq> R"
  shows "min_ext R O  (min_ext S \<union> {({},{})}) \<subseteq> min_ext R"
using assms 
apply (auto simp: min_ext_def)
apply (drule_tac x=ya in bspec, assumption)
apply (erule bexE)
apply (drule_tac x=xc in bspec)
apply assumption
by auto

lemma min_rpair_set: "reduction_pair (min_strict, min_weak)"
  unfolding min_strict_def min_weak_def 
apply (intro reduction_pairI min_ext_wf)
apply simp
apply (rule min_ext_compat)
by (auto simp: pair_less_def pair_leq_def)


subsection {* Tool setup *}

use "Tools/Function/termination.ML"
use "Tools/Function/scnp_solve.ML"
use "Tools/Function/scnp_reconstruct.ML"

setup {* ScnpReconstruct.setup *}

ML_val -- "setup inactive"
{*
  Context.theory_map (Function_Common.set_termination_prover
    (ScnpReconstruct.decomp_scnp_tac [ScnpSolve.MAX, ScnpSolve.MIN, ScnpSolve.MS]))
*}

end
