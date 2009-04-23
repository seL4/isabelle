(*  Title:      HOL/Library/Size_Change_Termination.thy
    Author:     Alexander Krauss, TU Muenchen
*)

header "Size-Change Termination"

theory Size_Change_Termination
imports Correctness Interpretation Implementation 
uses "sct.ML"
begin

subsection {* Simplifier setup *}

text {* This is needed to run the SCT algorithm in the simplifier: *}

lemma setbcomp_simps:
  "{x\<in>{}. P x} = {}"
  "{x\<in>insert y ys. P x} = (if P y then insert y {x\<in>ys. P x} else {x\<in>ys. P x})"
  by auto

lemma setbcomp_cong:
  "A = B \<Longrightarrow> (\<And>x. P x = Q x) \<Longrightarrow> {x\<in>A. P x} = {x\<in>B. Q x}"
  by auto

lemma cartprod_simps:
  "{} \<times> A = {}"
  "insert a A \<times> B = Pair a ` B \<union> (A \<times> B)"
  by (auto simp:image_def)

lemma image_simps:
  "fu ` {} = {}"
  "fu ` insert a A = insert (fu a) (fu ` A)"
  by (auto simp:image_def)

lemmas union_simps = 
  Un_empty_left Un_empty_right Un_insert_left
  
lemma subset_simps:
  "{} \<subseteq> B"
  "insert a A \<subseteq> B \<equiv> a \<in> B \<and> A \<subseteq> B"
  by auto 

lemma element_simps:
  "x \<in> {} \<equiv> False"
  "x \<in> insert a A \<equiv> x = a \<or> x \<in> A"
  by auto

lemma set_eq_simp:
  "A = B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A" by auto

lemma ball_simps:
  "\<forall>x\<in>{}. P x \<equiv> True"
  "(\<forall>x\<in>insert a A. P x) \<equiv> P a \<and> (\<forall>x\<in>A. P x)"
by auto

lemma bex_simps:
  "\<exists>x\<in>{}. P x \<equiv> False"
  "(\<exists>x\<in>insert a A. P x) \<equiv> P a \<or> (\<exists>x\<in>A. P x)"
by auto

lemmas set_simps =
  setbcomp_simps
  cartprod_simps image_simps union_simps subset_simps
  element_simps set_eq_simp
  ball_simps bex_simps

lemma sedge_simps:
  "\<down> * x = \<down>"
  "\<Down> * x = x"
  by (auto simp:mult_sedge_def)

lemmas sctTest_simps =
  simp_thms
  if_True
  if_False
  nat.inject
  nat.distinct
  Pair_eq 

  grcomp_code 
  edges_match.simps 
  connect_edges.simps 

  sedge_simps
  sedge.distinct
  set_simps

  graph_mult_def 
  graph_leq_def
  dest_graph.simps
  graph_plus_def
  graph.inject
  graph_zero_def

  test_SCT_def
  mk_tcl_code

  Let_def
  split_conv

lemmas sctTest_congs = 
  if_weak_cong let_weak_cong setbcomp_cong


lemma SCT_Main:
  "finite_acg A \<Longrightarrow> test_SCT A \<Longrightarrow> SCT A"
  using LJA_Theorem4 SCT'_exec
  by auto

end
