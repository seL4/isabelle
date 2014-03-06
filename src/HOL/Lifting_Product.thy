(*  Title:      HOL/Lifting_Product.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

header {* Setup for Lifting/Transfer for the product type *}

theory Lifting_Product
imports Lifting Basic_BNFs
begin

subsection {* Relator and predicator properties *}

definition prod_pred :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where "prod_pred R1 R2 = (\<lambda>(a, b). R1 a \<and> R2 b)"

lemma prod_pred_apply [simp]:
  "prod_pred P1 P2 (a, b) \<longleftrightarrow> P1 a \<and> P2 b"
  by (simp add: prod_pred_def)

lemmas rel_prod_eq[relator_eq] = prod.rel_eq
lemmas rel_prod_mono[relator_mono] = prod.rel_mono

lemma rel_prod_OO[relator_distr]:
  "(rel_prod A B) OO (rel_prod C D) = rel_prod (A OO C) (B OO D)"
by (rule ext)+ (auto simp: rel_prod_def OO_def)

lemma Domainp_prod[relator_domain]:
  assumes "Domainp T1 = P1"
  assumes "Domainp T2 = P2"
  shows "Domainp (rel_prod T1 T2) = (prod_pred P1 P2)"
using assms unfolding rel_prod_def prod_pred_def by blast

lemma left_total_rel_prod [reflexivity_rule]:
  assumes "left_total R1"
  assumes "left_total R2"
  shows "left_total (rel_prod R1 R2)"
  using assms unfolding left_total_def rel_prod_def by auto

lemma left_unique_rel_prod [reflexivity_rule]:
  assumes "left_unique R1" and "left_unique R2"
  shows "left_unique (rel_prod R1 R2)"
  using assms unfolding left_unique_def rel_prod_def by auto

lemma right_total_rel_prod [transfer_rule]:
  assumes "right_total R1" and "right_total R2"
  shows "right_total (rel_prod R1 R2)"
  using assms unfolding right_total_def rel_prod_def by auto

lemma right_unique_rel_prod [transfer_rule]:
  assumes "right_unique R1" and "right_unique R2"
  shows "right_unique (rel_prod R1 R2)"
  using assms unfolding right_unique_def rel_prod_def by auto

lemma bi_total_rel_prod [transfer_rule]:
  assumes "bi_total R1" and "bi_total R2"
  shows "bi_total (rel_prod R1 R2)"
  using assms unfolding bi_total_def rel_prod_def by auto

lemma bi_unique_rel_prod [transfer_rule]:
  assumes "bi_unique R1" and "bi_unique R2"
  shows "bi_unique (rel_prod R1 R2)"
  using assms unfolding bi_unique_def rel_prod_def by auto

lemma prod_invariant_commute [invariant_commute]: 
  "rel_prod (Lifting.invariant P1) (Lifting.invariant P2) = Lifting.invariant (prod_pred P1 P2)"
  by (simp add: fun_eq_iff rel_prod_def prod_pred_def Lifting.invariant_def) blast

subsection {* Quotient theorem for the Lifting package *}

lemma Quotient_prod[quot_map]:
  assumes "Quotient R1 Abs1 Rep1 T1"
  assumes "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (rel_prod R1 R2) (map_prod Abs1 Abs2) (map_prod Rep1 Rep2) (rel_prod T1 T2)"
  using assms unfolding Quotient_alt_def by auto

subsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

lemma Pair_transfer [transfer_rule]: "(A ===> B ===> rel_prod A B) Pair Pair"
  unfolding fun_rel_def rel_prod_def by simp

lemma fst_transfer [transfer_rule]: "(rel_prod A B ===> A) fst fst"
  unfolding fun_rel_def rel_prod_def by simp

lemma snd_transfer [transfer_rule]: "(rel_prod A B ===> B) snd snd"
  unfolding fun_rel_def rel_prod_def by simp

lemma case_prod_transfer [transfer_rule]:
  "((A ===> B ===> C) ===> rel_prod A B ===> C) case_prod case_prod"
  unfolding fun_rel_def rel_prod_def by simp

lemma curry_transfer [transfer_rule]:
  "((rel_prod A B ===> C) ===> A ===> B ===> C) curry curry"
  unfolding curry_def by transfer_prover

lemma map_prod_transfer [transfer_rule]:
  "((A ===> C) ===> (B ===> D) ===> rel_prod A B ===> rel_prod C D)
    map_prod map_prod"
  unfolding map_prod_def [abs_def] by transfer_prover

lemma rel_prod_transfer [transfer_rule]:
  "((A ===> B ===> op =) ===> (C ===> D ===> op =) ===>
    rel_prod A C ===> rel_prod B D ===> op =) rel_prod rel_prod"
  unfolding fun_rel_def by auto

end

end

