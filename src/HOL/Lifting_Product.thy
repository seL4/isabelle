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

lemmas prod_rel_eq[relator_eq] = prod.rel_eq
lemmas prod_rel_mono[relator_mono] = prod.rel_mono

lemma prod_rel_OO[relator_distr]:
  "(prod_rel A B) OO (prod_rel C D) = prod_rel (A OO C) (B OO D)"
by (rule ext)+ (auto simp: prod_rel_def OO_def)

lemma Domainp_prod[relator_domain]:
  assumes "Domainp T1 = P1"
  assumes "Domainp T2 = P2"
  shows "Domainp (prod_rel T1 T2) = (prod_pred P1 P2)"
using assms unfolding prod_rel_def prod_pred_def by blast

lemma reflp_prod_rel [reflexivity_rule]:
  assumes "reflp R1"
  assumes "reflp R2"
  shows "reflp (prod_rel R1 R2)"
using assms by (auto intro!: reflpI elim: reflpE)

lemma left_total_prod_rel [reflexivity_rule]:
  assumes "left_total R1"
  assumes "left_total R2"
  shows "left_total (prod_rel R1 R2)"
  using assms unfolding left_total_def prod_rel_def by auto

lemma left_unique_prod_rel [reflexivity_rule]:
  assumes "left_unique R1" and "left_unique R2"
  shows "left_unique (prod_rel R1 R2)"
  using assms unfolding left_unique_def prod_rel_def by auto

lemma right_total_prod_rel [transfer_rule]:
  assumes "right_total R1" and "right_total R2"
  shows "right_total (prod_rel R1 R2)"
  using assms unfolding right_total_def prod_rel_def by auto

lemma right_unique_prod_rel [transfer_rule]:
  assumes "right_unique R1" and "right_unique R2"
  shows "right_unique (prod_rel R1 R2)"
  using assms unfolding right_unique_def prod_rel_def by auto

lemma bi_total_prod_rel [transfer_rule]:
  assumes "bi_total R1" and "bi_total R2"
  shows "bi_total (prod_rel R1 R2)"
  using assms unfolding bi_total_def prod_rel_def by auto

lemma bi_unique_prod_rel [transfer_rule]:
  assumes "bi_unique R1" and "bi_unique R2"
  shows "bi_unique (prod_rel R1 R2)"
  using assms unfolding bi_unique_def prod_rel_def by auto

lemma prod_invariant_commute [invariant_commute]: 
  "prod_rel (Lifting.invariant P1) (Lifting.invariant P2) = Lifting.invariant (prod_pred P1 P2)"
  by (simp add: fun_eq_iff prod_rel_def prod_pred_def Lifting.invariant_def) blast

subsection {* Quotient theorem for the Lifting package *}

lemma Quotient_prod[quot_map]:
  assumes "Quotient R1 Abs1 Rep1 T1"
  assumes "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (prod_rel R1 R2) (map_pair Abs1 Abs2)
    (map_pair Rep1 Rep2) (prod_rel T1 T2)"
  using assms unfolding Quotient_alt_def by auto

subsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

lemma Pair_transfer [transfer_rule]: "(A ===> B ===> prod_rel A B) Pair Pair"
  unfolding fun_rel_def prod_rel_def by simp

lemma fst_transfer [transfer_rule]: "(prod_rel A B ===> A) fst fst"
  unfolding fun_rel_def prod_rel_def by simp

lemma snd_transfer [transfer_rule]: "(prod_rel A B ===> B) snd snd"
  unfolding fun_rel_def prod_rel_def by simp

lemma case_prod_transfer [transfer_rule]:
  "((A ===> B ===> C) ===> prod_rel A B ===> C) case_prod case_prod"
  unfolding fun_rel_def prod_rel_def by simp

lemma curry_transfer [transfer_rule]:
  "((prod_rel A B ===> C) ===> A ===> B ===> C) curry curry"
  unfolding curry_def by transfer_prover

lemma map_pair_transfer [transfer_rule]:
  "((A ===> C) ===> (B ===> D) ===> prod_rel A B ===> prod_rel C D)
    map_pair map_pair"
  unfolding map_pair_def [abs_def] by transfer_prover

lemma prod_rel_transfer [transfer_rule]:
  "((A ===> B ===> op =) ===> (C ===> D ===> op =) ===>
    prod_rel A C ===> prod_rel B D ===> op =) prod_rel prod_rel"
  unfolding fun_rel_def by auto

end

end

