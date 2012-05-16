(*  Title:      HOL/Library/Quotient_Product.thy
    Author:     Cezary Kaliszyk, Christian Urban and Brian Huffman
*)

header {* Quotient infrastructure for the product type *}

theory Quotient_Product
imports Main Quotient_Syntax
begin

subsection {* Relator for product type *}

definition
  prod_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'c \<Rightarrow> 'b \<times> 'd \<Rightarrow> bool"
where
  "prod_rel R1 R2 = (\<lambda>(a, b) (c, d). R1 a c \<and> R2 b d)"

lemma prod_rel_apply [simp]:
  "prod_rel R1 R2 (a, b) (c, d) \<longleftrightarrow> R1 a c \<and> R2 b d"
  by (simp add: prod_rel_def)

lemma map_pair_id [id_simps]:
  shows "map_pair id id = id"
  by (simp add: fun_eq_iff)

lemma prod_rel_eq [id_simps, relator_eq]:
  shows "prod_rel (op =) (op =) = (op =)"
  by (simp add: fun_eq_iff)

lemma prod_reflp [reflp_preserve]:
  assumes "reflp R1"
  assumes "reflp R2"
  shows "reflp (prod_rel R1 R2)"
using assms by (auto intro!: reflpI elim: reflpE)

lemma prod_equivp [quot_equiv]:
  assumes "equivp R1"
  assumes "equivp R2"
  shows "equivp (prod_rel R1 R2)"
  using assms by (auto intro!: equivpI reflpI sympI transpI elim!: equivpE elim: reflpE sympE transpE)

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

subsection {* Transfer rules for transfer package *}

lemma Pair_transfer [transfer_rule]: "(A ===> B ===> prod_rel A B) Pair Pair"
  unfolding fun_rel_def prod_rel_def by simp

lemma fst_transfer [transfer_rule]: "(prod_rel A B ===> A) fst fst"
  unfolding fun_rel_def prod_rel_def by simp

lemma snd_transfer [transfer_rule]: "(prod_rel A B ===> B) snd snd"
  unfolding fun_rel_def prod_rel_def by simp

lemma prod_case_transfer [transfer_rule]:
  "((A ===> B ===> C) ===> prod_rel A B ===> C) prod_case prod_case"
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

subsection {* Setup for lifting package *}

lemma Quotient_prod[quot_map]:
  assumes "Quotient R1 Abs1 Rep1 T1"
  assumes "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (prod_rel R1 R2) (map_pair Abs1 Abs2)
    (map_pair Rep1 Rep2) (prod_rel T1 T2)"
  using assms unfolding Quotient_alt_def by auto

definition prod_pred :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where "prod_pred R1 R2 = (\<lambda>(a, b). R1 a \<and> R2 b)"

lemma prod_invariant_commute [invariant_commute]: 
  "prod_rel (Lifting.invariant P1) (Lifting.invariant P2) = Lifting.invariant (prod_pred P1 P2)"
  apply (simp add: fun_eq_iff prod_rel_def prod_pred_def Lifting.invariant_def) 
  apply blast
done

subsection {* Rules for quotient package *}

lemma prod_quotient [quot_thm]:
  assumes "Quotient3 R1 Abs1 Rep1"
  assumes "Quotient3 R2 Abs2 Rep2"
  shows "Quotient3 (prod_rel R1 R2) (map_pair Abs1 Abs2) (map_pair Rep1 Rep2)"
  apply (rule Quotient3I)
  apply (simp add: map_pair.compositionality comp_def map_pair.identity
     Quotient3_abs_rep [OF assms(1)] Quotient3_abs_rep [OF assms(2)])
  apply (simp add: split_paired_all Quotient3_rel_rep [OF assms(1)] Quotient3_rel_rep [OF assms(2)])
  using Quotient3_rel [OF assms(1)] Quotient3_rel [OF assms(2)]
  apply (auto simp add: split_paired_all)
  done

declare [[mapQ3 prod = (prod_rel, prod_quotient)]]

lemma Pair_rsp [quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(R1 ===> R2 ===> prod_rel R1 R2) Pair Pair"
  by (rule Pair_transfer)

lemma Pair_prs [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep1 ---> Rep2 ---> (map_pair Abs1 Abs2)) Pair = Pair"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2])
  done

lemma fst_rsp [quot_respect]:
  assumes "Quotient3 R1 Abs1 Rep1"
  assumes "Quotient3 R2 Abs2 Rep2"
  shows "(prod_rel R1 R2 ===> R1) fst fst"
  by auto

lemma fst_prs [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(map_pair Rep1 Rep2 ---> Abs1) fst = fst"
  by (simp add: fun_eq_iff Quotient3_abs_rep[OF q1])

lemma snd_rsp [quot_respect]:
  assumes "Quotient3 R1 Abs1 Rep1"
  assumes "Quotient3 R2 Abs2 Rep2"
  shows "(prod_rel R1 R2 ===> R2) snd snd"
  by auto

lemma snd_prs [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(map_pair Rep1 Rep2 ---> Abs2) snd = snd"
  by (simp add: fun_eq_iff Quotient3_abs_rep[OF q2])

lemma split_rsp [quot_respect]:
  shows "((R1 ===> R2 ===> (op =)) ===> (prod_rel R1 R2) ===> (op =)) split split"
  by (rule prod_case_transfer)

lemma split_prs [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "(((Abs1 ---> Abs2 ---> id) ---> map_pair Rep1 Rep2 ---> id) split) = split"
  by (simp add: fun_eq_iff Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2])

lemma [quot_respect]:
  shows "((R2 ===> R2 ===> op =) ===> (R1 ===> R1 ===> op =) ===>
  prod_rel R2 R1 ===> prod_rel R2 R1 ===> op =) prod_rel prod_rel"
  by (rule prod_rel_transfer)

lemma [quot_preserve]:
  assumes q1: "Quotient3 R1 abs1 rep1"
  and     q2: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> abs1 ---> id) ---> (abs2 ---> abs2 ---> id) --->
  map_pair rep1 rep2 ---> map_pair rep1 rep2 ---> id) prod_rel = prod_rel"
  by (simp add: fun_eq_iff Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2])

lemma [quot_preserve]:
  shows"(prod_rel ((rep1 ---> rep1 ---> id) R1) ((rep2 ---> rep2 ---> id) R2)
  (l1, l2) (r1, r2)) = (R1 (rep1 l1) (rep1 r1) \<and> R2 (rep2 l2) (rep2 r2))"
  by simp

declare Pair_eq[quot_preserve]

end
