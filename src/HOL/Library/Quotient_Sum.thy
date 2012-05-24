(*  Title:      HOL/Library/Quotient_Sum.thy
    Author:     Cezary Kaliszyk, Christian Urban and Brian Huffman
*)

header {* Quotient infrastructure for the sum type *}

theory Quotient_Sum
imports Main Quotient_Syntax
begin

subsection {* Relator for sum type *}

fun
  sum_rel :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> 'c + 'd \<Rightarrow> bool"
where
  "sum_rel R1 R2 (Inl a1) (Inl b1) = R1 a1 b1"
| "sum_rel R1 R2 (Inl a1) (Inr b2) = False"
| "sum_rel R1 R2 (Inr a2) (Inl b1) = False"
| "sum_rel R1 R2 (Inr a2) (Inr b2) = R2 a2 b2"

lemma sum_rel_unfold:
  "sum_rel R1 R2 x y = (case (x, y) of (Inl x, Inl y) \<Rightarrow> R1 x y
    | (Inr x, Inr y) \<Rightarrow> R2 x y
    | _ \<Rightarrow> False)"
  by (cases x) (cases y, simp_all)+

lemma sum_rel_map1:
  "sum_rel R1 R2 (sum_map f1 f2 x) y \<longleftrightarrow> sum_rel (\<lambda>x. R1 (f1 x)) (\<lambda>x. R2 (f2 x)) x y"
  by (simp add: sum_rel_unfold split: sum.split)

lemma sum_rel_map2:
  "sum_rel R1 R2 x (sum_map f1 f2 y) \<longleftrightarrow> sum_rel (\<lambda>x y. R1 x (f1 y)) (\<lambda>x y. R2 x (f2 y)) x y"
  by (simp add: sum_rel_unfold split: sum.split)

lemma sum_map_id [id_simps]:
  "sum_map id id = id"
  by (simp add: id_def sum_map.identity fun_eq_iff)

lemma sum_rel_eq [id_simps, relator_eq]:
  "sum_rel (op =) (op =) = (op =)"
  by (simp add: sum_rel_unfold fun_eq_iff split: sum.split)

lemma split_sum_all: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P (Inl x)) \<and> (\<forall>x. P (Inr x))"
  by (metis sum.exhaust) (* TODO: move to Sum_Type.thy *)

lemma split_sum_ex: "(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. P (Inl x)) \<or> (\<exists>x. P (Inr x))"
  by (metis sum.exhaust) (* TODO: move to Sum_Type.thy *)

lemma sum_reflp[reflexivity_rule]:
  "reflp R1 \<Longrightarrow> reflp R2 \<Longrightarrow> reflp (sum_rel R1 R2)"
  unfolding reflp_def split_sum_all sum_rel.simps by fast

lemma sum_left_total[reflexivity_rule]:
  "left_total R1 \<Longrightarrow> left_total R2 \<Longrightarrow> left_total (sum_rel R1 R2)"
  apply (intro left_totalI)
  unfolding split_sum_ex 
  by (case_tac x) (auto elim: left_totalE)

lemma sum_symp:
  "symp R1 \<Longrightarrow> symp R2 \<Longrightarrow> symp (sum_rel R1 R2)"
  unfolding symp_def split_sum_all sum_rel.simps by fast

lemma sum_transp:
  "transp R1 \<Longrightarrow> transp R2 \<Longrightarrow> transp (sum_rel R1 R2)"
  unfolding transp_def split_sum_all sum_rel.simps by fast

lemma sum_equivp [quot_equiv]:
  "equivp R1 \<Longrightarrow> equivp R2 \<Longrightarrow> equivp (sum_rel R1 R2)"
  by (blast intro: equivpI sum_reflp sum_symp sum_transp elim: equivpE)

lemma right_total_sum_rel [transfer_rule]:
  "right_total R1 \<Longrightarrow> right_total R2 \<Longrightarrow> right_total (sum_rel R1 R2)"
  unfolding right_total_def split_sum_all split_sum_ex by simp

lemma right_unique_sum_rel [transfer_rule]:
  "right_unique R1 \<Longrightarrow> right_unique R2 \<Longrightarrow> right_unique (sum_rel R1 R2)"
  unfolding right_unique_def split_sum_all by simp

lemma bi_total_sum_rel [transfer_rule]:
  "bi_total R1 \<Longrightarrow> bi_total R2 \<Longrightarrow> bi_total (sum_rel R1 R2)"
  using assms unfolding bi_total_def split_sum_all split_sum_ex by simp

lemma bi_unique_sum_rel [transfer_rule]:
  "bi_unique R1 \<Longrightarrow> bi_unique R2 \<Longrightarrow> bi_unique (sum_rel R1 R2)"
  using assms unfolding bi_unique_def split_sum_all by simp

subsection {* Transfer rules for transfer package *}

lemma Inl_transfer [transfer_rule]: "(A ===> sum_rel A B) Inl Inl"
  unfolding fun_rel_def by simp

lemma Inr_transfer [transfer_rule]: "(B ===> sum_rel A B) Inr Inr"
  unfolding fun_rel_def by simp

lemma sum_case_transfer [transfer_rule]:
  "((A ===> C) ===> (B ===> C) ===> sum_rel A B ===> C) sum_case sum_case"
  unfolding fun_rel_def sum_rel_unfold by (simp split: sum.split)

subsection {* Setup for lifting package *}

lemma Quotient_sum[quot_map]:
  assumes "Quotient R1 Abs1 Rep1 T1"
  assumes "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (sum_rel R1 R2) (sum_map Abs1 Abs2)
    (sum_map Rep1 Rep2) (sum_rel T1 T2)"
  using assms unfolding Quotient_alt_def
  by (simp add: split_sum_all)

fun sum_pred :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> bool"
where
  "sum_pred R1 R2 (Inl a) = R1 a"
| "sum_pred R1 R2 (Inr a) = R2 a"

lemma sum_invariant_commute [invariant_commute]: 
  "sum_rel (Lifting.invariant P1) (Lifting.invariant P2) = Lifting.invariant (sum_pred P1 P2)"
  apply (simp add: fun_eq_iff Lifting.invariant_def)
  apply (intro allI) 
  apply (case_tac x rule: sum.exhaust)
  apply (case_tac xa rule: sum.exhaust)
  apply auto[2]
  apply (case_tac xa rule: sum.exhaust)
  apply auto
done

subsection {* Rules for quotient package *}

lemma sum_quotient [quot_thm]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "Quotient3 (sum_rel R1 R2) (sum_map Abs1 Abs2) (sum_map Rep1 Rep2)"
  apply (rule Quotient3I)
  apply (simp_all add: sum_map.compositionality comp_def sum_map.identity sum_rel_eq sum_rel_map1 sum_rel_map2
    Quotient3_abs_rep [OF q1] Quotient3_rel_rep [OF q1] Quotient3_abs_rep [OF q2] Quotient3_rel_rep [OF q2])
  using Quotient3_rel [OF q1] Quotient3_rel [OF q2]
  apply (simp add: sum_rel_unfold comp_def split: sum.split)
  done

declare [[mapQ3 sum = (sum_rel, sum_quotient)]]

lemma sum_Inl_rsp [quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(R1 ===> sum_rel R1 R2) Inl Inl"
  by auto

lemma sum_Inr_rsp [quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(R2 ===> sum_rel R1 R2) Inr Inr"
  by auto

lemma sum_Inl_prs [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep1 ---> sum_map Abs1 Abs2) Inl = Inl"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient3_abs_rep[OF q1])
  done

lemma sum_Inr_prs [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep2 ---> sum_map Abs1 Abs2) Inr = Inr"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient3_abs_rep[OF q2])
  done

end
