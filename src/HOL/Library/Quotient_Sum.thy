(*  Title:      HOL/Library/Quotient_Sum.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the sum type *}

theory Quotient_Sum
imports Main Quotient_Syntax
begin

subsection {* Rules for the Quotient package *}

lemma sum_rel_map1:
  "sum_rel R1 R2 (map_sum f1 f2 x) y \<longleftrightarrow> sum_rel (\<lambda>x. R1 (f1 x)) (\<lambda>x. R2 (f2 x)) x y"
  by (simp add: sum_rel_def split: sum.split)

lemma sum_rel_map2:
  "sum_rel R1 R2 x (map_sum f1 f2 y) \<longleftrightarrow> sum_rel (\<lambda>x y. R1 x (f1 y)) (\<lambda>x y. R2 x (f2 y)) x y"
  by (simp add: sum_rel_def split: sum.split)

lemma map_sum_id [id_simps]:
  "map_sum id id = id"
  by (simp add: id_def map_sum.identity fun_eq_iff)

lemma sum_rel_eq [id_simps]:
  "sum_rel (op =) (op =) = (op =)"
  by (simp add: sum_rel_def fun_eq_iff split: sum.split)

lemma reflp_sum_rel:
  "reflp R1 \<Longrightarrow> reflp R2 \<Longrightarrow> reflp (sum_rel R1 R2)"
  unfolding reflp_def split_sum_all sum_rel_simps by fast

lemma sum_symp:
  "symp R1 \<Longrightarrow> symp R2 \<Longrightarrow> symp (sum_rel R1 R2)"
  unfolding symp_def split_sum_all sum_rel_simps by fast

lemma sum_transp:
  "transp R1 \<Longrightarrow> transp R2 \<Longrightarrow> transp (sum_rel R1 R2)"
  unfolding transp_def split_sum_all sum_rel_simps by fast

lemma sum_equivp [quot_equiv]:
  "equivp R1 \<Longrightarrow> equivp R2 \<Longrightarrow> equivp (sum_rel R1 R2)"
  by (blast intro: equivpI reflp_sum_rel sum_symp sum_transp elim: equivpE)

lemma sum_quotient [quot_thm]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "Quotient3 (sum_rel R1 R2) (map_sum Abs1 Abs2) (map_sum Rep1 Rep2)"
  apply (rule Quotient3I)
  apply (simp_all add: map_sum.compositionality comp_def map_sum.identity sum_rel_eq sum_rel_map1 sum_rel_map2
    Quotient3_abs_rep [OF q1] Quotient3_rel_rep [OF q1] Quotient3_abs_rep [OF q2] Quotient3_rel_rep [OF q2])
  using Quotient3_rel [OF q1] Quotient3_rel [OF q2]
  apply (simp add: sum_rel_def comp_def split: sum.split)
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
  shows "(Rep1 ---> map_sum Abs1 Abs2) Inl = Inl"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient3_abs_rep[OF q1])
  done

lemma sum_Inr_prs [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  assumes q2: "Quotient3 R2 Abs2 Rep2"
  shows "(Rep2 ---> map_sum Abs1 Abs2) Inr = Inr"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient3_abs_rep[OF q2])
  done

end
