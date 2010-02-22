(*  Title:      Quotient_Sum.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)
theory Quotient_Sum
imports Main Quotient_Syntax
begin

section {* Quotient infrastructure for the sum type. *}

fun
  sum_rel
where
  "sum_rel R1 R2 (Inl a1) (Inl b1) = R1 a1 b1"
| "sum_rel R1 R2 (Inl a1) (Inr b2) = False"
| "sum_rel R1 R2 (Inr a2) (Inl b1) = False"
| "sum_rel R1 R2 (Inr a2) (Inr b2) = R2 a2 b2"

fun
  sum_map
where
  "sum_map f1 f2 (Inl a) = Inl (f1 a)"
| "sum_map f1 f2 (Inr a) = Inr (f2 a)"

declare [[map "+" = (sum_map, sum_rel)]]


text {* should probably be in @{theory Sum_Type} *}
lemma split_sum_all:
  shows "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P (Inl x)) \<and> (\<forall>x. P (Inr x))"
  apply(auto)
  apply(case_tac x)
  apply(simp_all)
  done

lemma sum_equivp[quot_equiv]:
  assumes a: "equivp R1"
  assumes b: "equivp R2"
  shows "equivp (sum_rel R1 R2)"
  apply(rule equivpI)
  unfolding reflp_def symp_def transp_def
  apply(simp_all add: split_sum_all)
  apply(blast intro: equivp_reflp[OF a] equivp_reflp[OF b])
  apply(blast intro: equivp_symp[OF a] equivp_symp[OF b])
  apply(blast intro: equivp_transp[OF a] equivp_transp[OF b])
  done

lemma sum_quotient[quot_thm]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "Quotient (sum_rel R1 R2) (sum_map Abs1 Abs2) (sum_map Rep1 Rep2)"
  unfolding Quotient_def
  apply(simp add: split_sum_all)
  apply(simp_all add: Quotient_abs_rep[OF q1] Quotient_rel_rep[OF q1])
  apply(simp_all add: Quotient_abs_rep[OF q2] Quotient_rel_rep[OF q2])
  using q1 q2
  unfolding Quotient_def
  apply(blast)+
  done

lemma sum_Inl_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(R1 ===> sum_rel R1 R2) Inl Inl"
  by simp

lemma sum_Inr_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(R2 ===> sum_rel R1 R2) Inr Inr"
  by simp

lemma sum_Inl_prs[quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(Rep1 ---> sum_map Abs1 Abs2) Inl = Inl"
  apply(simp add: expand_fun_eq)
  apply(simp add: Quotient_abs_rep[OF q1])
  done

lemma sum_Inr_prs[quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(Rep2 ---> sum_map Abs1 Abs2) Inr = Inr"
  apply(simp add: expand_fun_eq)
  apply(simp add: Quotient_abs_rep[OF q2])
  done

lemma sum_map_id[id_simps]:
  shows "sum_map id id = id"
  by (simp add: expand_fun_eq split_sum_all)

lemma sum_rel_eq[id_simps]:
  shows "sum_rel (op =) (op =) = (op =)"
  by (simp add: expand_fun_eq split_sum_all)

end
