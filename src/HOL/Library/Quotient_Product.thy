(*  Title:      HOL/Library/Quotient_Product.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the product type *}

theory Quotient_Product
imports Main Quotient_Syntax
begin

fun
  prod_rel
where
  "prod_rel R1 R2 = (\<lambda>(a, b) (c, d). R1 a c \<and> R2 b d)"

declare [[map * = (prod_fun, prod_rel)]]


lemma prod_equivp[quot_equiv]:
  assumes a: "equivp R1"
  assumes b: "equivp R2"
  shows "equivp (prod_rel R1 R2)"
  apply(rule equivpI)
  unfolding reflp_def symp_def transp_def
  apply(simp_all add: split_paired_all)
  apply(blast intro: equivp_reflp[OF a] equivp_reflp[OF b])
  apply(blast intro: equivp_symp[OF a] equivp_symp[OF b])
  apply(blast intro: equivp_transp[OF a] equivp_transp[OF b])
  done

lemma prod_quotient[quot_thm]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "Quotient (prod_rel R1 R2) (prod_fun Abs1 Abs2) (prod_fun Rep1 Rep2)"
  unfolding Quotient_def
  apply(simp add: split_paired_all)
  apply(simp add: Quotient_abs_rep[OF q1] Quotient_rel_rep[OF q1])
  apply(simp add: Quotient_abs_rep[OF q2] Quotient_rel_rep[OF q2])
  using q1 q2
  unfolding Quotient_def
  apply(blast)
  done

lemma Pair_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(R1 ===> R2 ===> prod_rel R1 R2) Pair Pair"
  by simp

lemma Pair_prs[quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(Rep1 ---> Rep2 ---> (prod_fun Abs1 Abs2)) Pair = Pair"
  apply(simp add: expand_fun_eq)
  apply(simp add: Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2])
  done

lemma fst_rsp[quot_respect]:
  assumes "Quotient R1 Abs1 Rep1"
  assumes "Quotient R2 Abs2 Rep2"
  shows "(prod_rel R1 R2 ===> R1) fst fst"
  by simp

lemma fst_prs[quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(prod_fun Rep1 Rep2 ---> Abs1) fst = fst"
  apply(simp add: expand_fun_eq)
  apply(simp add: Quotient_abs_rep[OF q1])
  done

lemma snd_rsp[quot_respect]:
  assumes "Quotient R1 Abs1 Rep1"
  assumes "Quotient R2 Abs2 Rep2"
  shows "(prod_rel R1 R2 ===> R2) snd snd"
  by simp

lemma snd_prs[quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  assumes q2: "Quotient R2 Abs2 Rep2"
  shows "(prod_fun Rep1 Rep2 ---> Abs2) snd = snd"
  apply(simp add: expand_fun_eq)
  apply(simp add: Quotient_abs_rep[OF q2])
  done

lemma split_rsp[quot_respect]:
  shows "((R1 ===> R2 ===> (op =)) ===> (prod_rel R1 R2) ===> (op =)) split split"
  by auto

lemma split_prs[quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "(((Abs1 ---> Abs2 ---> id) ---> prod_fun Rep1 Rep2 ---> id) split) = split"
  by (simp add: expand_fun_eq Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2])

lemma prod_fun_id[id_simps]:
  shows "prod_fun id id = id"
  by (simp add: prod_fun_def)

lemma prod_rel_eq[id_simps]:
  shows "prod_rel (op =) (op =) = (op =)"
  by (simp add: expand_fun_eq)

end
