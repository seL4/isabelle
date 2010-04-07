(*  Title:      HOL/Library/Quotient_Option.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the option type *}

theory Quotient_Option
imports Main Quotient_Syntax
begin

fun
  option_rel
where
  "option_rel R None None = True"
| "option_rel R (Some x) None = False"
| "option_rel R None (Some x) = False"
| "option_rel R (Some x) (Some y) = R x y"

declare [[map option = (Option.map, option_rel)]]

text {* should probably be in Option.thy *}
lemma split_option_all:
  shows "(\<forall>x. P x) \<longleftrightarrow> P None \<and> (\<forall>a. P (Some a))"
  apply(auto)
  apply(case_tac x)
  apply(simp_all)
  done

lemma option_quotient[quot_thm]:
  assumes q: "Quotient R Abs Rep"
  shows "Quotient (option_rel R) (Option.map Abs) (Option.map Rep)"
  unfolding Quotient_def
  apply(simp add: split_option_all)
  apply(simp add: Quotient_abs_rep[OF q] Quotient_rel_rep[OF q])
  using q
  unfolding Quotient_def
  apply(blast)
  done

lemma option_equivp[quot_equiv]:
  assumes a: "equivp R"
  shows "equivp (option_rel R)"
  apply(rule equivpI)
  unfolding reflp_def symp_def transp_def
  apply(simp_all add: split_option_all)
  apply(blast intro: equivp_reflp[OF a])
  apply(blast intro: equivp_symp[OF a])
  apply(blast intro: equivp_transp[OF a])
  done

lemma option_None_rsp[quot_respect]:
  assumes q: "Quotient R Abs Rep"
  shows "option_rel R None None"
  by simp

lemma option_Some_rsp[quot_respect]:
  assumes q: "Quotient R Abs Rep"
  shows "(R ===> option_rel R) Some Some"
  by simp

lemma option_None_prs[quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "Option.map Abs None = None"
  by simp

lemma option_Some_prs[quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "(Rep ---> Option.map Abs) Some = Some"
  apply(simp add: expand_fun_eq)
  apply(simp add: Quotient_abs_rep[OF q])
  done

lemma option_map_id[id_simps]:
  shows "Option.map id = id"
  by (simp add: expand_fun_eq split_option_all)

lemma option_rel_eq[id_simps]:
  shows "option_rel (op =) = (op =)"
  by (simp add: expand_fun_eq split_option_all)

end
