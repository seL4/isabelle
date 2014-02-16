(*  Title:      HOL/Library/Quotient_Option.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the option type *}

theory Quotient_Option
imports Main Quotient_Syntax
begin

subsection {* Rules for the Quotient package *}

lemma rel_option_map1:
  "rel_option R (map_option f x) y \<longleftrightarrow> rel_option (\<lambda>x. R (f x)) x y"
  by (simp add: rel_option_iff split: option.split)

lemma rel_option_map2:
  "rel_option R x (map_option f y) \<longleftrightarrow> rel_option (\<lambda>x y. R x (f y)) x y"
  by (simp add: rel_option_iff split: option.split)

declare
  map_option.id [id_simps]
  rel_option_eq [id_simps]

lemma option_symp:
  "symp R \<Longrightarrow> symp (rel_option R)"
  unfolding symp_def split_option_all
  by (simp only: option.rel_inject option.rel_distinct) fast

lemma option_transp:
  "transp R \<Longrightarrow> transp (rel_option R)"
  unfolding transp_def split_option_all
  by (simp only: option.rel_inject option.rel_distinct) fast

lemma option_equivp [quot_equiv]:
  "equivp R \<Longrightarrow> equivp (rel_option R)"
  by (blast intro: equivpI reflp_rel_option option_symp option_transp elim: equivpE)

lemma option_quotient [quot_thm]:
  assumes "Quotient3 R Abs Rep"
  shows "Quotient3 (rel_option R) (map_option Abs) (map_option Rep)"
  apply (rule Quotient3I)
  apply (simp_all add: option.map_comp comp_def option.map_id[unfolded id_def] rel_option_eq rel_option_map1 rel_option_map2 Quotient3_abs_rep [OF assms] Quotient3_rel_rep [OF assms])
  using Quotient3_rel [OF assms]
  apply (simp add: rel_option_iff split: option.split)
  done

declare [[mapQ3 option = (rel_option, option_quotient)]]

lemma option_None_rsp [quot_respect]:
  assumes q: "Quotient3 R Abs Rep"
  shows "rel_option R None None"
  by (rule None_transfer)

lemma option_Some_rsp [quot_respect]:
  assumes q: "Quotient3 R Abs Rep"
  shows "(R ===> rel_option R) Some Some"
  by (rule Some_transfer)

lemma option_None_prs [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "map_option Abs None = None"
  by (rule Option.option.map(1))

lemma option_Some_prs [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "(Rep ---> map_option Abs) Some = Some"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient3_abs_rep[OF q])
  done

end
