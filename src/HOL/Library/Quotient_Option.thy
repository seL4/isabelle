(*  Title:      HOL/Library/Quotient_Option.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the option type *}

theory Quotient_Option
imports Main Quotient_Syntax
begin

fun
  option_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> bool"
where
  "option_rel R None None = True"
| "option_rel R (Some x) None = False"
| "option_rel R None (Some x) = False"
| "option_rel R (Some x) (Some y) = R x y"

lemma option_rel_unfold:
  "option_rel R x y = (case (x, y) of (None, None) \<Rightarrow> True
    | (Some x, Some y) \<Rightarrow> R x y
    | _ \<Rightarrow> False)"
  by (cases x) (cases y, simp_all)+

lemma option_rel_map1:
  "option_rel R (Option.map f x) y \<longleftrightarrow> option_rel (\<lambda>x. R (f x)) x y"
  by (simp add: option_rel_unfold split: option.split)

lemma option_rel_map2:
  "option_rel R x (Option.map f y) \<longleftrightarrow> option_rel (\<lambda>x y. R x (f y)) x y"
  by (simp add: option_rel_unfold split: option.split)

lemma option_map_id [id_simps]:
  "Option.map id = id"
  by (simp add: id_def Option.map.identity fun_eq_iff)

lemma option_rel_eq [id_simps]:
  "option_rel (op =) = (op =)"
  by (simp add: option_rel_unfold fun_eq_iff split: option.split)

lemma option_reflp:
  "reflp R \<Longrightarrow> reflp (option_rel R)"
  by (auto simp add: option_rel_unfold split: option.splits intro!: reflpI elim: reflpE)

lemma option_symp:
  "symp R \<Longrightarrow> symp (option_rel R)"
  by (auto simp add: option_rel_unfold split: option.splits intro!: sympI elim: sympE)

lemma option_transp:
  "transp R \<Longrightarrow> transp (option_rel R)"
  by (auto simp add: option_rel_unfold split: option.splits intro!: transpI elim: transpE)

lemma option_equivp [quot_equiv]:
  "equivp R \<Longrightarrow> equivp (option_rel R)"
  by (blast intro: equivpI option_reflp option_symp option_transp elim: equivpE)

lemma option_quotient [quot_thm]:
  assumes "Quotient R Abs Rep"
  shows "Quotient (option_rel R) (Option.map Abs) (Option.map Rep)"
  apply (rule QuotientI)
  apply (simp_all add: Option.map.compositionality comp_def Option.map.identity option_rel_eq option_rel_map1 option_rel_map2 Quotient_abs_rep [OF assms] Quotient_rel_rep [OF assms])
  using Quotient_rel [OF assms]
  apply (simp add: option_rel_unfold split: option.split)
  done

declare [[map option = (option_rel, option_quotient)]]

lemma option_None_rsp [quot_respect]:
  assumes q: "Quotient R Abs Rep"
  shows "option_rel R None None"
  by simp

lemma option_Some_rsp [quot_respect]:
  assumes q: "Quotient R Abs Rep"
  shows "(R ===> option_rel R) Some Some"
  by auto

lemma option_None_prs [quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "Option.map Abs None = None"
  by simp

lemma option_Some_prs [quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "(Rep ---> Option.map Abs) Some = Some"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient_abs_rep[OF q])
  done

end
