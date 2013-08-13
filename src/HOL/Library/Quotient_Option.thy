(*  Title:      HOL/Library/Quotient_Option.thy
    Author:     Cezary Kaliszyk, Christian Urban and Brian Huffman
*)

header {* Quotient infrastructure for the option type *}

theory Quotient_Option
imports Main Quotient_Syntax
begin

subsection {* Relator for option type *}

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

fun option_pred :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "option_pred R None = True"
| "option_pred R (Some x) = R x"

lemma option_pred_unfold:
  "option_pred P x = (case x of None \<Rightarrow> True
    | Some x \<Rightarrow> P x)"
by (cases x) simp_all

lemma option_rel_map1:
  "option_rel R (Option.map f x) y \<longleftrightarrow> option_rel (\<lambda>x. R (f x)) x y"
  by (simp add: option_rel_unfold split: option.split)

lemma option_rel_map2:
  "option_rel R x (Option.map f y) \<longleftrightarrow> option_rel (\<lambda>x y. R x (f y)) x y"
  by (simp add: option_rel_unfold split: option.split)

lemma option_map_id [id_simps]:
  "Option.map id = id"
  by (simp add: id_def Option.map.identity fun_eq_iff)

lemma option_rel_eq [id_simps, relator_eq]:
  "option_rel (op =) = (op =)"
  by (simp add: option_rel_unfold fun_eq_iff split: option.split)

lemma option_rel_mono[relator_mono]:
  assumes "A \<le> B"
  shows "(option_rel A) \<le> (option_rel B)"
using assms by (auto simp: option_rel_unfold split: option.splits)

lemma option_rel_OO[relator_distr]:
  "(option_rel A) OO (option_rel B) = option_rel (A OO B)"
by (rule ext)+ (auto simp: option_rel_unfold OO_def split: option.split)

lemma Domainp_option[relator_domain]:
  assumes "Domainp A = P"
  shows "Domainp (option_rel A) = (option_pred P)"
using assms unfolding Domainp_iff[abs_def] option_rel_unfold[abs_def] option_pred_unfold[abs_def]
by (auto iff: fun_eq_iff split: option.split)

lemma reflp_option_rel[reflexivity_rule]:
  "reflp R \<Longrightarrow> reflp (option_rel R)"
  unfolding reflp_def split_option_all by simp

lemma left_total_option_rel[reflexivity_rule]:
  "left_total R \<Longrightarrow> left_total (option_rel R)"
  unfolding left_total_def split_option_all split_option_ex by simp

lemma left_unique_option_rel [reflexivity_rule]:
  "left_unique R \<Longrightarrow> left_unique (option_rel R)"
  unfolding left_unique_def split_option_all by simp

lemma option_symp:
  "symp R \<Longrightarrow> symp (option_rel R)"
  unfolding symp_def split_option_all option_rel.simps by fast

lemma option_transp:
  "transp R \<Longrightarrow> transp (option_rel R)"
  unfolding transp_def split_option_all option_rel.simps by fast

lemma option_equivp [quot_equiv]:
  "equivp R \<Longrightarrow> equivp (option_rel R)"
  by (blast intro: equivpI reflp_option_rel option_symp option_transp elim: equivpE)

lemma right_total_option_rel [transfer_rule]:
  "right_total R \<Longrightarrow> right_total (option_rel R)"
  unfolding right_total_def split_option_all split_option_ex by simp

lemma right_unique_option_rel [transfer_rule]:
  "right_unique R \<Longrightarrow> right_unique (option_rel R)"
  unfolding right_unique_def split_option_all by simp

lemma bi_total_option_rel [transfer_rule]:
  "bi_total R \<Longrightarrow> bi_total (option_rel R)"
  unfolding bi_total_def split_option_all split_option_ex by simp

lemma bi_unique_option_rel [transfer_rule]:
  "bi_unique R \<Longrightarrow> bi_unique (option_rel R)"
  unfolding bi_unique_def split_option_all by simp

subsection {* Transfer rules for transfer package *}

lemma None_transfer [transfer_rule]: "(option_rel A) None None"
  by simp

lemma Some_transfer [transfer_rule]: "(A ===> option_rel A) Some Some"
  unfolding fun_rel_def by simp

lemma option_case_transfer [transfer_rule]:
  "(B ===> (A ===> B) ===> option_rel A ===> B) option_case option_case"
  unfolding fun_rel_def split_option_all by simp

lemma option_map_transfer [transfer_rule]:
  "((A ===> B) ===> option_rel A ===> option_rel B) Option.map Option.map"
  unfolding Option.map_def by transfer_prover

lemma option_bind_transfer [transfer_rule]:
  "(option_rel A ===> (A ===> option_rel B) ===> option_rel B)
    Option.bind Option.bind"
  unfolding fun_rel_def split_option_all by simp

subsection {* Setup for lifting package *}

lemma Quotient_option[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (option_rel R) (Option.map Abs)
    (Option.map Rep) (option_rel T)"
  using assms unfolding Quotient_alt_def option_rel_unfold
  by (simp split: option.split)

lemma option_invariant_commute [invariant_commute]:
  "option_rel (Lifting.invariant P) = Lifting.invariant (option_pred P)"
  apply (simp add: fun_eq_iff Lifting.invariant_def)
  apply (intro allI) 
  apply (case_tac x rule: option.exhaust)
  apply (case_tac xa rule: option.exhaust)
  apply auto[2]
  apply (case_tac xa rule: option.exhaust)
  apply auto
done

subsection {* Rules for quotient package *}

lemma option_quotient [quot_thm]:
  assumes "Quotient3 R Abs Rep"
  shows "Quotient3 (option_rel R) (Option.map Abs) (Option.map Rep)"
  apply (rule Quotient3I)
  apply (simp_all add: Option.map.compositionality comp_def Option.map.identity option_rel_eq option_rel_map1 option_rel_map2 Quotient3_abs_rep [OF assms] Quotient3_rel_rep [OF assms])
  using Quotient3_rel [OF assms]
  apply (simp add: option_rel_unfold split: option.split)
  done

declare [[mapQ3 option = (option_rel, option_quotient)]]

lemma option_None_rsp [quot_respect]:
  assumes q: "Quotient3 R Abs Rep"
  shows "option_rel R None None"
  by (rule None_transfer)

lemma option_Some_rsp [quot_respect]:
  assumes q: "Quotient3 R Abs Rep"
  shows "(R ===> option_rel R) Some Some"
  by (rule Some_transfer)

lemma option_None_prs [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "Option.map Abs None = None"
  by simp

lemma option_Some_prs [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "(Rep ---> Option.map Abs) Some = Some"
  apply(simp add: fun_eq_iff)
  apply(simp add: Quotient3_abs_rep[OF q])
  done

end
