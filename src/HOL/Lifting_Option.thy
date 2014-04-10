(*  Title:      HOL/Lifting_Option.thy
    Author:     Brian Huffman and Ondrej Kuncar
    Author:     Andreas Lochbihler, Karlsruhe Institute of Technology
*)

header {* Setup for Lifting/Transfer for the option type *}

theory Lifting_Option
imports Lifting Partial_Function
begin

subsection {* Relator and predicator properties *}

lemma rel_option_iff:
  "rel_option R x y = (case (x, y) of (None, None) \<Rightarrow> True
    | (Some x, Some y) \<Rightarrow> R x y
    | _ \<Rightarrow> False)"
by (auto split: prod.split option.split)

abbreviation (input) pred_option :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
  "pred_option \<equiv> case_option True"

lemma rel_option_eq [relator_eq]:
  "rel_option (op =) = (op =)"
  by (simp add: rel_option_iff fun_eq_iff split: option.split)

lemma rel_option_mono[relator_mono]:
  assumes "A \<le> B"
  shows "(rel_option A) \<le> (rel_option B)"
using assms by (auto simp: rel_option_iff split: option.splits)

lemma rel_option_OO[relator_distr]:
  "(rel_option A) OO (rel_option B) = rel_option (A OO B)"
by (rule ext)+ (auto simp: rel_option_iff OO_def split: option.split)

lemma Domainp_option[relator_domain]: 
  "Domainp (rel_option A) = (pred_option (Domainp A))"
unfolding Domainp_iff[abs_def] rel_option_iff[abs_def]
by (auto iff: fun_eq_iff split: option.split)

lemma left_total_rel_option[transfer_rule]:
  "left_total R \<Longrightarrow> left_total (rel_option R)"
  unfolding left_total_def split_option_all split_option_ex by simp

lemma left_unique_rel_option [transfer_rule]:
  "left_unique R \<Longrightarrow> left_unique (rel_option R)"
  unfolding left_unique_def split_option_all by simp

lemma right_total_rel_option [transfer_rule]:
  "right_total R \<Longrightarrow> right_total (rel_option R)"
  unfolding right_total_def split_option_all split_option_ex by simp

lemma right_unique_rel_option [transfer_rule]:
  "right_unique R \<Longrightarrow> right_unique (rel_option R)"
  unfolding right_unique_def split_option_all by simp

lemma bi_total_rel_option [transfer_rule]:
  "bi_total R \<Longrightarrow> bi_total (rel_option R)"
  unfolding bi_total_def split_option_all split_option_ex by simp

lemma bi_unique_rel_option [transfer_rule]:
  "bi_unique R \<Longrightarrow> bi_unique (rel_option R)"
  unfolding bi_unique_def split_option_all by simp

lemma option_relator_eq_onp [relator_eq_onp]:
  "rel_option (eq_onp P) = eq_onp (pred_option P)"
  by (auto simp add: fun_eq_iff eq_onp_def split_option_all)

subsection {* Quotient theorem for the Lifting package *}

lemma Quotient_option[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (rel_option R) (map_option Abs)
    (map_option Rep) (rel_option T)"
  using assms unfolding Quotient_alt_def rel_option_iff
  by (simp split: option.split)

subsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

lemma None_transfer [transfer_rule]: "(rel_option A) None None"
  by (rule option.rel_inject)

lemma Some_transfer [transfer_rule]: "(A ===> rel_option A) Some Some"
  unfolding rel_fun_def by simp

lemma case_option_transfer [transfer_rule]:
  "(B ===> (A ===> B) ===> rel_option A ===> B) case_option case_option"
  unfolding rel_fun_def split_option_all by simp

lemma map_option_transfer [transfer_rule]:
  "((A ===> B) ===> rel_option A ===> rel_option B) map_option map_option"
  unfolding map_option_case[abs_def] by transfer_prover

lemma option_bind_transfer [transfer_rule]:
  "(rel_option A ===> (A ===> rel_option B) ===> rel_option B)
    Option.bind Option.bind"
  unfolding rel_fun_def split_option_all by simp

end

end
