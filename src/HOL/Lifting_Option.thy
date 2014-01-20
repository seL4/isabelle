(*  Title:      HOL/Lifting_Option.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

header {* Setup for Lifting/Transfer for the option type *}

theory Lifting_Option
imports Lifting Partial_Function
begin

subsection {* Relator and predicator properties *}

definition
  option_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> bool"
where
  "option_rel R x y = (case (x, y) of (None, None) \<Rightarrow> True
    | (Some x, Some y) \<Rightarrow> R x y
    | _ \<Rightarrow> False)"

lemma option_rel_simps[simp]:
  "option_rel R None None = True"
  "option_rel R (Some x) None = False"
  "option_rel R None (Some y) = False"
  "option_rel R (Some x) (Some y) = R x y"
  unfolding option_rel_def by simp_all

abbreviation (input) option_pred :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
  "option_pred \<equiv> option_case True"

lemma option_rel_eq [relator_eq]:
  "option_rel (op =) = (op =)"
  by (simp add: option_rel_def fun_eq_iff split: option.split)

lemma option_rel_mono[relator_mono]:
  assumes "A \<le> B"
  shows "(option_rel A) \<le> (option_rel B)"
using assms by (auto simp: option_rel_def split: option.splits)

lemma option_rel_OO[relator_distr]:
  "(option_rel A) OO (option_rel B) = option_rel (A OO B)"
by (rule ext)+ (auto simp: option_rel_def OO_def split: option.split)

lemma Domainp_option[relator_domain]:
  assumes "Domainp A = P"
  shows "Domainp (option_rel A) = (option_pred P)"
using assms unfolding Domainp_iff[abs_def] option_rel_def[abs_def]
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

lemma option_invariant_commute [invariant_commute]:
  "option_rel (Lifting.invariant P) = Lifting.invariant (option_pred P)"
  by (auto simp add: fun_eq_iff Lifting.invariant_def split_option_all)

subsection {* Quotient theorem for the Lifting package *}

lemma Quotient_option[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (option_rel R) (Option.map Abs)
    (Option.map Rep) (option_rel T)"
  using assms unfolding Quotient_alt_def option_rel_def
  by (simp split: option.split)

subsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

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

end

end
