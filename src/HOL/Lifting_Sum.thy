(*  Title:      HOL/Lifting_Sum.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

header {* Setup for Lifting/Transfer for the sum type *}

theory Lifting_Sum
imports Lifting Basic_BNFs
begin

subsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

lemma Inl_transfer [transfer_rule]: "(A ===> rel_sum A B) Inl Inl"
  unfolding rel_fun_def by simp

lemma Inr_transfer [transfer_rule]: "(B ===> rel_sum A B) Inr Inr"
  unfolding rel_fun_def by simp

lemma case_sum_transfer [transfer_rule]:
  "((A ===> C) ===> (B ===> C) ===> rel_sum A B ===> C) case_sum case_sum"
  unfolding rel_fun_def rel_sum_def by (simp split: sum.split)

end

end
