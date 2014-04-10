(*  Title:      HOL/Lifting_Product.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

header {* Setup for Lifting/Transfer for the product type *}

theory Lifting_Product
imports Lifting Basic_BNFs
begin

subsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

lemma Pair_transfer [transfer_rule]: "(A ===> B ===> rel_prod A B) Pair Pair"
  unfolding rel_fun_def rel_prod_def by simp

lemma fst_transfer [transfer_rule]: "(rel_prod A B ===> A) fst fst"
  unfolding rel_fun_def rel_prod_def by simp

lemma snd_transfer [transfer_rule]: "(rel_prod A B ===> B) snd snd"
  unfolding rel_fun_def rel_prod_def by simp

lemma case_prod_transfer [transfer_rule]:
  "((A ===> B ===> C) ===> rel_prod A B ===> C) case_prod case_prod"
  unfolding rel_fun_def rel_prod_def by simp

lemma curry_transfer [transfer_rule]:
  "((rel_prod A B ===> C) ===> A ===> B ===> C) curry curry"
  unfolding curry_def by transfer_prover

lemma map_prod_transfer [transfer_rule]:
  "((A ===> C) ===> (B ===> D) ===> rel_prod A B ===> rel_prod C D)
    map_prod map_prod"
  unfolding map_prod_def [abs_def] by transfer_prover

lemma rel_prod_transfer [transfer_rule]:
  "((A ===> B ===> op =) ===> (C ===> D ===> op =) ===>
    rel_prod A C ===> rel_prod B D ===> op =) rel_prod rel_prod"
  unfolding rel_fun_def by auto

end

end
