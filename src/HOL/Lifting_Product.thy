(*  Title:      HOL/Lifting_Product.thy
    Author:     Brian Huffman and Ondrej Kuncar
*)

header {* Setup for Lifting/Transfer for the product type *}

theory Lifting_Product
imports Lifting Basic_BNFs
begin

(* The following lemma can be deleted when product is added to FP sugar *)
lemma prod_pred_inject [simp]:
  "pred_prod P1 P2 (a, b) = (P1 a \<and> P2 b)"
  unfolding pred_prod_def fun_eq_iff prod_set_simps by blast

subsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

declare Pair_transfer [transfer_rule]
declare fst_transfer [transfer_rule]
declare snd_transfer [transfer_rule]
declare case_prod_transfer [transfer_rule]

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
