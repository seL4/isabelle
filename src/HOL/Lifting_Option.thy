(*  Title:      HOL/Lifting_Option.thy
    Author:     Brian Huffman and Ondrej Kuncar
    Author:     Andreas Lochbihler, Karlsruhe Institute of Technology
*)

header {* Setup for Lifting/Transfer for the option type *}

theory Lifting_Option
imports Lifting Option
begin

subsection {* Relator and predicator properties *}

lemma rel_option_iff:
  "rel_option R x y = (case (x, y) of (None, None) \<Rightarrow> True
    | (Some x, Some y) \<Rightarrow> R x y
    | _ \<Rightarrow> False)"
by (auto split: prod.split option.split)

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
