(*  Title:      HOL/IOA/Asig.thy
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen
*)

section \<open>Action signatures\<close>

theory Asig
imports Main
begin

type_synonym 'a signature = "('a set \<times> 'a set \<times> 'a set)"

definition "inputs" :: "'action signature \<Rightarrow> 'action set"
  where asig_inputs_def: "inputs \<equiv> fst"

definition "outputs" :: "'action signature \<Rightarrow> 'action set"
  where asig_outputs_def: "outputs \<equiv> (fst \<circ> snd)"

definition "internals" :: "'action signature \<Rightarrow> 'action set"
  where asig_internals_def: "internals \<equiv> (snd \<circ> snd)"

definition "actions" :: "'action signature \<Rightarrow> 'action set"
  where actions_def: "actions(asig) \<equiv> (inputs(asig) \<union> outputs(asig) \<union> internals(asig))"

definition externals :: "'action signature \<Rightarrow> 'action set"
  where externals_def: "externals(asig) \<equiv> (inputs(asig) \<union> outputs(asig))"

definition is_asig :: "'action signature => bool"
  where "is_asig(triple) \<equiv>
    ((inputs(triple) \<inter> outputs(triple) = {})    \<and>
     (outputs(triple) \<inter> internals(triple) = {}) \<and>
     (inputs(triple) \<inter> internals(triple) = {}))"

definition mk_ext_asig :: "'action signature \<Rightarrow> 'action signature"
  where "mk_ext_asig(triple) \<equiv> (inputs(triple), outputs(triple), {})"


lemmas asig_projections = asig_inputs_def asig_outputs_def asig_internals_def

lemma int_and_ext_is_act: "\<lbrakk>a\<notin>internals(S); a\<notin>externals(S)\<rbrakk> \<Longrightarrow> a\<notin>actions(S)"
  apply (simp add: externals_def actions_def)
  done

lemma ext_is_act: "a\<in>externals(S) \<Longrightarrow> a\<in>actions(S)"
  apply (simp add: externals_def actions_def)
  done

end
