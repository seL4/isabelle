(*  Title:      HOL/IOA/Asig.thy
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen
*)

section \<open>Action signatures\<close>

theory Asig
imports Main
begin

type_synonym 'a signature = "('a set * 'a set * 'a set)"

definition "inputs" :: "'action signature => 'action set"
  where asig_inputs_def: "inputs == fst"

definition "outputs" :: "'action signature => 'action set"
  where asig_outputs_def: "outputs == (fst o snd)"

definition "internals" :: "'action signature => 'action set"
  where asig_internals_def: "internals == (snd o snd)"

definition "actions" :: "'action signature => 'action set"
  where actions_def: "actions(asig) == (inputs(asig) Un outputs(asig) Un internals(asig))"

definition externals :: "'action signature => 'action set"
  where externals_def: "externals(asig) == (inputs(asig) Un outputs(asig))"

definition is_asig :: "'action signature => bool"
  where "is_asig(triple) ==
    ((inputs(triple) Int outputs(triple) = {})    &
     (outputs(triple) Int internals(triple) = {}) &
     (inputs(triple) Int internals(triple) = {}))"

definition mk_ext_asig :: "'action signature => 'action signature"
  where "mk_ext_asig(triple) == (inputs(triple), outputs(triple), {})"


lemmas asig_projections = asig_inputs_def asig_outputs_def asig_internals_def

lemma int_and_ext_is_act: "[| a~:internals(S) ;a~:externals(S)|] ==> a~:actions(S)"
  apply (simp add: externals_def actions_def)
  done

lemma ext_is_act: "[|a:externals(S)|] ==> a:actions(S)"
  apply (simp add: externals_def actions_def)
  done

end
