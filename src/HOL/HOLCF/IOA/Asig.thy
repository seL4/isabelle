(*  Title:      HOL/HOLCF/IOA/Asig.thy
    Author:     Olaf Müller, Tobias Nipkow & Konrad Slind
*)

section \<open>Action signatures\<close>

theory Asig
imports Main
begin

type_synonym 'a signature = "'a set \<times> 'a set \<times> 'a set"

definition inputs :: "'action signature \<Rightarrow> 'action set"
  where asig_inputs_def: "inputs = fst"

definition outputs :: "'action signature \<Rightarrow> 'action set"
  where asig_outputs_def: "outputs = fst \<circ> snd"

definition internals :: "'action signature \<Rightarrow> 'action set"
  where asig_internals_def: "internals = snd \<circ> snd"

definition actions :: "'action signature \<Rightarrow> 'action set"
  where "actions asig = inputs asig \<union> outputs asig \<union> internals asig"

definition externals :: "'action signature \<Rightarrow> 'action set"
  where "externals asig = inputs asig \<union> outputs asig"

definition locals :: "'action signature \<Rightarrow> 'action set"
  where "locals asig = internals asig \<union> outputs asig"

definition is_asig :: "'action signature \<Rightarrow> bool"
  where "is_asig triple \<longleftrightarrow>
    inputs triple \<inter> outputs triple = {} \<and>
    outputs triple \<inter> internals triple = {} \<and>
    inputs triple \<inter> internals triple = {}"

definition mk_ext_asig :: "'action signature \<Rightarrow> 'action signature"
  where "mk_ext_asig triple = (inputs triple, outputs triple, {})"


lemmas asig_projections = asig_inputs_def asig_outputs_def asig_internals_def

lemma asig_triple_proj:
  "outputs (a, b, c) = b \<and>
   inputs (a, b, c) = a \<and>
   internals (a, b, c) = c"
  by (simp add: asig_projections)

lemma int_and_ext_is_act: "a \<notin> internals S \<Longrightarrow> a \<notin> externals S \<Longrightarrow> a \<notin> actions S"
  by (simp add: externals_def actions_def)

lemma ext_is_act: "a \<in> externals S \<Longrightarrow> a \<in> actions S"
  by (simp add: externals_def actions_def)

lemma int_is_act: "a \<in> internals S \<Longrightarrow> a \<in> actions S"
  by (simp add: asig_internals_def actions_def)

lemma inp_is_act: "a \<in> inputs S \<Longrightarrow> a \<in> actions S"
  by (simp add: asig_inputs_def actions_def)

lemma out_is_act: "a \<in> outputs S \<Longrightarrow> a \<in> actions S"
  by (simp add: asig_outputs_def actions_def)

lemma ext_and_act: "x \<in> actions S \<and> x \<in> externals S \<longleftrightarrow> x \<in> externals S"
  by (fast intro!: ext_is_act)

lemma not_ext_is_int: "is_asig S \<Longrightarrow> x \<in> actions S \<Longrightarrow> x \<notin> externals S \<longleftrightarrow> x \<in> internals S"
  by (auto simp add: actions_def is_asig_def externals_def)

lemma not_ext_is_int_or_not_act: "is_asig S \<Longrightarrow> x \<notin> externals S \<longleftrightarrow> x \<in> internals S \<or> x \<notin> actions S"
  by (auto simp add: actions_def is_asig_def externals_def)

lemma int_is_not_ext:"is_asig S \<Longrightarrow> x \<in> internals S \<Longrightarrow> x \<notin> externals S"
  by (auto simp add: externals_def actions_def is_asig_def)

end
