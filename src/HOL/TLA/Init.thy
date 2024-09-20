(*  Title:      HOL/TLA/Init.thy
    Author:     Stephan Merz
    Copyright:  1998 University of Munich

Introduces type of temporal formulas.  Defines interface between
temporal formulas and its "subformulas" (state predicates and
actions).
*)

theory Init
imports Action
begin

typedecl behavior
instance behavior :: world ..

type_synonym temporal = "behavior form"

consts
  first_world :: "behavior \<Rightarrow> ('w::world)"
  st1         :: "behavior \<Rightarrow> state"
  st2         :: "behavior \<Rightarrow> state"

definition Initial :: "('w::world \<Rightarrow> bool) \<Rightarrow> temporal"
  where Init_def: "Initial F sigma = F (first_world sigma)"

syntax
  "_TEMP"    :: "lift \<Rightarrow> 'a"                          (\<open>(TEMP _)\<close>)
  "_Init"    :: "lift \<Rightarrow> lift"                        (\<open>(Init _)\<close>[40] 50)
translations
  "TEMP F"   => "(F::behavior \<Rightarrow> _)"
  "_Init"    == "CONST Initial"
  "sigma \<Turnstile> Init F"  <= "_Init F sigma"

overloading
  fw_temp \<equiv> "first_world :: behavior \<Rightarrow> behavior"
  fw_stp \<equiv> "first_world :: behavior \<Rightarrow> state"
  fw_act \<equiv> "first_world :: behavior \<Rightarrow> state \<times> state"
begin

definition "first_world == \<lambda>sigma. sigma"
definition "first_world == st1"
definition "first_world == \<lambda>sigma. (st1 sigma, st2 sigma)"

end

lemma const_simps [int_rewrite, simp]:
  "\<turnstile> (Init #True) = #True"
  "\<turnstile> (Init #False) = #False"
  by (auto simp: Init_def)

lemma Init_simps1 [int_rewrite]:
  "\<And>F. \<turnstile> (Init \<not>F) = (\<not> Init F)"
  "\<turnstile> (Init (P \<longrightarrow> Q)) = (Init P \<longrightarrow> Init Q)"
  "\<turnstile> (Init (P \<and> Q)) = (Init P \<and> Init Q)"
  "\<turnstile> (Init (P \<or> Q)) = (Init P \<or> Init Q)"
  "\<turnstile> (Init (P = Q)) = ((Init P) = (Init Q))"
  "\<turnstile> (Init (\<forall>x. F x)) = (\<forall>x. (Init F x))"
  "\<turnstile> (Init (\<exists>x. F x)) = (\<exists>x. (Init F x))"
  "\<turnstile> (Init (\<exists>!x. F x)) = (\<exists>!x. (Init F x))"
  by (auto simp: Init_def)

lemma Init_stp_act: "\<turnstile> (Init $P) = (Init P)"
  by (auto simp add: Init_def fw_act_def fw_stp_def)

lemmas Init_simps2 = Init_stp_act [int_rewrite] Init_simps1
lemmas Init_stp_act_rev = Init_stp_act [int_rewrite, symmetric]

lemma Init_temp: "\<turnstile> (Init F) = F"
  by (auto simp add: Init_def fw_temp_def)

lemmas Init_simps = Init_temp [int_rewrite] Init_simps2

(* Trivial instances of the definitions that avoid introducing lambda expressions. *)
lemma Init_stp: "(sigma \<Turnstile> Init P) = P (st1 sigma)"
  by (simp add: Init_def fw_stp_def)

lemma Init_act: "(sigma \<Turnstile> Init A) = A (st1 sigma, st2 sigma)"
  by (simp add: Init_def fw_act_def)

lemmas Init_defs = Init_stp Init_act Init_temp [int_use]

end
