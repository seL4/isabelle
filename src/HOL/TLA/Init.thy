(*
    File:        TLA/Init.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

Introduces type of temporal formulas. Defines interface between
temporal formulas and its "subformulas" (state predicates and actions).
*)

theory Init
imports Action
begin

typedecl behavior
instance behavior :: world ..

types
  temporal = "behavior form"


consts
  Initial     :: "('w::world => bool) => temporal"
  first_world :: "behavior => ('w::world)"
  st1         :: "behavior => state"
  st2         :: "behavior => state"

syntax
  TEMP       :: "lift => 'a"                          ("(TEMP _)")
  "_Init"    :: "lift => lift"                        ("(Init _)"[40] 50)

translations
  "TEMP F"   => "(F::behavior => _)"
  "_Init"    == "Initial"
  "sigma |= Init F"  <= "_Init F sigma"

defs
  Init_def:    "sigma |= Init F  ==  (first_world sigma) |= F"
  fw_temp_def: "first_world == %sigma. sigma"
  fw_stp_def:  "first_world == st1"
  fw_act_def:  "first_world == %sigma. (st1 sigma, st2 sigma)"

lemma const_simps [int_rewrite, simp]:
  "|- (Init #True) = #True"
  "|- (Init #False) = #False"
  by (auto simp: Init_def)

lemma Init_simps [int_rewrite]:
  "!!F. |- (Init ~F) = (~ Init F)"
  "|- (Init (P --> Q)) = (Init P --> Init Q)"
  "|- (Init (P & Q)) = (Init P & Init Q)"
  "|- (Init (P | Q)) = (Init P | Init Q)"
  "|- (Init (P = Q)) = ((Init P) = (Init Q))"
  "|- (Init (!x. F x)) = (!x. (Init F x))"
  "|- (Init (? x. F x)) = (? x. (Init F x))"
  "|- (Init (?! x. F x)) = (?! x. (Init F x))"
  by (auto simp: Init_def)

lemma Init_stp_act: "|- (Init $P) = (Init P)"
  by (auto simp add: Init_def fw_act_def fw_stp_def)

lemmas Init_simps = Init_stp_act [int_rewrite] Init_simps
lemmas Init_stp_act_rev = Init_stp_act [int_rewrite, symmetric]

lemma Init_temp: "|- (Init F) = F"
  by (auto simp add: Init_def fw_temp_def)

lemmas Init_simps = Init_temp [int_rewrite] Init_simps

(* Trivial instances of the definitions that avoid introducing lambda expressions. *)
lemma Init_stp: "(sigma |= Init P) = P (st1 sigma)"
  by (simp add: Init_def fw_stp_def)

lemma Init_act: "(sigma |= Init A) = A (st1 sigma, st2 sigma)"
  by (simp add: Init_def fw_act_def)

lemmas Init_defs = Init_stp Init_act Init_temp [int_use]

end
