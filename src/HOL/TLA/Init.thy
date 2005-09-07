(*
    File:        TLA/Init.thy
    ID:          $Id$
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

    Theory Name: Init
    Logic Image: HOL

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

ML {* use_legacy_bindings (the_context ()) *}

end
