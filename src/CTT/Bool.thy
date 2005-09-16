(*  Title:      CTT/bool
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header {* The two-element type (booleans and conditionals) *}

theory Bool
imports CTT
uses "~~/src/Provers/typedsimp.ML" "rew.ML"
begin

consts
  Bool        :: "t"
  true        :: "i"
  false       :: "i"
  cond        :: "[i,i,i]=>i"
defs
  Bool_def:   "Bool == T+T"
  true_def:   "true == inl(tt)"
  false_def:  "false == inr(tt)"
  cond_def:   "cond(a,b,c) == when(a, %u. b, %u. c)"

ML {* use_legacy_bindings (the_context ()) *}

end
