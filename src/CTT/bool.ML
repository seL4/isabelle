(*  Title: 	CTT/bool
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Theorems for bool.thy (booleans and conditionals)
*)

open Bool;

val bool_defs = [Bool_def,true_def,false_def,cond_def];

(*Derivation of rules for the type Bool*)

(*formation rule*)
val boolF = prove_goal Bool.thy 
    "Bool type"
 (fn prems=>
  [ (rewrite_goals_tac bool_defs),
    (typechk_tac[]) ]);


(*introduction rules for true, false*)

val boolI_true = prove_goal Bool.thy 
    "true : Bool"
 (fn prems=>
  [ (rewrite_goals_tac bool_defs),
    (typechk_tac[]) ]);

val boolI_false = prove_goal Bool.thy 
    "false : Bool"
 (fn prems=>
  [ (rewrite_goals_tac bool_defs),
    (typechk_tac[]) ]);

(*elimination rule: typing of cond*)
val boolE = prove_goal Bool.thy 
    "[| p:Bool;  a : C(true);  b : C(false) |] ==> cond(p,a,b) : C(p)"
 (fn prems=>
  [ (cut_facts_tac prems 1),
    (rewrite_goals_tac bool_defs),
    (typechk_tac prems),
    (ALLGOALS (etac TE)),
    (typechk_tac prems) ]);

val boolEL = prove_goal Bool.thy 
    "[| p = q : Bool;  a = c : C(true);  b = d : C(false) |] ==> \
\    cond(p,a,b) = cond(q,c,d) : C(p)"
 (fn prems=>
  [ (cut_facts_tac prems 1),
    (rewrite_goals_tac bool_defs),
    (resolve_tac [PlusEL] 1),
    (REPEAT (eresolve_tac [asm_rl, refl_elem RS TEL] 1)) ]);

(*computation rules for true, false*)

val boolC_true = prove_goal Bool.thy 
    "[| a : C(true);  b : C(false) |] ==> cond(true,a,b) = a : C(true)"
 (fn prems=>
  [ (cut_facts_tac prems 1),
    (rewrite_goals_tac bool_defs),
    (resolve_tac comp_rls 1),
    (typechk_tac[]),
    (ALLGOALS (etac TE)),
    (typechk_tac prems) ]);

val boolC_false = prove_goal Bool.thy 
    "[| a : C(true);  b : C(false) |] ==> cond(false,a,b) = b : C(false)"
 (fn prems=>
  [ (cut_facts_tac prems 1),
    (rewrite_goals_tac bool_defs),
    (resolve_tac comp_rls 1),
    (typechk_tac[]),
    (ALLGOALS (etac TE)),
    (typechk_tac prems) ]);

writeln"Reached end of file.";

