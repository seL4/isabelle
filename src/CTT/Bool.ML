(*  Title:      CTT/bool
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Theorems for bool.thy (booleans and conditionals)
*)

open Bool;

val bool_defs = [Bool_def,true_def,false_def,cond_def];

(*Derivation of rules for the type Bool*)

(*formation rule*)
qed_goalw "boolF" Bool.thy bool_defs 
    "Bool type"
 (fn _ => [ (typechk_tac []) ]);


(*introduction rules for true, false*)

qed_goalw "boolI_true" Bool.thy bool_defs 
    "true : Bool"
 (fn _ => [ (typechk_tac []) ]);

qed_goalw "boolI_false" Bool.thy bool_defs 
    "false : Bool"
 (fn _ => [ (typechk_tac []) ]);

(*elimination rule: typing of cond*)
qed_goalw "boolE" Bool.thy bool_defs 
    "!!C. [| p:Bool;  a : C(true);  b : C(false) |] ==> cond(p,a,b) : C(p)"
 (fn _ =>
  [ (typechk_tac []),
    (ALLGOALS (etac TE)),
    (typechk_tac []) ]);

qed_goalw "boolEL" Bool.thy bool_defs 
    "!!C. [| p = q : Bool;  a = c : C(true);  b = d : C(false) |] ==> \
\         cond(p,a,b) = cond(q,c,d) : C(p)"
 (fn _ =>
  [ (rtac PlusEL 1),
    (REPEAT (eresolve_tac [asm_rl, refl_elem RS TEL] 1)) ]);

(*computation rules for true, false*)

qed_goalw "boolC_true" Bool.thy bool_defs 
    "!!C. [| a : C(true);  b : C(false) |] ==> cond(true,a,b) = a : C(true)"
 (fn _ =>
  [ (resolve_tac comp_rls 1),
    (typechk_tac []),
    (ALLGOALS (etac TE)),
    (typechk_tac []) ]);

qed_goalw "boolC_false" Bool.thy bool_defs 
    "!!C. [| a : C(true);  b : C(false) |] ==> cond(false,a,b) = b : C(false)"
 (fn _ =>
  [ (resolve_tac comp_rls 1),
    (typechk_tac []),
    (ALLGOALS (etac TE)),
    (typechk_tac []) ]);

writeln"Reached end of file.";

