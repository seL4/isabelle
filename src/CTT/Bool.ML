(*  Title:      CTT/Bool
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The two-element type (booleans and conditionals)
*)

val bool_defs = [Bool_def,true_def,false_def,cond_def];

(*Derivation of rules for the type Bool*)

(*formation rule*)
Goalw bool_defs "Bool type";
by (typechk_tac []) ;
qed "boolF";


(*introduction rules for true, false*)

Goalw bool_defs "true : Bool";
by (typechk_tac []) ;
qed "boolI_true";

Goalw bool_defs "false : Bool";
by (typechk_tac []) ;
qed "boolI_false";

(*elimination rule: typing of cond*)
Goalw bool_defs 
    "[| p:Bool;  a : C(true);  b : C(false) |] ==> cond(p,a,b) : C(p)";
by (typechk_tac []);
by (ALLGOALS (etac TE));
by (typechk_tac []) ;
qed "boolE";

Goalw bool_defs
    "[| p = q : Bool;  a = c : C(true);  b = d : C(false) |] \
\    ==> cond(p,a,b) = cond(q,c,d) : C(p)";
by (rtac PlusEL 1);
by (REPEAT (eresolve_tac [asm_rl, refl_elem RS TEL] 1)) ;
qed "boolEL";

(*computation rules for true, false*)

Goalw bool_defs 
    "[| a : C(true);  b : C(false) |] ==> cond(true,a,b) = a : C(true)";
by (resolve_tac comp_rls 1);
by (typechk_tac []);
by (ALLGOALS (etac TE));
by (typechk_tac []) ;
qed "boolC_true";

Goalw bool_defs
    "[| a : C(true);  b : C(false) |] ==> cond(false,a,b) = b : C(false)";
by (resolve_tac comp_rls 1);
by (typechk_tac []);
by (ALLGOALS (etac TE));
by (typechk_tac []) ;
qed "boolC_false";

writeln"Reached end of file.";

