(*  Title:      ZF/typechk
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics for type checking -- from CTT
*)

fun is_rigid_elem (Const("Trueprop",_) $ (Const("op :",_) $ a $ _)) = 
      not (is_Var (head_of a))
  | is_rigid_elem _ = false;

(*Try solving a:A by assumption provided a is rigid!*) 
val test_assume_tac = SUBGOAL(fn (prem,i) =>
    if is_rigid_elem (Logic.strip_assums_concl prem)
    then  assume_tac i  else  eq_assume_tac i);

(*Type checking solves a:?A (a rigid, ?A maybe flexible).  
  match_tac is too strict; would refuse to instantiate ?A*)
fun typechk_step_tac tyrls =
    FIRSTGOAL (test_assume_tac ORELSE' filt_resolve_tac tyrls 3);

fun typechk_tac tyrls = REPEAT (typechk_step_tac tyrls);

val ZF_typechecks =
    [if_type, lam_type, SigmaI, apply_type, split_type, consI1];

(*Instantiates variables in typing conditions.
  drawback: does not simplify conjunctions*)
fun type_auto_tac tyrls hyps = SELECT_GOAL
    (DEPTH_SOLVE (typechk_step_tac (tyrls@hyps)
           ORELSE ares_tac [TrueI,refl,iff_refl,ballI,allI,conjI,impI] 1));

