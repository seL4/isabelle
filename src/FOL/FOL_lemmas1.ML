(*  Title:      FOL/FOL_lemmas1.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics and lemmas for theory FOL (classical First-Order Logic).
*)

val classical = thm "classical";
bind_thm ("ccontr", FalseE RS classical);


(*** Classical introduction rules for | and EX ***)

qed_goal "disjCI" (the_context ()) 
   "(~Q ==> P) ==> P|Q"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[disjI1,notI]) 1)),
    (REPEAT (ares_tac (prems@[disjI2,notE]) 1)) ]);

(*introduction rule involving only EX*)
qed_goal "ex_classical" (the_context ()) 
   "( ~(EX x. P(x)) ==> P(a)) ==> EX x. P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (eresolve_tac (prems RL [exI]) 1) ]);

(*version of above, simplifying ~EX to ALL~ *)
qed_goal "exCI" (the_context ()) 
   "(ALL x. ~P(x) ==> P(a)) ==> EX x. P(x)"
 (fn [prem]=>
  [ (rtac ex_classical 1),
    (resolve_tac [notI RS allI RS prem] 1),
    (etac notE 1),
    (etac exI 1) ]);

qed_goal "excluded_middle" (the_context ()) "~P | P"
 (fn _=> [ rtac disjCI 1, assume_tac 1 ]);

(*For disjunctive case analysis*)
fun excluded_middle_tac sP =
    res_inst_tac [("Q",sP)] (excluded_middle RS disjE);

qed_goal "case_split_thm" (the_context ()) "[| P ==> Q; ~P ==> Q |] ==> Q"
  (fn [p1,p2] => [rtac (excluded_middle RS disjE) 1,
                  etac p2 1, etac p1 1]);

(*HOL's more natural case analysis tactic*)
fun case_tac a = res_inst_tac [("P",a)] case_split_thm;


(*** Special elimination rules *)


(*Classical implies (-->) elimination. *)
qed_goal "impCE" (the_context ()) 
    "[| P-->Q;  ~P ==> R;  Q ==> R |] ==> R"
 (fn major::prems=>
  [ (resolve_tac [excluded_middle RS disjE] 1),
    (DEPTH_SOLVE (ares_tac (prems@[major RS mp]) 1)) ]);

(*This version of --> elimination works on Q before P.  It works best for
  those cases in which P holds "almost everywhere".  Can't install as
  default: would break old proofs.*)
qed_goal "impCE'" (the_context ()) 
    "[| P-->Q;  Q ==> R;  ~P ==> R |] ==> R"
 (fn major::prems=>
  [ (resolve_tac [excluded_middle RS disjE] 1),
    (DEPTH_SOLVE (ares_tac (prems@[major RS mp]) 1)) ]);

(*Double negation law*)
qed_goal "notnotD" (the_context ()) "~~P ==> P"
 (fn [major]=>
  [ (rtac classical 1), (eresolve_tac [major RS notE] 1) ]);

qed_goal "contrapos2" (the_context ()) "[| Q; ~ P ==> ~ Q |] ==> P" (fn [p1,p2] => [
        rtac classical 1,
        dtac p2 1,
        etac notE 1,
        rtac p1 1]);

(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in 
    ~P ==> ~Q    and    P ==> Q  *)
qed_goalw "iffCE" (the_context ()) [iff_def]
    "[| P<->Q;  [| P; Q |] ==> R;  [| ~P; ~Q |] ==> R |] ==> R"
 (fn prems =>
  [ (rtac conjE 1),
    (REPEAT (DEPTH_SOLVE_1 
        (etac impCE 1  ORELSE  mp_tac 1  ORELSE  ares_tac prems 1))) ]);
