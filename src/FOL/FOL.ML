(*  Title:      FOL/FOL.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics and lemmas for FOL.thy (classical First-Order Logic)
*)

open FOL;


val ccontr = FalseE RS classical;

(*** Classical introduction rules for | and EX ***)

qed_goal "disjCI" FOL.thy 
   "(~Q ==> P) ==> P|Q"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[disjI1,notI]) 1)),
    (REPEAT (ares_tac (prems@[disjI2,notE]) 1)) ]);

(*introduction rule involving only EX*)
qed_goal "ex_classical" FOL.thy 
   "( ~(EX x. P(x)) ==> P(a)) ==> EX x.P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (eresolve_tac (prems RL [exI]) 1) ]);

(*version of above, simplifying ~EX to ALL~ *)
qed_goal "exCI" FOL.thy 
   "(ALL x. ~P(x) ==> P(a)) ==> EX x.P(x)"
 (fn [prem]=>
  [ (rtac ex_classical 1),
    (resolve_tac [notI RS allI RS prem] 1),
    (etac notE 1),
    (etac exI 1) ]);

qed_goal "excluded_middle" FOL.thy "~P | P"
 (fn _=> [ rtac disjCI 1, assume_tac 1 ]);

(*For disjunctive case analysis*)
fun excluded_middle_tac sP =
    res_inst_tac [("Q",sP)] (excluded_middle RS disjE);

(*** Special elimination rules *)


(*Classical implies (-->) elimination. *)
qed_goal "impCE" FOL.thy 
    "[| P-->Q;  ~P ==> R;  Q ==> R |] ==> R"
 (fn major::prems=>
  [ (resolve_tac [excluded_middle RS disjE] 1),
    (DEPTH_SOLVE (ares_tac (prems@[major RS mp]) 1)) ]);

(*Double negation law*)
qed_goal "notnotD" FOL.thy "~~P ==> P"
 (fn [major]=>
  [ (rtac classical 1), (eresolve_tac [major RS notE] 1) ]);


(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in 
    ~P ==> ~Q    and    P ==> Q  *)
qed_goalw "iffCE" FOL.thy [iff_def]
    "[| P<->Q;  [| P; Q |] ==> R;  [| ~P; ~Q |] ==> R |] ==> R"
 (fn prems =>
  [ (rtac conjE 1),
    (REPEAT (DEPTH_SOLVE_1 
        (etac impCE 1  ORELSE  mp_tac 1  ORELSE  ares_tac prems 1))) ]);


(*Thus, assignments to the references claset and simpset are recorded
  with theory "FOL".  These files cannot be loaded directly in ROOT.ML.*)
use "cladata.ML";
use "simpdata.ML";
