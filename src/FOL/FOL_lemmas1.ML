(*  Title:      FOL/FOL_lemmas1.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics and lemmas for theory FOL (classical First-Order Logic).
*)

val classical = thm "classical";
bind_thm ("ccontr", FalseE RS classical);


(*** Classical introduction rules for | and EX ***)

val prems = Goal "(~Q ==> P) ==> P|Q";
by (rtac classical 1);
by (REPEAT (ares_tac (prems@[disjI1,notI]) 1));
by (REPEAT (ares_tac (prems@[disjI2,notE]) 1)) ;
qed "disjCI";

(*introduction rule involving only EX*)
val prems = Goal "( ~(EX x. P(x)) ==> P(a)) ==> EX x. P(x)";
by (rtac classical 1);
by (eresolve_tac (prems RL [exI]) 1) ;
qed "ex_classical";

(*version of above, simplifying ~EX to ALL~ *)
val [prem]= Goal "(ALL x. ~P(x) ==> P(a)) ==> EX x. P(x)";
by (rtac ex_classical 1);
by (resolve_tac [notI RS allI RS prem] 1);
by (etac notE 1);
by (etac exI 1) ;
qed "exCI";

Goal"~P | P";
by (rtac disjCI 1);
by (assume_tac 1) ;
qed "excluded_middle";

(*For disjunctive case analysis*)
fun excluded_middle_tac sP =
    res_inst_tac [("Q",sP)] (excluded_middle RS disjE);

val [p1,p2] = Goal"[| P ==> Q; ~P ==> Q |] ==> Q";
by (rtac (excluded_middle RS disjE) 1);
by (etac p2 1);
by (etac p1 1);
qed "case_split_thm";

(*HOL's more natural case analysis tactic*)
fun case_tac a = res_inst_tac [("P",a)] case_split_thm;


(*** Special elimination rules *)


(*Classical implies (-->) elimination. *)
val major::prems = Goal "[| P-->Q;  ~P ==> R;  Q ==> R |] ==> R";
by (resolve_tac [excluded_middle RS disjE] 1);
by (DEPTH_SOLVE (ares_tac (prems@[major RS mp]) 1)) ;
qed "impCE";

(*This version of --> elimination works on Q before P.  It works best for
  those cases in which P holds "almost everywhere".  Can't install as
  default: would break old proofs.*)
val major::prems = Goal "[| P-->Q;  Q ==> R;  ~P ==> R |] ==> R";
by (resolve_tac [excluded_middle RS disjE] 1);
by (DEPTH_SOLVE (ares_tac (prems@[major RS mp]) 1)) ;
qed "impCE'";

(*Double negation law*)
Goal"~~P ==> P";
by (rtac classical 1);
by (etac notE 1);
by (assume_tac 1);
qed "notnotD";

val [p1,p2] = Goal"[| Q; ~ P ==> ~ Q |] ==> P";
by (rtac classical 1);
by (dtac p2 1);
by (etac notE 1);
by (rtac p1 1);
qed "contrapos2";

(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in 
    ~P ==> ~Q    and    P ==> Q  *)
val major::prems = 
Goalw  [iff_def] "[| P<->Q;  [| P; Q |] ==> R;  [| ~P; ~Q |] ==> R |] ==> R";
by (rtac (major RS conjE) 1);
by (REPEAT_FIRST (etac impCE));
by (REPEAT (DEPTH_SOLVE_1 (mp_tac 1  ORELSE  ares_tac prems 1)));
qed "iffCE";

