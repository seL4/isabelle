(*  Title:      FOLP/FOLP.ML
    ID:         $Id$
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics and lemmas for FOLP (Classical First-Order Logic with Proofs)
*)

(*** Classical introduction rules for | and EX ***)

val prems= goal FOLP.thy 
   "(!!x. x:~Q ==> f(x):P) ==> ?p : P|Q";
by (rtac classical 1);
by (REPEAT (ares_tac (prems@[disjI1,notI]) 1));
by (REPEAT (ares_tac (prems@[disjI2,notE]) 1)) ;
qed "disjCI";

(*introduction rule involving only EX*)
val prems= goal FOLP.thy 
   "( !!u. u:~(EX x. P(x)) ==> f(u):P(a)) ==> ?p : EX x. P(x)";
by (rtac classical 1);
by (eresolve_tac (prems RL [exI]) 1) ;
qed "ex_classical";

(*version of above, simplifying ~EX to ALL~ *)
val [prem]= goal FOLP.thy 
   "(!!u. u:ALL x. ~P(x) ==> f(u):P(a)) ==> ?p : EX x. P(x)";
by (rtac ex_classical 1);
by (resolve_tac [notI RS allI RS prem] 1);
by (etac notE 1);
by (etac exI 1) ;
qed "exCI";

val excluded_middle = prove_goal FOLP.thy "?p : ~P | P"
 (fn _=> [ rtac disjCI 1, assume_tac 1 ]);


(*** Special elimination rules *)


(*Classical implies (-->) elimination. *)
val major::prems= goal FOLP.thy 
    "[| p:P-->Q;  !!x. x:~P ==> f(x):R;  !!y. y:Q ==> g(y):R |] ==> ?p : R";
by (resolve_tac [excluded_middle RS disjE] 1);
by (DEPTH_SOLVE (ares_tac (prems@[major RS mp]) 1)) ;
qed "impCE";

(*Double negation law*)
Goal "p:~~P ==> ?p : P";
by (rtac classical 1);
by (etac notE 1);
by (assume_tac 1);
qed "notnotD";


(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in 
    ~P ==> ~Q    and    P ==> Q  *)
val prems = goalw FOLP.thy [iff_def]
    "[| p:P<->Q; !!x y.[| x:P; y:Q |] ==> f(x,y):R;  \
\                !!x y.[| x:~P; y:~Q |] ==> g(x,y):R |] ==> ?p : R";
by (rtac conjE 1);
by (REPEAT (DEPTH_SOLVE_1 (etac impCE 1
               ORELSE  mp_tac 1  ORELSE  ares_tac prems 1))) ;
qed "iffCE";


(*Should be used as swap since ~P becomes redundant*)
val major::prems= goal FOLP.thy 
   "p:~P ==> (!!x. x:~Q ==> f(x):P) ==> ?p : Q";
by (rtac classical 1);
by (rtac (major RS notE) 1);
by (REPEAT (ares_tac prems 1)) ;
qed "swap";

