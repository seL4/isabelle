(*  Title: 	FOL/fol.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Tactics and lemmas for fol.thy (classical First-Order Logic)
*)

open FOLP;

signature FOLP_LEMMAS = 
  sig
  val disjCI : thm
  val excluded_middle : thm
  val exCI : thm
  val ex_classical : thm
  val iffCE : thm
  val impCE : thm
  val notnotD : thm
  val swap : thm
  end;


structure FOLP_Lemmas : FOLP_LEMMAS = 
struct

(*** Classical introduction rules for | and EX ***)

val disjCI = prove_goal FOLP.thy 
   "(!!x.x:~Q ==> f(x):P) ==> ?p : P|Q"
 (fn prems=>
  [ (resolve_tac [classical] 1),
    (REPEAT (ares_tac (prems@[disjI1,notI]) 1)),
    (REPEAT (ares_tac (prems@[disjI2,notE]) 1)) ]);

(*introduction rule involving only EX*)
val ex_classical = prove_goal FOLP.thy 
   "( !!u.u:~(EX x. P(x)) ==> f(u):P(a)) ==> ?p : EX x.P(x)"
 (fn prems=>
  [ (resolve_tac [classical] 1),
    (eresolve_tac (prems RL [exI]) 1) ]);

(*version of above, simplifying ~EX to ALL~ *)
val exCI = prove_goal FOLP.thy 
   "(!!u.u:ALL x. ~P(x) ==> f(u):P(a)) ==> ?p : EX x.P(x)"
 (fn [prem]=>
  [ (resolve_tac [ex_classical] 1),
    (resolve_tac [notI RS allI RS prem] 1),
    (eresolve_tac [notE] 1),
    (eresolve_tac [exI] 1) ]);

val excluded_middle = prove_goal FOLP.thy "?p : ~P | P"
 (fn _=> [ rtac disjCI 1, assume_tac 1 ]);


(*** Special elimination rules *)


(*Classical implies (-->) elimination. *)
val impCE = prove_goal FOLP.thy 
    "[| p:P-->Q;  !!x.x:~P ==> f(x):R;  !!y.y:Q ==> g(y):R |] ==> ?p : R"
 (fn major::prems=>
  [ (resolve_tac [excluded_middle RS disjE] 1),
    (DEPTH_SOLVE (ares_tac (prems@[major RS mp]) 1)) ]);

(*Double negation law*)
val notnotD = prove_goal FOLP.thy "p:~~P ==> ?p : P"
 (fn [major]=>
  [ (resolve_tac [classical] 1), (eresolve_tac [major RS notE] 1) ]);


(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in 
    ~P ==> ~Q    and    P ==> Q  *)
val iffCE = prove_goalw FOLP.thy [iff_def]
    "[| p:P<->Q; !!x y.[| x:P; y:Q |] ==> f(x,y):R;  \
\                !!x y.[| x:~P; y:~Q |] ==> g(x,y):R |] ==> ?p : R"
 (fn prems =>
  [ (resolve_tac [conjE] 1),
    (REPEAT (DEPTH_SOLVE_1 
	(etac impCE 1  ORELSE  mp_tac 1  ORELSE  ares_tac prems 1))) ]);


(*Should be used as swap since ~P becomes redundant*)
val swap = prove_goal FOLP.thy 
   "p:~P ==> (!!x.x:~Q ==> f(x):P) ==> ?p : Q"
 (fn major::prems=>
  [ (resolve_tac [classical] 1),
    (rtac (major RS notE) 1),
    (REPEAT (ares_tac prems 1)) ]);

end;

open FOLP_Lemmas;
