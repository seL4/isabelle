(*  Title:      HOL/meson_lemmas.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Lemmas for Meson.
*)

(* "Axiom" of Choice, proved using the description operator *)

Goal "ALL x. EX y. Q x y ==> EX f. ALL x. Q x (f x)";
by (fast_tac (claset() addEs [someI]) 1);
qed "choice";


(* Generation of contrapositives *)

(*Inserts negated disjunct after removing the negation; P is a literal*)
val [major,minor] = Goal "~P|Q ==> ((~P==>P) ==> Q)";
by (rtac (major RS disjE) 1);
by (rtac notE 1);
by (etac minor 2);
by (ALLGOALS assume_tac);
qed "make_neg_rule";

(*For Plaisted's "Postive refinement" of the MESON procedure*)
Goal "~P|Q ==> (P ==> Q)";
by (Blast_tac 1);
qed "make_refined_neg_rule";

(*P should be a literal*)
val [major,minor] = Goal "P|Q ==> ((P==>~P) ==> Q)";
by (rtac (major RS disjE) 1);
by (rtac notE 1);
by (etac minor 1);
by (ALLGOALS assume_tac);
qed "make_pos_rule";


(* Generation of a goal clause -- put away the final literal *)

val [major,minor] = Goal "~P ==> ((~P==>P) ==> False)";
by (rtac notE 1);
by (rtac minor 2);
by (ALLGOALS (rtac major));
qed "make_neg_goal";

val [major,minor] = Goal "P ==> ((P==>~P) ==> False)";
by (rtac notE 1);
by (rtac minor 1);
by (ALLGOALS (rtac major));
qed "make_pos_goal";


(* Lemmas for forward proof (like congruence rules) *)

(*NOTE: could handle conjunctions (faster?) by
    nf(th RS conjunct2) RS (nf(th RS conjunct1) RS conjI) *)
val major::prems = Goal
    "[| P'&Q';  P' ==> P;  Q' ==> Q |] ==> P&Q";
by (rtac (major RS conjE) 1);
by (rtac conjI 1);
by (ALLGOALS (eresolve_tac prems));
qed "conj_forward";

val major::prems = Goal
    "[| P'|Q';  P' ==> P;  Q' ==> Q |] ==> P|Q";
by (rtac (major RS disjE) 1);
by (ALLGOALS (dresolve_tac prems));
by (ALLGOALS (eresolve_tac [disjI1,disjI2]));
qed "disj_forward";

(*Version for removal of duplicate literals*)
val major::prems = Goal
    "[| P'|Q';  P' ==> P;  [| Q'; P==>False |] ==> Q |] ==> P|Q";
by (cut_facts_tac [major] 1);
by (blast_tac (claset() addIs prems) 1);
qed "disj_forward2";

val major::prems = Goal
    "[| ALL x. P'(x);  !!x. P'(x) ==> P(x) |] ==> ALL x. P(x)";
by (rtac allI 1);
by (resolve_tac prems 1);
by (rtac (major RS spec) 1);
qed "all_forward";

val major::prems = Goal
    "[| EX x. P'(x);  !!x. P'(x) ==> P(x) |] ==> EX x. P(x)";
by (rtac (major RS exE) 1);
by (rtac exI 1);
by (eresolve_tac prems 1);
qed "ex_forward";
