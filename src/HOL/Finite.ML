(*  Title: 	HOL/Finite.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Finite powerset operator
*)

open Finite;

goalw Finite.thy Fin.defs "!!A B. A<=B ==> Fin(A) <= Fin(B)";
br lfp_mono 1;
by (REPEAT (ares_tac basic_monos 1));
qed "Fin_mono";

goalw Finite.thy Fin.defs "Fin(A) <= Pow(A)";
by (fast_tac (set_cs addSIs [lfp_lowerbound]) 1);
qed "Fin_subset_Pow";

(* A : Fin(B) ==> A <= B *)
val FinD = Fin_subset_Pow RS subsetD RS PowD;

(*Discharging ~ x:y entails extra work*)
val major::prems = goal Finite.thy 
    "[| F:Fin(A);  P({}); \
\	!!F x. [| x:A;  F:Fin(A);  x~:F;  P(F) |] ==> P(insert x F) \
\    |] ==> P(F)";
by (rtac (major RS Fin.induct) 1);
by (excluded_middle_tac "a:b" 2);
by (etac (insert_absorb RS ssubst) 3 THEN assume_tac 3);   (*backtracking!*)
by (REPEAT (ares_tac prems 1));
qed "Fin_induct";

(** Simplification for Fin **)

Addsimps Fin.intrs;

(*The union of two finite sets is finite*)
val major::prems = goal Finite.thy
    "[| F: Fin(A);  G: Fin(A) |] ==> F Un G : Fin(A)";
by (rtac (major RS Fin_induct) 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps (prems @ [Un_insert_left]))));
qed "Fin_UnI";

(*Every subset of a finite set is finite*)
val [subs,fin] = goal Finite.thy "[| A<=B;  B: Fin(M) |] ==> A: Fin(M)";
by (EVERY1 [subgoal_tac "ALL C. C<=B --> C: Fin(M)",
	    rtac mp, etac spec,
	    rtac subs]);
by (rtac (fin RS Fin_induct) 1);
by (simp_tac (!simpset addsimps [subset_Un_eq]) 1);
by (safe_tac (set_cs addSDs [subset_insert_iff RS iffD1]));
by (eres_inst_tac [("t","C")] (insert_Diff RS subst) 2);
by (ALLGOALS Asm_simp_tac);
qed "Fin_subset";

(*The image of a finite set is finite*)
val major::_ = goal Finite.thy
    "F: Fin(A) ==> h``F : Fin(h``A)";
by (rtac (major RS Fin_induct) 1);
by (Simp_tac 1);
by (asm_simp_tac
    (!simpset addsimps [image_eqI RS Fin.insertI, image_insert]) 1);
qed "Fin_imageI";

val major::prems = goal Finite.thy 
    "[| c: Fin(A);  b: Fin(A);  				\
\       P(b);       						\
\       !!(x::'a) y. [| x:A; y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> c<=b --> P(b-c)";
by (rtac (major RS Fin_induct) 1);
by (rtac (Diff_insert RS ssubst) 2);
by (ALLGOALS (asm_simp_tac
                (!simpset addsimps (prems@[Diff_subset RS Fin_subset]))));
qed "Fin_empty_induct_lemma";

val prems = goal Finite.thy 
    "[| b: Fin(A);  						\
\       P(b);        						\
\       !!x y. [| x:A; y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> P({})";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (Fin_empty_induct_lemma RS mp) 1);
by (REPEAT (ares_tac (subset_refl::prems) 1));
qed "Fin_empty_induct";
