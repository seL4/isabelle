(*  Title:      HOL/UNITY/FP
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Fixed Point of a Program

From Misra, "A Logic for Concurrent Programming", 1994
*)

goal thy "Union(B) Int A = (UN C:B. C Int A)";
by (Blast_tac 1);
qed "Int_Union2";

open FP;

goalw thy [FP_Orig_def, stable_def] "stable Acts (FP_Orig Acts Int B)";
by (stac Int_Union2 1);
by (rtac ball_constrains_UN 1);
by (Simp_tac 1);
qed "stable_FP_Orig_Int";


val prems = goalw thy [FP_Orig_def, stable_def]
    "(!!B. stable Acts (A Int B)) ==> A <= FP_Orig Acts";
by (blast_tac (claset() addIs prems) 1);
qed "FP_Orig_weakest";


goal thy "stable Acts (FP Acts Int B)";
by (subgoal_tac "FP Acts Int B = (UN x:B. FP Acts Int {x})" 1);
by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [Int_insert_right]) 1);
by (rewrite_goals_tac [FP_def, stable_def]);
by (rtac ball_constrains_UN 1);
by (Simp_tac 1);
qed "stable_FP_Int";

goal thy "FP Acts <= FP_Orig Acts";
by (rtac (stable_FP_Int RS FP_Orig_weakest) 1);
val lemma1 = result();

goalw thy [FP_Orig_def, FP_def] "FP_Orig Acts <= FP Acts";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{x}")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [Int_insert_right]) 1);
val lemma2 = result();

goal thy "FP Acts = FP_Orig Acts";
by (rtac ([lemma1,lemma2] MRS equalityI) 1);
qed "FP_equivalence";

val [prem] = goal thy
    "(!!B. stable Acts (A Int B)) ==> A <= FP Acts";
by (simp_tac (simpset() addsimps [FP_equivalence, prem RS FP_Orig_weakest]) 1);
qed "FP_weakest";

goalw thy [FP_def, stable_def, constrains_def]
    "Compl (FP Acts) = (UN act:Acts. Compl{s. act^^{s} <= {s}})";
by (Blast_tac 1);
qed "Compl_FP";

goal thy "A - (FP Acts) = (UN act:Acts. A - {s. act^^{s} <= {s}})";
by (simp_tac (simpset() addsimps [Diff_eq, Compl_FP]) 1);
qed "Diff_FP";

