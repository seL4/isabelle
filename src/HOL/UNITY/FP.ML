(*  Title:      HOL/UNITY/FP
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Fixed Point of a Program

From Misra, "A Logic for Concurrent Programming", 1994
*)

Goalw [FP_Orig_def, stable_def] "F : stable (FP_Orig F Int B)";
by (stac Int_Union2 1);
by (blast_tac (claset() addIs [constrains_UN]) 1);
qed "stable_FP_Orig_Int";


val prems = goalw thy [FP_Orig_def, stable_def]
    "(!!B. F : stable (A Int B)) ==> A <= FP_Orig F";
by (blast_tac (claset() addIs prems) 1);
qed "FP_Orig_weakest";


Goal "F : stable (FP F Int B)";
by (subgoal_tac "FP F Int B = (UN x:B. FP F Int {x})" 1);
by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [Int_insert_right]) 1);
by (rewrite_goals_tac [FP_def, stable_def]);
by (rtac constrains_UN 1);
by (Simp_tac 1);
qed "stable_FP_Int";

Goal "FP F <= FP_Orig F";
by (rtac (stable_FP_Int RS FP_Orig_weakest) 1);
val lemma1 = result();

Goalw [FP_Orig_def, FP_def] "FP_Orig F <= FP F";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{x}")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [Int_insert_right]) 1);
val lemma2 = result();

Goal "FP F = FP_Orig F";
by (rtac ([lemma1,lemma2] MRS equalityI) 1);
qed "FP_equivalence";

val [prem] = goal thy
    "(!!B. F : stable (A Int B)) ==> A <= FP F";
by (simp_tac (simpset() addsimps [FP_equivalence, prem RS FP_Orig_weakest]) 1);
qed "FP_weakest";

Goalw [FP_def, stable_def, constrains_def]
    "-(FP F) = (UN act: Acts F. -{s. act```{s} <= {s}})";
by (Blast_tac 1);
qed "Compl_FP";

Goal "A - (FP F) = (UN act: Acts F. A - {s. act```{s} <= {s}})";
by (simp_tac (simpset() addsimps [Diff_eq, Compl_FP]) 1);
qed "Diff_FP";

