(*  Title:      ZF/UNITY/FP.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Fixed Point of a Program

From Misra, "A Logic for Concurrent Programming", 1994

Theory ported form HOL.
*)

Goalw [FP_Orig_def] "FP_Orig(F)<=state";
by (Blast_tac 1);
qed "FP_Orig_type";

Goalw [st_set_def] "st_set(FP_Orig(F))";
by (rtac FP_Orig_type 1);
qed "st_set_FP_Orig";
AddIffs [st_set_FP_Orig];

Goalw [FP_def] "FP(F)<=state";
by (Blast_tac 1);
qed "FP_type";

Goalw [st_set_def] "st_set(FP(F))";
by (rtac FP_type 1);
qed "st_set_FP";
AddIffs [st_set_FP];

Goalw [FP_Orig_def, stable_def] "F:program ==> F:stable(FP_Orig(F) Int B)";
by (stac Int_Union2 1);
by (blast_tac (claset() addIs [constrains_UN]) 1);
qed "stable_FP_Orig_Int";

Goalw [FP_Orig_def, stable_def, st_set_def]
    "[| ALL B. F: stable (A Int B); st_set(A) |]  ==> A <= FP_Orig(F)";
by (Blast_tac 1);
qed "FP_Orig_weakest2";

bind_thm("FP_Orig_weakest",  allI RS FP_Orig_weakest2);

Goal "F:program ==> F : stable (FP(F) Int B)";
by (subgoal_tac "FP(F) Int B = (UN x:B. FP(F) Int {x})" 1);
by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [Int_cons_right]) 1);
by (rewrite_goals_tac [FP_def, stable_def]);
by (rtac constrains_UN 1);
by (auto_tac (claset(), simpset() addsimps [cons_absorb]));
qed "stable_FP_Int";

Goal "F:program ==> FP(F) <= FP_Orig(F)";
by (rtac (stable_FP_Int RS FP_Orig_weakest) 1);
by Auto_tac;
qed "FP_subset_FP_Orig";

Goalw [FP_Orig_def, FP_def] "F:program ==> FP_Orig(F) <= FP(F)";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{x}")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [Int_cons_right]) 1);
by (ftac stableD2 1);
by (auto_tac (claset(), simpset() addsimps [cons_absorb, st_set_def]));
qed "FP_Orig_subset_FP";


Goal "F:program ==> FP(F) = FP_Orig(F)";
by (rtac ([FP_subset_FP_Orig,FP_Orig_subset_FP] MRS equalityI) 1);
by (ALLGOALS(assume_tac));
qed "FP_equivalence";


Goal  "[| ALL B. F : stable(A Int B); F:program; st_set(A) |] ==> A <= FP(F)";
by (asm_simp_tac (simpset() addsimps [FP_equivalence, FP_Orig_weakest]) 1);
qed "FP_weakest2";
bind_thm("FP_weakest", allI RS FP_weakest2);

Goalw [FP_def, stable_def, constrains_def, st_set_def]
"[| F:program;  st_set(A) |] ==> A-FP(F) = (UN act:Acts(F). A-{s:state. act``{s} <= {s}})";
by (Blast_tac 1);
qed "Diff_FP";

