(*  Title:      HOL/UNITY/FP.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Fixed Point of a Program

From Misra, "A Logic for Concurrent Programming", 1994

Theory ported form HOL.
*)


Goalw [FP_Orig_def] 
  "FP_Orig(F):condition";
by (Blast_tac 1);
qed "FP_Orig_type";
AddIffs [FP_Orig_type];
AddTCs  [FP_Orig_type];

Goalw [FP_Orig_def, condition_def]  
  "x:FP_Orig(F) ==> x:state";
by Auto_tac;
qed "FP_OrigD";

Goalw [FP_def, condition_def] 
         "FP(F):condition";
by (Blast_tac 1);
qed "FP_type";
AddIffs [FP_type];
AddTCs  [FP_type];

Goalw [FP_def, condition_def]  
  "x:FP(F) ==> x:state";
by Auto_tac;
qed "FP_D";

Goal "Union(B) Int A = (UN C:B. C Int A)"; 
by (Blast_tac 1);
qed "Int_Union2";

Goalw [FP_Orig_def, stable_def] 
"[| F:program; B:condition |] \
\        ==> F:stable(FP_Orig(F) Int B)";
by (stac Int_Union2 1);
by (blast_tac (claset() addIs [constrains_UN]) 1);
qed "stable_FP_Orig_Int";

Goalw [FP_Orig_def, stable_def]
    "[| ALL B:condition. F : stable (A Int B); A:condition |] \
\    ==> A <= FP_Orig(F)";
by (Blast_tac 1);
bind_thm("FP_Orig_weakest",  ballI RS result());

Goal "A Int cons(a, B) = \
   \ (if a : A then cons(a, cons(a, (A Int B))) else A Int B)";
by Auto_tac;
qed "Int_cons_right";


Goal "[| F:program; B:condition |] ==> F : stable (FP(F) Int B)";
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
val lemma1 = result();


Goalw [FP_Orig_def, FP_def] 
"F:program ==> FP_Orig(F) <= FP(F)";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{x}")] bspec 1);
by (force_tac (claset(), simpset() addsimps [condition_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [Int_cons_right]) 1);
by (auto_tac (claset(), simpset() addsimps [cons_absorb]));
by (force_tac (claset(), simpset() addsimps [condition_def]) 1);
val lemma2 = result();


Goal "F:program ==> FP(F) = FP_Orig(F)";
by (rtac ([lemma1,lemma2] MRS equalityI) 1);
by (ALLGOALS(assume_tac));
qed "FP_equivalence";


Goal  "[| ALL B:condition. F : stable(A Int B); A:condition; F:program |] \
\      ==> A <= FP(F)";
by (asm_simp_tac (simpset() addsimps [FP_equivalence, FP_Orig_weakest]) 1);
bind_thm("FP_weakest", result() RS ballI);

Goalw [FP_def, stable_def, constrains_def, condition_def]
    "[| F:program;  A:condition |] ==> \
\ A - FP(F) = (UN act: Acts(F). A -{s:state. act``{s} <= {s}})";
by (Blast_tac 1);
qed "Diff_FP";

