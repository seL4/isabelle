(*  Title:      ZF/UNITY/GenIncreasing
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

A general form of the `Increasing' relation of Charpentier
*)

(** increasing **)

Goalw [increasing_def] "increasing[A](r, f) <= program";
by (Blast_tac 1);
qed "increasing_type";

Goalw [increasing_def] "F:increasing[A](r, f) ==> F:program";
by (Blast_tac 1);
qed "increasing_into_program";

Goalw [increasing_def]
"[| F:increasing[A](r, f); x:A |] ==>F:stable({s:state. <x, f(s)>:r})";
by (Blast_tac 1);
qed "increasing_imp_stable";

Goalw [increasing_def]
"F:increasing[A](r,f) ==> F:program & (EX a. a:A) & (ALL s:state. f(s):A)";
by (subgoal_tac "EX x. x:state" 1);
by (auto_tac (claset() addDs [stable_type RS subsetD]
                       addIs [st0_in_state], simpset()));
qed "increasingD";

Goalw [increasing_def, stable_def]
 "F:increasing[A](r, %s. c) <-> F:program & c:A";
by (subgoal_tac "EX x. x:state" 1);
by (auto_tac (claset() addDs [stable_type RS subsetD]
                       addIs [st0_in_state], simpset()));
qed "increasing_constant";
Addsimps [increasing_constant];

Goalw [increasing_def, stable_def, part_order_def, 
       constrains_def, mono1_def, comp_def]
"[| mono1(A, r, B, s, g); refl(A, r); trans[B](s)  |] ==> \
\  increasing[A](r, f) <= increasing[B](s, g comp f)";
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "xa:state" 1);
by (blast_tac (claset() addSDs [ActsD]) 2);
by (subgoal_tac "<f(xb), f(xb)>:r" 1);
by (force_tac (claset(), simpset() addsimps [refl_def]) 2);
by (rotate_tac 5 1);
by (dres_inst_tac [("x", "f(xb)")] bspec 1);
by (rotate_tac ~1 2);
by (dres_inst_tac [("x", "act")] bspec 2);
by (ALLGOALS(Asm_full_simp_tac));
by (dres_inst_tac [("A", "act``?u"), ("c", "xa")] subsetD 1);
by (Blast_tac 1);
by (dres_inst_tac [("x", "f(xa)"), ("x1", "f(xb)")] (bspec RS bspec) 1);
by (res_inst_tac [("b", "g(f(xb))"), ("A", "B")] trans_onD 3);
by (ALLGOALS(Asm_simp_tac));
qed "subset_increasing_comp";

Goal "[| F:increasing[A](r, f); mono1(A, r, B, s, g); \
\        refl(A, r); trans[B](s) |] ==> F:increasing[B](s, g comp f)";
by (rtac (subset_increasing_comp RS subsetD) 1);
by Auto_tac;
qed "imp_increasing_comp";

Goalw [increasing_def, Le_def, Lt_def]
   "increasing[nat](Le, f) <= increasing[nat](Lt, f)";
by Auto_tac;
qed "strict_increasing";

Goalw [increasing_def, Gt_def, Ge_def]
   "increasing[nat](Ge, f) <= increasing[nat](Gt, f)";
by Auto_tac;
by (etac natE 1);
by (auto_tac (claset(), simpset() addsimps [stable_def]));
qed "strict_gt_increasing";

(** Increasing **)

Goalw [increasing_def, Increasing_def]
     "F : increasing[A](r, f) ==> F : Increasing[A](r, f)";
by (auto_tac (claset() addIs [stable_imp_Stable], simpset())); 
qed "increasing_imp_Increasing";

Goalw [Increasing_def] "Increasing[A](r, f) <= program";
by Auto_tac;
qed "Increasing_type";

Goalw [Increasing_def] "F:Increasing[A](r, f) ==> F:program";
by Auto_tac;
qed "Increasing_into_program";

Goalw [Increasing_def]
"[| F:Increasing[A](r, f); a:A |] ==> F: Stable({s:state. <a,f(s)>:r})";
by (Blast_tac 1);
qed "Increasing_imp_Stable";

Goalw [Increasing_def]
"F:Increasing[A](r, f) ==> F:program & (EX a. a:A) & (ALL s:state. f(s):A)";
by (subgoal_tac "EX x. x:state" 1);
by (auto_tac (claset() addIs [st0_in_state], simpset()));
qed "IncreasingD";

Goal
"F:Increasing[A](r, %s. c) <-> F:program & (c:A)";
by (subgoal_tac "EX x. x:state" 1);
by (auto_tac (claset() addSDs [IncreasingD]
                       addIs [st0_in_state,
                   increasing_imp_Increasing], simpset()));
qed "Increasing_constant";
Addsimps [Increasing_constant];

Goalw [Increasing_def, Stable_def, Constrains_def, part_order_def, 
       constrains_def, mono1_def, comp_def]
"[| mono1(A, r, B, s, g); refl(A, r); trans[B](s) |] ==> \
\  Increasing[A](r, f) <= Increasing[B](s, g comp f)";
by Safe_tac;
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [ActsD])));
by (subgoal_tac "xb:state & xa:state" 1);
by (asm_simp_tac (simpset() addsimps [ActsD]) 2);
by (subgoal_tac "<f(xb), f(xb)>:r" 1);
by (force_tac (claset(), simpset() addsimps [refl_def]) 2);
by (rotate_tac 5 1);
by (dres_inst_tac [("x", "f(xb)")] bspec 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Clarify_tac 1);
by (rotate_tac ~2 1);
by (dres_inst_tac [("x", "act")] bspec 1);
by (dres_inst_tac [("A", "act``?u"), ("c", "xa")] subsetD 2);
by (ALLGOALS(Asm_full_simp_tac));
by (Blast_tac 1);
by (dres_inst_tac [("x", "f(xa)"), ("x1", "f(xb)")] (bspec RS bspec) 1);
by (res_inst_tac [("b", "g(f(xb))"), ("A", "B")] trans_onD 3);
by (ALLGOALS(Asm_full_simp_tac));
qed "subset_Increasing_comp";

Goal "[| F:Increasing[A](r, f); mono1(A, r, B, s, g); refl(A, r); trans[B](s) |]  \
\ ==> F:Increasing[B](s, g comp f)";
by (rtac (subset_Increasing_comp RS subsetD) 1);
by Auto_tac;
qed "imp_Increasing_comp";
  
Goalw [Increasing_def, Le_def, Lt_def]
"Increasing[nat](Le, f) <= Increasing[nat](Lt, f)";
by Auto_tac;
qed "strict_Increasing";

Goalw [Increasing_def, Ge_def, Gt_def] 
"Increasing[nat](Ge, f)<= Increasing[nat](Gt, f)";
by Auto_tac;
by (etac natE 1);
by (auto_tac (claset(), simpset() addsimps [Stable_def]));
qed "strict_gt_Increasing";

(** Two-place monotone operations **)

Goalw [increasing_def, stable_def, 
       part_order_def, constrains_def, mono2_def]
"[| F:increasing[A](r, f); F:increasing[B](s, g); \
\   mono2(A, r, B, s, C, t, h); refl(A, r); refl(B, s); trans[C](t) |] ==> \
\  F:increasing[C](t, %x. h(f(x), g(x)))";
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (rename_tac "xa xb" 1);
by (subgoal_tac "xb:state & xa:state" 1);
by (blast_tac (claset() addSDs [ActsD]) 2);
by (subgoal_tac "<f(xb), f(xb)>:r & <g(xb), g(xb)>:s" 1);
by (force_tac (claset(), simpset() addsimps [refl_def]) 2);
by (rotate_tac 6 1);
by (dres_inst_tac [("x", "f(xb)")] bspec 1);
by (rotate_tac 1 2);
by (dres_inst_tac [("x", "g(xb)")] bspec 2);
by (ALLGOALS(Asm_simp_tac));
by (rotate_tac ~1 1);
by (dres_inst_tac [("x", "act")] bspec 1);
by (rotate_tac ~3 2);
by (dres_inst_tac [("x", "act")] bspec 2);
by (ALLGOALS(Asm_full_simp_tac));
by (dres_inst_tac [("A", "act``?u"), ("c", "xa")] subsetD 1);
by (dres_inst_tac [("A", "act``?u"), ("c", "xa")] subsetD 2);
by (Blast_tac 1);
by (Blast_tac 1);
by (rotate_tac ~4 1);
by (dres_inst_tac [("x", "f(xa)"), ("x1", "f(xb)")] (bspec RS bspec) 1);
by (rotate_tac ~1 3);
by (dres_inst_tac [("x", "g(xa)"), ("x1", "g(xb)")] (bspec RS bspec) 3);
by (ALLGOALS(Asm_full_simp_tac));
by (res_inst_tac [("b", "h(f(xb), g(xb))"), ("A", "C")] trans_onD 1);
by (ALLGOALS(Asm_full_simp_tac));
qed "imp_increasing_comp2";

Goalw [Increasing_def, stable_def, 
       part_order_def, constrains_def, mono2_def, Stable_def, Constrains_def]
"[| F:Increasing[A](r, f); F:Increasing[B](s, g); \
\ mono2(A, r, B, s, C, t, h); refl(A, r); refl(B, s); trans[C](t) |] ==> \
\ F:Increasing[C](t, %x. h(f(x), g(x)))";
by Safe_tac;
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [ActsD])));
by (subgoal_tac "xa:state & x:state" 1);
by (blast_tac (claset() addSDs [ActsD]) 2);
by (subgoal_tac "<f(xa), f(xa)>:r & <g(xa), g(xa)>:s" 1);
by (force_tac (claset(), simpset() addsimps [refl_def]) 2);
by (rotate_tac 6 1);
by (dres_inst_tac [("x", "f(xa)")] bspec 1);
by (rotate_tac 1 2);
by (dres_inst_tac [("x", "g(xa)")] bspec 2);
by (ALLGOALS(Asm_simp_tac));
by (Clarify_tac 1);
by (rotate_tac ~2 1);
by (dres_inst_tac [("x", "act")] bspec 1);
by (rotate_tac ~3 2);
by (dres_inst_tac [("x", "act")] bspec 2);
by (ALLGOALS(Asm_full_simp_tac));
by (dres_inst_tac [("A", "act``?u"), ("c", "x")] subsetD 1);
by (dres_inst_tac [("A", "act``?u"), ("c", "x")] subsetD 2);
by (Blast_tac 1);
by (Blast_tac 1);
by (rotate_tac ~9 1);
by (dres_inst_tac [("x", "f(x)"), ("x1", "f(xa)")] (bspec RS bspec) 1);
by (rotate_tac ~1 3);
by (dres_inst_tac [("x", "g(x)"), ("x1", "g(xa)")] (bspec RS bspec) 3);
by (ALLGOALS(Asm_full_simp_tac));
by (res_inst_tac [("b", "h(f(xa), g(xa))"), ("A", "C")] trans_onD 1);
by (ALLGOALS(Asm_full_simp_tac));
qed "imp_Increasing_comp2";

