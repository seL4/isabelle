(*  Title:      ZF/ex/Primrec
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Primitive Recursive Functions

Proof adopted from
Nora Szasz, 
A Machine Checked Proof that Ackermann's Function is not Primitive Recursive,
In: Huet & Plotkin, eds., Logical Environments (CUP, 1993), 317-338.

See also E. Mendelson, Introduction to Mathematical Logic.
(Van Nostrand, 1964), page 250, exercise 11.
*)

(*** Inductive definition of the PR functions ***)

(* c: prim_rec ==> c: list(nat) -> nat *)
val prim_rec_into_fun = prim_rec.dom_subset RS subsetD;

AddTCs ([prim_rec_into_fun] @ prim_rec.intrs);

Goal "i:nat ==> ACK(i): prim_rec";
by (induct_tac "i" 1);
by (ALLGOALS Asm_simp_tac);
qed "ACK_in_prim_rec";

AddTCs [ACK_in_prim_rec, prim_rec_into_fun RS apply_type,
	list_add_type, nat_into_Ord, rec_type];

Goal "[| i:nat;  j:nat |] ==>  ack(i,j): nat";
by Auto_tac;
qed "ack_type";
AddTCs [ack_type];

(** Ackermann's function cases **)

(*PROPERTY A 1*)
Goal "j:nat ==> ack(0,j) = succ(j)";
by (asm_simp_tac (simpset() addsimps [SC]) 1);
qed "ack_0";

(*PROPERTY A 2*)
Goal "ack(succ(i), 0) = ack(i,1)";
by (asm_simp_tac (simpset() addsimps [CONST,PREC_0]) 1);
qed "ack_succ_0";

(*PROPERTY A 3*)
Goal "[| i:nat;  j:nat |]  \
\     ==> ack(succ(i), succ(j)) = ack(i, ack(succ(i), j))";
by (asm_simp_tac (simpset() addsimps [CONST,PREC_succ,COMP_1,PROJ_0]) 1);
qed "ack_succ_succ";

Addsimps [ack_0, ack_succ_0, ack_succ_succ, ack_type];
Delsimps [ACK_0, ACK_succ];


(*PROPERTY A 4*)
Goal "i:nat ==> ALL j:nat. j < ack(i,j)";
by (induct_tac "i" 1);
by (Asm_simp_tac 1);
by (rtac ballI 1);
by (induct_tac "j" 1);
by (etac (succ_leI RS lt_trans1) 2);
by (rtac (nat_0I RS nat_0_le RS lt_trans) 1);
by Auto_tac;
qed_spec_mp "lt_ack2";

(*PROPERTY A 5-, the single-step lemma*)
Goal "[| i:nat; j:nat |] ==> ack(i,j) < ack(i, succ(j))";
by (induct_tac "i" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lt_ack2])));
qed "ack_lt_ack_succ2";

(*PROPERTY A 5, monotonicity for < *)
Goal "[| j<k; i:nat; k:nat |] ==> ack(i,j) < ack(i,k)";
by (ftac lt_nat_in_nat 1 THEN assume_tac 1);
by (etac succ_lt_induct 1);
by (assume_tac 1);
by (rtac lt_trans 2);
by (auto_tac (claset() addIs [ack_lt_ack_succ2], simpset()));
qed "ack_lt_mono2";

(*PROPERTY A 5', monotonicity for le *)
Goal "[| j le k;  i: nat;  k:nat |] ==> ack(i,j) le ack(i,k)";
by (res_inst_tac [("f", "%j. ack(i,j)")] Ord_lt_mono_imp_le_mono 1);
by (REPEAT (ares_tac [ack_lt_mono2, ack_type RS nat_into_Ord] 1));
qed "ack_le_mono2";

(*PROPERTY A 6*)
Goal "[| i:nat;  j:nat |] ==> ack(i, succ(j)) le ack(succ(i), j)";
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
by (rtac ack_le_mono2 1);
by (rtac (lt_ack2 RS succ_leI RS le_trans) 1);
by Auto_tac;
qed "ack2_le_ack1";

(*PROPERTY A 7-, the single-step lemma*)
Goal "[| i:nat; j:nat |] ==> ack(i,j) < ack(succ(i),j)";
by (rtac (ack_lt_mono2 RS lt_trans2) 1);
by (rtac ack2_le_ack1 4);
by Auto_tac;
qed "ack_lt_ack_succ1";

(*PROPERTY A 7, monotonicity for < *)
Goal "[| i<j; j:nat; k:nat |] ==> ack(i,k) < ack(j,k)";
by (ftac lt_nat_in_nat 1 THEN assume_tac 1);
by (etac succ_lt_induct 1);
by (assume_tac 1);
by (rtac lt_trans 2);
by (auto_tac (claset() addIs [ack_lt_ack_succ1], simpset()));
qed "ack_lt_mono1";

(*PROPERTY A 7', monotonicity for le *)
Goal "[| i le j; j:nat; k:nat |] ==> ack(i,k) le ack(j,k)";
by (res_inst_tac [("f", "%j. ack(j,k)")] Ord_lt_mono_imp_le_mono 1);
by (REPEAT (ares_tac [ack_lt_mono1, ack_type RS nat_into_Ord] 1));
qed "ack_le_mono1";

(*PROPERTY A 8*)
Goal "j:nat ==> ack(1,j) = succ(succ(j))";
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
qed "ack_1";

(*PROPERTY A 9*)
Goal "j:nat ==> ack(succ(1),j) = succ(succ(succ(j#+j)))";
by (induct_tac "j" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ack_1, add_succ_right])));
qed "ack_2";

(*PROPERTY A 10*)
Goal "[| i1:nat; i2:nat; j:nat |] ==> \
\               ack(i1, ack(i2,j)) < ack(succ(succ(i1#+i2)), j)";
by (rtac (ack2_le_ack1 RSN (2,lt_trans2)) 1);
by (Asm_simp_tac 1);
by (rtac (add_le_self RS ack_le_mono1 RS lt_trans1) 1);
by (rtac (add_le_self2 RS ack_lt_mono1 RS ack_lt_mono2) 4);
by Auto_tac;
qed "ack_nest_bound";

(*PROPERTY A 11*)
Goal "[| i1:nat; i2:nat; j:nat |] ==> \
\          ack(i1,j) #+ ack(i2,j) < ack(succ(succ(succ(succ(i1#+i2)))), j)";
by (res_inst_tac [("j", "ack(succ(1), ack(i1 #+ i2, j))")] lt_trans 1);
by (asm_simp_tac (simpset() addsimps [ack_2]) 1);
by (rtac (ack_nest_bound RS lt_trans2) 2);
by (Asm_simp_tac 5);
by (rtac (add_le_mono RS leI RS leI) 1);
by (auto_tac (claset() addIs [add_le_self, add_le_self2, ack_le_mono1], 
	      simpset()));
qed "ack_add_bound";

(*PROPERTY A 12.  Article uses existential quantifier but the ALF proof
  used k#+4.  Quantified version must be nested EX k'. ALL i,j... *)
Goal "[| i < ack(k,j);  j:nat;  k:nat |] ==> \
\             i#+j < ack(succ(succ(succ(succ(k)))), j)";
by (res_inst_tac [("j", "ack(k,j) #+ ack(0,j)")] lt_trans 1);
by (rtac (ack_add_bound RS lt_trans2) 2);
by (rtac add_lt_mono 1);
by Auto_tac;
qed "ack_add_bound2";

(*** MAIN RESULT ***)

Addsimps [list_add_type];

Goalw [SC_def] "l: list(nat) ==> SC ` l < ack(1, list_add(l))";
by (exhaust_tac "l" 1);
by (asm_simp_tac (simpset() addsimps [succ_iff]) 1);
by (asm_simp_tac (simpset() addsimps [ack_1, add_le_self]) 1);
qed "SC_case";

(*PROPERTY A 4'? Extra lemma needed for CONST case, constant functions*)
Goal "[| i:nat; j:nat |] ==> i < ack(i,j)";
by (induct_tac "i" 1);
by (asm_simp_tac (simpset() addsimps [nat_0_le]) 1);
by (etac ([succ_leI, ack_lt_ack_succ1] MRS lt_trans1) 1);
by Auto_tac;
qed "lt_ack1";

Goalw [CONST_def]
    "[| l: list(nat);  k: nat |] ==> CONST(k) ` l < ack(k, list_add(l))";
by (asm_simp_tac (simpset() addsimps [lt_ack1]) 1);
qed "CONST_case";

Goalw [PROJ_def]
    "l: list(nat) ==> ALL i:nat. PROJ(i) ` l < ack(0, list_add(l))";
by (Asm_simp_tac 1);
by (etac list.induct 1);
by (asm_simp_tac (simpset() addsimps [nat_0_le]) 1);
by (Asm_simp_tac 1);
by (rtac ballI 1);
by (eres_inst_tac [("n","x")] natE 1);
by (asm_simp_tac (simpset() addsimps [add_le_self]) 1);
by (Asm_simp_tac 1);
by (etac (bspec RS lt_trans2) 1);
by (rtac (add_le_self2 RS succ_leI) 2);
by Auto_tac;
qed_spec_mp "PROJ_case";

(** COMP case **)

Goal "fs : list({f: prim_rec .                                 \
\                  EX kf:nat. ALL l:list(nat).                  \
\                             f`l < ack(kf, list_add(l))})      \
\      ==> EX k:nat. ALL l: list(nat).                          \
\                list_add(map(%f. f ` l, fs)) < ack(k, list_add(l))";
by (etac list.induct 1);
by (res_inst_tac [("x","0")] bexI 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lt_ack1, nat_0_le])));
by (Clarify_tac 1);
by (rtac (ballI RS bexI) 1);
by (rtac (add_lt_mono RS lt_trans) 1);
by (REPEAT (FIRSTGOAL (etac bspec)));
by (rtac ack_add_bound 5);
by Auto_tac;
qed "COMP_map_lemma";

Goalw [COMP_def]
 "[| kg: nat;                                 \
\         ALL l:list(nat). g`l < ack(kg, list_add(l));          \
\         fs : list({f: prim_rec .                               \
\                    EX kf:nat. ALL l:list(nat).                \
\                       f`l < ack(kf, list_add(l))})            \
\      |] ==> EX k:nat. ALL l: list(nat). COMP(g,fs)`l < ack(k, list_add(l))";
by (Asm_simp_tac 1);
by (ftac list_CollectD 1);
by (etac (COMP_map_lemma RS bexE) 1);
by (rtac (ballI RS bexI) 1);
by (etac (bspec RS lt_trans) 1);
by (rtac lt_trans 2);
by (rtac ack_nest_bound 3);
by (etac (bspec RS ack_lt_mono2) 2);
by Auto_tac;
qed "COMP_case";

(** PREC case **)

Goalw [PREC_def]
 "[| ALL l:list(nat). f`l #+ list_add(l) < ack(kf, list_add(l)); \
\           ALL l:list(nat). g`l #+ list_add(l) < ack(kg, list_add(l)); \
\           f: prim_rec;  kf: nat;                                       \
\           g: prim_rec;  kg: nat;                                       \
\           l: list(nat)                                                \
\        |] ==> PREC(f,g)`l #+ list_add(l) < ack(succ(kf#+kg), list_add(l))";
by (exhaust_tac "l" 1);
by (asm_simp_tac (simpset() addsimps [[nat_le_refl, lt_ack2] MRS lt_trans]) 1);
by (Asm_simp_tac 1);
by (etac ssubst 1);  (*get rid of the needless assumption*)
by (induct_tac "a" 1);
(*base case*)
by (EVERY1 [Asm_simp_tac, rtac lt_trans, etac bspec,
	    assume_tac, rtac (add_le_self RS ack_lt_mono1)]);
by (ALLGOALS Asm_simp_tac);
(*ind step*)
by (rtac (succ_leI RS lt_trans1) 1);
by (res_inst_tac [("j", "g ` ?ll #+ ?mm")] lt_trans1 1);
by (etac bspec 2);
by (rtac (nat_le_refl RS add_le_mono) 1);
by Typecheck_tac;
by (asm_simp_tac (simpset() addsimps [add_le_self2]) 1);
(*final part of the simplification*)
by (Asm_simp_tac 1);
by (rtac (add_le_self2 RS ack_le_mono1 RS lt_trans1) 1);
by (etac ack_lt_mono2 4);
by Auto_tac;
qed "PREC_case_lemma";

Goal "[| f: prim_rec;  kf: nat;                               \
\        g: prim_rec;  kg: nat;                               \
\        ALL l:list(nat). f`l < ack(kf, list_add(l));        \
\        ALL l:list(nat). g`l < ack(kg, list_add(l))         \
\     |] ==> EX k:nat. ALL l: list(nat). PREC(f,g)`l< ack(k, list_add(l))";
by (rtac (ballI RS bexI) 1);
by (rtac ([add_le_self, PREC_case_lemma] MRS lt_trans1) 1);
by (REPEAT_FIRST (rtac (ack_add_bound2 RS ballI) THEN' etac bspec));
by Typecheck_tac;
qed "PREC_case";

Goal "f:prim_rec ==> EX k:nat. ALL l:list(nat). f`l < ack(k, list_add(l))";
by (etac prim_rec.induct 1);
by (auto_tac (claset() addIs [SC_case, CONST_case, PROJ_case, COMP_case, 
			      PREC_case], 
	      simpset()));
qed "ack_bounds_prim_rec";

Goal "~ (lam l:list(nat). list_case(0, %x xs. ack(x,x), l)) : prim_rec";
by (rtac notI 1);
by (etac (ack_bounds_prim_rec RS bexE) 1);
by (rtac lt_irrefl 1);
by (dres_inst_tac [("x", "[x]")] bspec 1);
by Auto_tac;
qed "ack_not_prim_rec";

