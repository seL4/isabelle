(*  Title:      HOL/ex/Primrec
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Primitive Recursive Functions

Proof adopted from
Nora Szasz, 
A Machine Checked Proof that Ackermann's Function is not Primitive Recursive,
In: Huet & Plotkin, eds., Logical Environments (CUP, 1993), 317-338.

See also E. Mendelson, Introduction to Mathematical Logic.
(Van Nostrand, 1964), page 250, exercise 11.
*)


(** Useful special cases of evaluation ***)

Goalw [SC_def] "SC (x#l) = Suc x";
by (Asm_simp_tac 1);
qed "SC";

Goalw [CONST_def] "CONST k l = k";
by (Asm_simp_tac 1);
qed "CONST";

Goalw [PROJ_def] "PROJ(0) (x#l) = x";
by (Asm_simp_tac 1);
qed "PROJ_0";

Goalw [COMP_def] "COMP g [f] l = g [f l]";
by (Asm_simp_tac 1);
qed "COMP_1";

Goalw [PREC_def] "PREC f g (0#l) = f l";
by (Asm_simp_tac 1);
qed "PREC_0";

Goalw [PREC_def] "PREC f g (Suc x # l) = g (PREC f g (x#l) # x # l)";
by (Asm_simp_tac 1);
qed "PREC_Suc";

Addsimps [SC, CONST, PROJ_0, COMP_1, PREC_0, PREC_Suc];


(*PROPERTY A 4*)
Goal "j < ack(i,j)";
by (induct_thm_tac ack.induct "i j" 1);
by (ALLGOALS Asm_simp_tac);
qed "less_ack2";

AddIffs [less_ack2];

(*PROPERTY A 5-, the single-step lemma*)
Goal "ack(i,j) < ack(i, Suc(j))";
by (induct_thm_tac ack.induct "i j" 1);
by (ALLGOALS Asm_simp_tac);
qed "ack_less_ack_Suc2";

AddIffs [ack_less_ack_Suc2];

(*PROPERTY A 5, monotonicity for < *)
Goal "j<k --> ack(i,j) < ack(i,k)";
by (induct_thm_tac ack.induct "i k" 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (claset() addSEs [less_SucE] addIs [less_trans]) 1);
qed_spec_mp "ack_less_mono2";

(*PROPERTY A 5', monotonicity for<=*)
Goal "j<=k ==> ack(i,j)<=ack(i,k)";
by (full_simp_tac (simpset() addsimps [order_le_less]) 1);
by (blast_tac (claset() addIs [ack_less_mono2]) 1);
qed "ack_le_mono2";

(*PROPERTY A 6*)
Goal "ack(i, Suc(j)) <= ack(Suc(i), j)";
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (claset() addIs [ack_le_mono2, less_ack2 RS Suc_leI, 
			      le_trans]) 1);
qed "ack2_le_ack1";

AddIffs [ack2_le_ack1];

(*PROPERTY A 7-, the single-step lemma*)
Goal "ack(i,j) < ack(Suc(i),j)";
by (blast_tac (claset() addIs [ack_less_mono2, less_le_trans]) 1);
qed "ack_less_ack_Suc1";

AddIffs [ack_less_ack_Suc1];

(*PROPERTY A 4'? Extra lemma needed for CONST case, constant functions*)
Goal "i < ack(i,j)";
by (induct_tac "i" 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (claset() addIs [Suc_leI, le_less_trans]) 1);
qed "less_ack1";
AddIffs [less_ack1];

(*PROPERTY A 8*)
Goal "ack(1,j) = j + #2";
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
qed "ack_1";
Addsimps [ack_1];

(*PROPERTY A 9.  The unary 1 and 2 in ack is essential for the rewriting.*)
Goal "ack(2,j) = #2*j + #3";
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
qed "ack_2";
Addsimps [ack_2];


(*PROPERTY A 7, monotonicity for < [not clear why ack_1 is now needed first!]*)
Goal "ack(i,k) < ack(Suc(i+i'),k)";
by (induct_thm_tac ack.induct "i k" 1);
by (ALLGOALS Asm_full_simp_tac);
by (blast_tac (claset() addIs [less_trans, ack_less_mono2]) 2);
by (induct_thm_tac ack.induct "i' n" 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (claset() addIs [less_trans, ack_less_mono2]) 1);
by (blast_tac (claset() addIs [Suc_leI RS le_less_trans, ack_less_mono2]) 1);
val lemma = result();

Goal "i<j ==> ack(i,k) < ack(j,k)";
by (dtac less_imp_Suc_add 1);
by (blast_tac (claset() addSIs [lemma]) 1);
qed "ack_less_mono1";

(*PROPERTY A 7', monotonicity for<=*)
Goal "i<=j ==> ack(i,k)<=ack(j,k)";
by (full_simp_tac (simpset() addsimps [order_le_less]) 1);
by (blast_tac (claset() addIs [ack_less_mono1]) 1);
qed "ack_le_mono1";

(*PROPERTY A 10*)
Goal "ack(i1, ack(i2,j)) < ack(#2 + (i1+i2), j)";
by (simp_tac numeral_ss 1);
by (rtac (ack2_le_ack1 RSN (2,less_le_trans)) 1);
by (Asm_simp_tac 1);
by (rtac (le_add1 RS ack_le_mono1 RS le_less_trans) 1);
by (rtac (ack_less_mono1 RS ack_less_mono2) 1);
by (simp_tac (simpset() addsimps [le_imp_less_Suc, le_add2]) 1);
qed "ack_nest_bound";

(*PROPERTY A 11*)
Goal "ack(i1,j) + ack(i2,j) < ack(#4 + (i1 + i2), j)";
by (res_inst_tac [("j", "ack(2, ack(i1 + i2, j))")] less_trans 1);
by (Asm_simp_tac 1);
by (rtac (ack_nest_bound RS less_le_trans) 2);
by (asm_simp_tac (simpset() addsimps [Suc3_eq_add_3]) 2);
by (cut_inst_tac [("i","i1"), ("m1","i2"), ("k","j")] 
    (le_add1 RS ack_le_mono1) 1);
by (cut_inst_tac [("i","i2"), ("m1","i1"), ("k","j")] 
    (le_add2 RS ack_le_mono1) 1);
by Auto_tac;
qed "ack_add_bound";

(*PROPERTY A 12.  Article uses existential quantifier but the ALF proof
  used k+4.  Quantified version must be nested EX k'. ALL i,j... *)
Goal "i < ack(k,j) ==> i+j < ack(#4 + k, j)";
by (res_inst_tac [("j", "ack(k,j) + ack(0,j)")] less_trans 1);
by (rtac (ack_add_bound RS less_le_trans) 2);
by (Asm_simp_tac 2);
by (REPEAT (ares_tac ([add_less_mono, less_ack2]) 1));
qed "ack_add_bound2";


(*** Inductive definition of the PR functions ***)

(*** MAIN RESULT ***)

Goalw [SC_def] "SC l < ack(1, list_add l)";
by (induct_tac "l" 1);
by (ALLGOALS (simp_tac (simpset() addsimps [le_add1, le_imp_less_Suc])));
qed "SC_case";

Goal "CONST k l < ack(k, list_add l)";
by (Simp_tac 1);
qed "CONST_case";

Goalw [PROJ_def] "ALL i. PROJ i l < ack(0, list_add l)";
by (Simp_tac 1);
by (induct_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (case_tac "i" 1);
by (asm_simp_tac (simpset() addsimps [le_add1, le_imp_less_Suc]) 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [less_le_trans] 
                       addSIs [le_add2]) 1);
qed_spec_mp "PROJ_case";

(** COMP case **)

Goal "fs : lists(PRIMREC Int {f. EX kf. ALL l. f l < ack(kf, list_add l)}) \
\     ==> EX k. ALL l. list_add (map(%f. f l) fs) < ack(k, list_add l)";
by (etac lists.induct 1);
by (res_inst_tac [("x","0")] exI 1 THEN Asm_simp_tac 1);
by Safe_tac;
by (Asm_simp_tac 1);
by (rtac exI 1);
by (blast_tac (claset() addIs [add_less_mono, ack_add_bound, less_trans]) 1);
qed "COMP_map_lemma";

Goalw [COMP_def]
 "[| ALL l. g l < ack(kg, list_add l);           \
\    fs: lists(PRIMREC Int {f. EX kf. ALL l. f l < ack(kf, list_add l)}) \
\ |] ==> EX k. ALL l. COMP g fs  l < ack(k, list_add l)";
by (forward_tac [impOfSubs (Int_lower1 RS lists_mono)] 1);
by (etac (COMP_map_lemma RS exE) 1);
by (rtac exI 1);
by (rtac allI 1);
by (REPEAT (dtac spec 1));
by (etac less_trans 1);
by (blast_tac (claset() addIs [ack_less_mono2, ack_nest_bound, less_trans]) 1);
qed "COMP_case";

(** PREC case **)

Goalw [PREC_def]
 "[| ALL l. f l + list_add l < ack(kf, list_add l); \
\    ALL l. g l + list_add l < ack(kg, list_add l)  \
\ |] ==> PREC f g l + list_add l < ack(Suc(kf+kg), list_add l)";
by (case_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (claset() addIs [less_trans]) 1);
by (etac ssubst 1);  (*get rid of the needless assumption*)
by (induct_tac "a" 1);
by (ALLGOALS Asm_simp_tac);
(*base case*)
by (blast_tac (claset() addIs [le_add1 RS le_imp_less_Suc RS ack_less_mono1, 
			      less_trans]) 1);
(*induction step*)
by (rtac (Suc_leI RS le_less_trans) 1);
by (rtac (le_refl RS add_le_mono RS le_less_trans) 1);
by (etac spec 2);
by (asm_simp_tac (simpset() addsimps [le_add2]) 1);
(*final part of the simplification*)
by (Asm_simp_tac 1);
by (rtac (le_add2 RS ack_le_mono1 RS le_less_trans) 1);
by (etac ack_less_mono2 1);
qed "PREC_case_lemma";

Goal "[| ALL l. f l < ack(kf, list_add l);        \
\        ALL l. g l < ack(kg, list_add l)         \
\     |] ==> EX k. ALL l. PREC f g l< ack(k, list_add l)";
by (rtac exI 1);
by (rtac allI 1);
by (rtac ([le_add1, PREC_case_lemma] MRS le_less_trans) 1);
by (REPEAT (blast_tac (claset() addIs [ack_add_bound2]) 1));
qed "PREC_case";

Goal "f:PRIMREC ==> EX k. ALL l. f l < ack(k, list_add l)";
by (etac PRIMREC.induct 1);
by (ALLGOALS 
    (blast_tac (claset() addIs [SC_case, CONST_case, PROJ_case, COMP_case, 
			       PREC_case])));
qed "ack_bounds_PRIMREC";

Goal "(%l. case l of [] => 0 | x#l' => ack(x,x)) ~: PRIMREC";
by (rtac notI 1);
by (etac (ack_bounds_PRIMREC RS exE) 1);
by (rtac less_irrefl 1);
by (dres_inst_tac [("x", "[x]")] spec 1);
by (Asm_full_simp_tac 1);
qed "ack_not_PRIMREC";

