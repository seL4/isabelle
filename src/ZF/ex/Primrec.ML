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

open Primrec;

val pr_typechecks = 
    nat_typechecks @ list.intrs @ 
    [lam_type, list_case_type, drop_type, map_type, apply_type, rec_type];

(** Useful special cases of evaluation ***)

val pr_ss = arith_ss 
    addsimps list.case_eqns
    addsimps [list_rec_Nil, list_rec_Cons, 
              drop_0, drop_Nil, drop_succ_Cons,
              map_Nil, map_Cons]
    setsolver (type_auto_tac pr_typechecks);

goalw Primrec.thy [SC_def]
    "!!x l. [| x:nat;  l: list(nat) |] ==> SC ` (Cons(x,l)) = succ(x)";
by (asm_simp_tac pr_ss 1);
qed "SC";

goalw Primrec.thy [CONST_def]
    "!!l. [| l: list(nat) |] ==> CONST(k) ` l = k";
by (asm_simp_tac pr_ss 1);
qed "CONST";

goalw Primrec.thy [PROJ_def]
    "!!l. [| x: nat;  l: list(nat) |] ==> PROJ(0) ` (Cons(x,l)) = x";
by (asm_simp_tac pr_ss 1);
qed "PROJ_0";

goalw Primrec.thy [COMP_def]
    "!!l. [| l: list(nat) |] ==> COMP(g,[f]) ` l = g` [f`l]";
by (asm_simp_tac pr_ss 1);
qed "COMP_1";

goalw Primrec.thy [PREC_def]
    "!!l. l: list(nat) ==> PREC(f,g) ` (Cons(0,l)) = f`l";
by (asm_simp_tac pr_ss 1);
qed "PREC_0";

goalw Primrec.thy [PREC_def]
    "!!l. [| x:nat;  l: list(nat) |] ==>  \
\         PREC(f,g) ` (Cons(succ(x),l)) = \
\         g ` Cons(PREC(f,g)`(Cons(x,l)), Cons(x,l))";
by (asm_simp_tac pr_ss 1);
qed "PREC_succ";

(*** Inductive definition of the PR functions ***)

(* c: primrec ==> c: list(nat) -> nat *)
val primrec_into_fun = primrec.dom_subset RS subsetD;

val pr_ss = pr_ss 
    setsolver (type_auto_tac ([primrec_into_fun] @ 
                              pr_typechecks @ primrec.intrs));

goalw Primrec.thy [ACK_def] "!!i. i:nat ==> ACK(i): primrec";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac pr_ss));
qed "ACK_in_primrec";

val ack_typechecks =
    [ACK_in_primrec, primrec_into_fun RS apply_type,
     add_type, list_add_type, nat_into_Ord] @ 
    nat_typechecks @ list.intrs @ primrec.intrs;

(*strict typechecking for the Ackermann proof; instantiates no vars*)
fun tc_tac rls =
    REPEAT
      (SOMEGOAL (test_assume_tac ORELSE' match_tac (rls @ ack_typechecks)));

goal Primrec.thy "!!i j. [| i:nat;  j:nat |] ==>  ack(i,j): nat";
by (tc_tac []);
qed "ack_type";

(** Ackermann's function cases **)

(*PROPERTY A 1*)
goalw Primrec.thy [ACK_def] "!!j. j:nat ==> ack(0,j) = succ(j)";
by (asm_simp_tac (pr_ss addsimps [SC]) 1);
qed "ack_0";

(*PROPERTY A 2*)
goalw Primrec.thy [ACK_def] "ack(succ(i), 0) = ack(i,1)";
by (asm_simp_tac (pr_ss addsimps [CONST,PREC_0]) 1);
qed "ack_succ_0";

(*PROPERTY A 3*)
(*Could be proved in Primrec0, like the previous two cases, but using
  primrec_into_fun makes type-checking easier!*)
goalw Primrec.thy [ACK_def]
    "!!i j. [| i:nat;  j:nat |] ==> \
\           ack(succ(i), succ(j)) = ack(i, ack(succ(i), j))";
by (asm_simp_tac (pr_ss addsimps [CONST,PREC_succ,COMP_1,PROJ_0]) 1);
qed "ack_succ_succ";

val ack_ss = 
    pr_ss addsimps [ack_0, ack_succ_0, ack_succ_succ, 
                    ack_type, nat_into_Ord];

(*PROPERTY A 4*)
goal Primrec.thy "!!i. i:nat ==> ALL j:nat. j < ack(i,j)";
by (etac nat_induct 1);
by (asm_simp_tac ack_ss 1);
by (rtac ballI 1);
by (eres_inst_tac [("n","j")] nat_induct 1);
by (DO_GOAL [rtac (nat_0I RS nat_0_le RS lt_trans),
             asm_simp_tac ack_ss] 1);
by (DO_GOAL [etac (succ_leI RS lt_trans1),
             asm_simp_tac ack_ss] 1);
qed "lt_ack2_lemma";
bind_thm ("lt_ack2", (lt_ack2_lemma RS bspec));

(*PROPERTY A 5-, the single-step lemma*)
goal Primrec.thy "!!i j. [| i:nat; j:nat |] ==> ack(i,j) < ack(i, succ(j))";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac (ack_ss addsimps [lt_ack2])));
qed "ack_lt_ack_succ2";

(*PROPERTY A 5, monotonicity for < *)
goal Primrec.thy "!!i j k. [| j<k; i:nat; k:nat |] ==> ack(i,j) < ack(i,k)";
by (forward_tac [lt_nat_in_nat] 1 THEN assume_tac 1);
by (etac succ_lt_induct 1);
by (assume_tac 1);
by (rtac lt_trans 2);
by (REPEAT (ares_tac ([ack_lt_ack_succ2, ack_type] @ pr_typechecks) 1));
qed "ack_lt_mono2";

(*PROPERTY A 5', monotonicity for le *)
goal Primrec.thy
    "!!i j k. [| j le k;  i: nat;  k:nat |] ==> ack(i,j) le ack(i,k)";
by (res_inst_tac [("f", "%j.ack(i,j)")] Ord_lt_mono_imp_le_mono 1);
by (REPEAT (ares_tac [ack_lt_mono2, ack_type RS nat_into_Ord] 1));
qed "ack_le_mono2";

(*PROPERTY A 6*)
goal Primrec.thy
    "!!i j. [| i:nat;  j:nat |] ==> ack(i, succ(j)) le ack(succ(i), j)";
by (nat_ind_tac "j" [] 1);
by (ALLGOALS (asm_simp_tac ack_ss));
by (rtac ack_le_mono2 1);
by (rtac (lt_ack2 RS succ_leI RS le_trans) 1);
by (REPEAT (ares_tac (ack_typechecks) 1));
qed "ack2_le_ack1";

(*PROPERTY A 7-, the single-step lemma*)
goal Primrec.thy "!!i j. [| i:nat; j:nat |] ==> ack(i,j) < ack(succ(i),j)";
by (rtac (ack_lt_mono2 RS lt_trans2) 1);
by (rtac ack2_le_ack1 4);
by (REPEAT (ares_tac ([nat_le_refl, ack_type] @ pr_typechecks) 1));
qed "ack_lt_ack_succ1";

(*PROPERTY A 7, monotonicity for < *)
goal Primrec.thy "!!i j k. [| i<j; j:nat; k:nat |] ==> ack(i,k) < ack(j,k)";
by (forward_tac [lt_nat_in_nat] 1 THEN assume_tac 1);
by (etac succ_lt_induct 1);
by (assume_tac 1);
by (rtac lt_trans 2);
by (REPEAT (ares_tac ([ack_lt_ack_succ1, ack_type] @ pr_typechecks) 1));
qed "ack_lt_mono1";

(*PROPERTY A 7', monotonicity for le *)
goal Primrec.thy
    "!!i j k. [| i le j; j:nat; k:nat |] ==> ack(i,k) le ack(j,k)";
by (res_inst_tac [("f", "%j.ack(j,k)")] Ord_lt_mono_imp_le_mono 1);
by (REPEAT (ares_tac [ack_lt_mono1, ack_type RS nat_into_Ord] 1));
qed "ack_le_mono1";

(*PROPERTY A 8*)
goal Primrec.thy "!!j. j:nat ==> ack(1,j) = succ(succ(j))";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac ack_ss));
qed "ack_1";

(*PROPERTY A 9*)
goal Primrec.thy "!!j. j:nat ==> ack(succ(1),j) = succ(succ(succ(j#+j)))";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac (ack_ss addsimps [ack_1, add_succ_right])));
qed "ack_2";

(*PROPERTY A 10*)
goal Primrec.thy
    "!!i1 i2 j. [| i1:nat; i2:nat; j:nat |] ==> \
\               ack(i1, ack(i2,j)) < ack(succ(succ(i1#+i2)), j)";
by (rtac (ack2_le_ack1 RSN (2,lt_trans2)) 1);
by (asm_simp_tac ack_ss 1);
by (rtac (add_le_self RS ack_le_mono1 RS lt_trans1) 1);
by (rtac (add_le_self2 RS ack_lt_mono1 RS ack_lt_mono2) 5);
by (tc_tac []);
qed "ack_nest_bound";

(*PROPERTY A 11*)
goal Primrec.thy
    "!!i1 i2 j. [| i1:nat; i2:nat; j:nat |] ==> \
\          ack(i1,j) #+ ack(i2,j) < ack(succ(succ(succ(succ(i1#+i2)))), j)";
by (res_inst_tac [("j", "ack(succ(1), ack(i1 #+ i2, j))")] lt_trans 1);
by (asm_simp_tac (ack_ss addsimps [ack_2]) 1);
by (rtac (ack_nest_bound RS lt_trans2) 2);
by (asm_simp_tac ack_ss 5);
by (rtac (add_le_mono RS leI RS leI) 1);
by (REPEAT (ares_tac ([add_le_self, add_le_self2, ack_le_mono1] @
                      ack_typechecks) 1));
qed "ack_add_bound";

(*PROPERTY A 12.  Article uses existential quantifier but the ALF proof
  used k#+4.  Quantified version must be nested EX k'. ALL i,j... *)
goal Primrec.thy
    "!!i j k. [| i < ack(k,j);  j:nat;  k:nat |] ==> \
\             i#+j < ack(succ(succ(succ(succ(k)))), j)";
by (res_inst_tac [("j", "ack(k,j) #+ ack(0,j)")] lt_trans 1);
by (rtac (ack_add_bound RS lt_trans2) 2);
by (asm_simp_tac (ack_ss addsimps [add_0_right]) 5);
by (REPEAT (ares_tac ([add_lt_mono, lt_ack2] @ ack_typechecks) 1));
qed "ack_add_bound2";

(*** MAIN RESULT ***)

val ack2_ss =
    ack_ss addsimps [list_add_Nil, list_add_Cons, list_add_type, nat_into_Ord];

goalw Primrec.thy [SC_def]
    "!!l. l: list(nat) ==> SC ` l < ack(1, list_add(l))";
by (etac list.elim 1);
by (asm_simp_tac (ack2_ss addsimps [succ_iff]) 1);
by (asm_simp_tac (ack2_ss addsimps [ack_1, add_le_self]) 1);
qed "SC_case";

(*PROPERTY A 4'? Extra lemma needed for CONST case, constant functions*)
goal Primrec.thy "!!j. [| i:nat; j:nat |] ==> i < ack(i,j)";
by (etac nat_induct 1);
by (asm_simp_tac (ack_ss addsimps [nat_0_le]) 1);
by (etac ([succ_leI, ack_lt_ack_succ1] MRS lt_trans1) 1);
by (tc_tac []);
qed "lt_ack1";

goalw Primrec.thy [CONST_def]
    "!!l. [| l: list(nat);  k: nat |] ==> CONST(k) ` l < ack(k, list_add(l))";
by (asm_simp_tac (ack2_ss addsimps [lt_ack1]) 1);
qed "CONST_case";

goalw Primrec.thy [PROJ_def]
    "!!l. l: list(nat) ==> ALL i:nat. PROJ(i) ` l < ack(0, list_add(l))";
by (asm_simp_tac ack2_ss 1);
by (etac list.induct 1);
by (asm_simp_tac (ack2_ss addsimps [nat_0_le]) 1);
by (asm_simp_tac ack2_ss 1);
by (rtac ballI 1);
by (eres_inst_tac [("n","x")] natE 1);
by (asm_simp_tac (ack2_ss addsimps [add_le_self]) 1);
by (asm_simp_tac ack2_ss 1);
by (etac (bspec RS lt_trans2) 1);
by (rtac (add_le_self2 RS succ_leI) 2);
by (tc_tac []);
qed "PROJ_case_lemma";
val PROJ_case = PROJ_case_lemma RS bspec;

(** COMP case **)

goal Primrec.thy
 "!!fs. fs : list({f: primrec .                                 \
\                  EX kf:nat. ALL l:list(nat).                  \
\                             f`l < ack(kf, list_add(l))})      \
\      ==> EX k:nat. ALL l: list(nat).                          \
\                list_add(map(%f. f ` l, fs)) < ack(k, list_add(l))";
by (etac list.induct 1);
by (DO_GOAL [res_inst_tac [("x","0")] bexI,
             asm_simp_tac (ack2_ss addsimps [lt_ack1, nat_0_le]),
             resolve_tac nat_typechecks] 1);
by (safe_tac ZF_cs);
by (asm_simp_tac ack2_ss 1);
by (rtac (ballI RS bexI) 1);
by (rtac (add_lt_mono RS lt_trans) 1);
by (REPEAT (FIRSTGOAL (etac bspec)));
by (rtac ack_add_bound 5);
by (tc_tac []);
qed "COMP_map_lemma";

goalw Primrec.thy [COMP_def]
 "!!g. [| g: primrec;  kg: nat;                                 \
\         ALL l:list(nat). g`l < ack(kg, list_add(l));          \
\         fs : list({f: primrec .                               \
\                    EX kf:nat. ALL l:list(nat).                \
\                       f`l < ack(kf, list_add(l))})            \
\      |] ==> EX k:nat. ALL l: list(nat). COMP(g,fs)`l < ack(k, list_add(l))";
by (asm_simp_tac ZF_ss 1);
by (forward_tac [list_CollectD] 1);
by (etac (COMP_map_lemma RS bexE) 1);
by (rtac (ballI RS bexI) 1);
by (etac (bspec RS lt_trans) 1);
by (rtac lt_trans 2);
by (rtac ack_nest_bound 3);
by (etac (bspec RS ack_lt_mono2) 2);
by (tc_tac [map_type]);
qed "COMP_case";

(** PREC case **)

goalw Primrec.thy [PREC_def]
 "!!f g. [| ALL l:list(nat). f`l #+ list_add(l) < ack(kf, list_add(l)); \
\           ALL l:list(nat). g`l #+ list_add(l) < ack(kg, list_add(l)); \
\           f: primrec;  kf: nat;                                       \
\           g: primrec;  kg: nat;                                       \
\           l: list(nat)                                                \
\        |] ==> PREC(f,g)`l #+ list_add(l) < ack(succ(kf#+kg), list_add(l))";
by (etac list.elim 1);
by (asm_simp_tac (ack2_ss addsimps [[nat_le_refl, lt_ack2] MRS lt_trans]) 1);
by (asm_simp_tac ack2_ss 1);
by (etac ssubst 1);  (*get rid of the needless assumption*)
by (eres_inst_tac [("n","a")] nat_induct 1);
(*base case*)
by (DO_GOAL [asm_simp_tac ack2_ss, rtac lt_trans, etac bspec,
             assume_tac, rtac (add_le_self RS ack_lt_mono1),
             REPEAT o ares_tac (ack_typechecks)] 1);
(*ind step*)
by (asm_simp_tac (ack2_ss addsimps [add_succ_right]) 1);
by (rtac (succ_leI RS lt_trans1) 1);
by (res_inst_tac [("j", "g ` ?ll #+ ?mm")] lt_trans1 1);
by (etac bspec 2);
by (rtac (nat_le_refl RS add_le_mono) 1);
by (tc_tac []);
by (asm_simp_tac (ack2_ss addsimps [add_le_self2]) 1);
(*final part of the simplification*)
by (asm_simp_tac ack2_ss 1);
by (rtac (add_le_self2 RS ack_le_mono1 RS lt_trans1) 1);
by (etac ack_lt_mono2 5);
by (tc_tac []);
qed "PREC_case_lemma";

goal Primrec.thy
 "!!f g. [| f: primrec;  kf: nat;                               \
\           g: primrec;  kg: nat;                               \
\           ALL l:list(nat). f`l < ack(kf, list_add(l));        \
\           ALL l:list(nat). g`l < ack(kg, list_add(l))         \
\        |] ==> EX k:nat. ALL l: list(nat).                     \
\                   PREC(f,g)`l< ack(k, list_add(l))";
by (rtac (ballI RS bexI) 1);
by (rtac ([add_le_self, PREC_case_lemma] MRS lt_trans1) 1);
by (REPEAT
    (SOMEGOAL
     (FIRST' [test_assume_tac,
              match_tac (ack_typechecks),
              rtac (ack_add_bound2 RS ballI) THEN' etac bspec])));
qed "PREC_case";

goal Primrec.thy
    "!!f. f:primrec ==> EX k:nat. ALL l:list(nat). f`l < ack(k, list_add(l))";
by (etac primrec.induct 1);
by (safe_tac ZF_cs);
by (DEPTH_SOLVE
    (ares_tac ([SC_case, CONST_case, PROJ_case, COMP_case, PREC_case,
                       bexI, ballI] @ nat_typechecks) 1));
qed "ack_bounds_primrec";

goal Primrec.thy
    "~ (lam l:list(nat). list_case(0, %x xs. ack(x,x), l)) : primrec";
by (rtac notI 1);
by (etac (ack_bounds_primrec RS bexE) 1);
by (rtac lt_irrefl 1);
by (dres_inst_tac [("x", "[x]")] bspec 1);
by (asm_simp_tac ack2_ss 1);
by (asm_full_simp_tac (ack2_ss addsimps [add_0_right]) 1);
qed "ack_not_primrec";

