(*  Title:      ZF/ex/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Checkerboard Problem, formalized inductively
*)

open Mutil;


(** Basic properties of evnodd **)

goalw thy [evnodd_def]
    "!!i j. [| <i,j>: A;  (i#+j) mod 2 = b |] ==> <i,j>: evnodd(A,b)";
by (fast_tac ZF_cs 1);
qed "evnoddI";

val major::prems = goalw thy [evnodd_def]
    "[| z: evnodd(A,b);     \
\       !!i j. [| z=<i,j>;  <i,j>: A;  (i#+j) mod 2 = b |] ==> P |] ==> P";
br (major RS CollectE) 1;
by (REPEAT (eresolve_tac [exE,conjE] 1));
by (resolve_tac prems 1);
by (REPEAT (fast_tac ZF_cs 1));
qed "evnoddE";


goalw thy [evnodd_def] "evnodd(A, b) <= A";
by (fast_tac ZF_cs 1);
qed "evnodd_subset";

(* Finite(X) ==> Finite(evnodd(X,b)) *)
bind_thm("Finite_evnodd", evnodd_subset RS subset_imp_lepoll RS lepoll_Finite);

goalw thy [evnodd_def] "evnodd(A Un B, b) = evnodd(A,b) Un evnodd(B,b)";
by (simp_tac (ZF_ss addsimps [Collect_Un]) 1);
qed "evnodd_Un";

goalw thy [evnodd_def] "evnodd(A - B, b) = evnodd(A,b) - evnodd(B,b)";
by (simp_tac (ZF_ss addsimps [Collect_Diff]) 1);
qed "evnodd_Diff";

goalw thy [evnodd_def]
    "evnodd(cons(<i,j>,C), b) = \
\    if((i#+j) mod 2 = b, cons(<i,j>, evnodd(C,b)), evnodd(C,b))";
by (asm_simp_tac (ZF_ss addsimps [evnodd_def, Collect_cons] 
                        setloop split_tac [expand_if]) 1);
by (fast_tac ZF_cs 1);
qed "evnodd_cons";

goalw thy [evnodd_def] "evnodd(0, b) = 0";
by (simp_tac (ZF_ss addsimps [evnodd_def]) 1);
qed "evnodd_0";


(*** Dominoes ***)

goal thy "!!d. d:domino ==> Finite(d)";
by (fast_tac (ZF_cs addSIs [Finite_cons, Finite_0] addEs [domino.elim]) 1);
qed "domino_Finite";

goal thy "!!d. [| d:domino; b<2 |] ==> EX i' j'. evnodd(d,b) = {<i',j'>}";
by (eresolve_tac [domino.elim] 1);
by (res_inst_tac [("k1", "i#+j")] (mod2_cases RS disjE) 2);
by (res_inst_tac [("k1", "i#+j")] (mod2_cases RS disjE) 1);
by (REPEAT_FIRST (ares_tac [add_type]));
(*Four similar cases: case (i#+j) mod 2 = b, 2#-b, ...*)
by (REPEAT (asm_simp_tac (arith_ss addsimps [evnodd_cons, evnodd_0, mod_succ,
					     succ_neq_self] 
                                   setloop split_tac [expand_if]) 1
           THEN fast_tac (ZF_cs addDs [ltD]) 1));
qed "domino_singleton";

val prems = goal thy "[| d:domino; b<2 |] ==> |evnodd(d,b)| = 1";
by (cut_facts_tac [prems MRS domino_singleton] 1);
by (REPEAT (etac exE 1));
by (asm_simp_tac (ZF_ss addsimps [cardinal_singleton]) 1);
qed "cardinal_evnodd_domino";


(*** Tilings ***)

(** The union of two disjoint tilings is a tiling **)

goal thy "!!t. t: tiling(A) ==> \
\              ALL u: tiling(A). t Int u = 0 --> t Un u : tiling(A)";
by (etac tiling.induct 1);
by (simp_tac (ZF_ss addsimps tiling.intrs) 1);
by (asm_full_simp_tac (ZF_ss addsimps [Int_Un_distrib, Un_assoc, Un_subset_iff,
				       subset_empty_iff RS iff_sym]) 1);
by (safe_tac ZF_cs);
by (resolve_tac tiling.intrs 1);
by (assume_tac 1);
by (fast_tac ZF_cs 1);
by (fast_tac eq_cs 1);
val lemma = result();

goal thy "!!t u. [| t: tiling(A);  u: tiling(A);  t Int u = 0 |] ==> \
\                t Un u : tiling(A)";
by (fast_tac (ZF_cs addIs [lemma RS bspec RS mp]) 1);
qed "tiling_UnI";

goal thy "!!t. t:tiling(domino) ==> Finite(t)";
by (eresolve_tac [tiling.induct] 1);
by (resolve_tac [Finite_0] 1);
by (fast_tac (ZF_cs addIs [domino_Finite, Finite_Un]) 1);
qed "tiling_domino_Finite";

(*Uses AC in the form of cardinal_disjoint_Un; could instead use
  tiling_domino_Finite, well_ord_cardinal_eqE and Finite_imp_well_ord*)
goal thy "!!t. t: tiling(domino) ==> |evnodd(t,0)| = |evnodd(t,1)|";
by (eresolve_tac [tiling.induct] 1);
by (simp_tac (ZF_ss addsimps [evnodd_def]) 1);
by (asm_simp_tac (ZF_ss addsimps [evnodd_Un]) 1);
by (rtac cardinal_disjoint_Un 1);
by (asm_simp_tac (arith_ss addsimps [cardinal_evnodd_domino]) 1);
by (asm_simp_tac (arith_ss addsimps [cardinal_evnodd_domino]) 1);
bw evnodd_def;
by (fast_tac (eq_cs addSEs [equalityE]) 1);
by (fast_tac (eq_cs addSEs [equalityE]) 1);
qed "tiling_domino_0_1";

goal thy "!!i n. [| i: nat;  n: nat |] ==> {i} * (n #+ n) : tiling(domino)";
by (nat_ind_tac "n" [] 1);
by (simp_tac (arith_ss addsimps tiling.intrs) 1);
by (asm_simp_tac (arith_ss addsimps [Un_assoc RS sym, Sigma_succ2]) 1);
by (resolve_tac tiling.intrs 1);
by (assume_tac 2);
by (subgoal_tac	   (*seems the easiest way of turning one to the other*)
    "{i}*{succ(n1#+n1)} Un {i}*{n1#+n1} = {<i,n1#+n1>, <i,succ(n1#+n1)>}" 1);
by (fast_tac eq_cs 2);
by (asm_simp_tac (arith_ss addsimps [domino.horiz]) 1);
by (fast_tac (eq_cs addEs [mem_irrefl, mem_asym]) 1);
qed "dominoes_tile_row";

goal thy "!!m n. [| m: nat;  n: nat |] ==> m * (n #+ n) : tiling(domino)";
by (nat_ind_tac "m" [] 1);
by (simp_tac (arith_ss addsimps tiling.intrs) 1);
by (asm_simp_tac (arith_ss addsimps [Sigma_succ1]) 1);
by (fast_tac (eq_cs addIs [tiling_UnI, dominoes_tile_row] 
                    addEs [mem_irrefl]) 1);
qed "dominoes_tile_matrix";


goal thy "!!m n. [| m: nat;  n: nat;  \
\                   t = (succ(m)#+succ(m))*(succ(n)#+succ(n));  \
\                   t' = t - {<0,0>} - {<succ(m#+m), succ(n#+n)>} |] ==> \
\                t' ~: tiling(domino)";
by (resolve_tac [notI] 1);
by (dresolve_tac [tiling_domino_0_1] 1);
by (subgoal_tac "|evnodd(t',0)| < |evnodd(t',1)|" 1);
by (asm_full_simp_tac (ZF_ss addsimps [lt_not_refl]) 1);
by (subgoal_tac "t : tiling(domino)" 1);
by (asm_simp_tac (ZF_ss addsimps [nat_succI, add_type, 
				  dominoes_tile_matrix]) 2);
by (subgoal_tac "(m#+m)#+(n#+n) = (m#+n)#+(m#+n)" 1);
by (asm_simp_tac (arith_ss addsimps add_ac) 2);
by (asm_full_simp_tac 
    (arith_ss addsimps [evnodd_Diff, evnodd_cons, evnodd_0, mod2_add_self,
			mod2_succ_succ, tiling_domino_0_1 RS sym]) 1);
by (resolve_tac [lt_trans] 1);
by (REPEAT
    (rtac Finite_imp_cardinal_Diff 1 
     THEN
     asm_simp_tac (arith_ss addsimps [tiling_domino_Finite, Finite_evnodd, 
				      Finite_Diff]) 1 
     THEN
     asm_simp_tac (arith_ss addsimps [evnoddI, nat_0_le RS ltD, mod2_add_self]) 1));
qed "mutil_not_tiling";
