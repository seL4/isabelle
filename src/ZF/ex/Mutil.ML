(*  Title:      ZF/ex/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Checkerboard Problem, formalized inductively
*)

open Mutil;


(** Basic properties of evnodd **)

Goalw [evnodd_def] "<i,j>: evnodd(A,b) <-> <i,j>: A & (i#+j) mod 2 = b";
by (Blast_tac 1);
qed "evnodd_iff";

Goalw [evnodd_def] "evnodd(A, b) <= A";
by (Blast_tac 1);
qed "evnodd_subset";

(* Finite(X) ==> Finite(evnodd(X,b)) *)
bind_thm("Finite_evnodd", evnodd_subset RS subset_imp_lepoll RS lepoll_Finite);

Goalw [evnodd_def] "evnodd(A Un B, b) = evnodd(A,b) Un evnodd(B,b)";
by (simp_tac (simpset() addsimps [Collect_Un]) 1);
qed "evnodd_Un";

Goalw [evnodd_def] "evnodd(A - B, b) = evnodd(A,b) - evnodd(B,b)";
by (simp_tac (simpset() addsimps [Collect_Diff]) 1);
qed "evnodd_Diff";

Goalw [evnodd_def]
    "evnodd(cons(<i,j>,C), b) = \
\    (if (i#+j) mod 2 = b then cons(<i,j>, evnodd(C,b)) else evnodd(C,b))";
by (asm_simp_tac (simpset() addsimps [evnodd_def, Collect_cons]) 1);
qed "evnodd_cons";

Goalw [evnodd_def] "evnodd(0, b) = 0";
by (simp_tac (simpset() addsimps [evnodd_def]) 1);
qed "evnodd_0";

Addsimps [evnodd_cons, evnodd_0];

(*** Dominoes ***)

Goal "d:domino ==> Finite(d)";
by (blast_tac (claset() addSIs [Finite_cons, Finite_0] addEs [domino.elim]) 1);
qed "domino_Finite";

Goal "[| d:domino; b<2 |] ==> EX i' j'. evnodd(d,b) = {<i',j'>}";
by (eresolve_tac [domino.elim] 1);
by (res_inst_tac [("k1", "i#+j")] (mod2_cases RS disjE) 2);
by (res_inst_tac [("k1", "i#+j")] (mod2_cases RS disjE) 1);
by (REPEAT_FIRST (ares_tac [add_type]));
(*Four similar cases: case (i#+j) mod 2 = b, 2#-b, ...*)
by (REPEAT (asm_simp_tac (simpset() addsimps [mod_succ, succ_neq_self]) 1
	    THEN blast_tac (claset() addDs [ltD]) 1));
qed "domino_singleton";


(*** Tilings ***)

(** The union of two disjoint tilings is a tiling **)

Goal "t: tiling(A) ==> \
\              u: tiling(A) --> t Int u = 0 --> t Un u : tiling(A)";
by (etac tiling.induct 1);
by (simp_tac (simpset() addsimps tiling.intrs) 1);
by (asm_full_simp_tac (simpset() addsimps [Un_assoc,
					  subset_empty_iff RS iff_sym]) 1);
by (blast_tac (claset() addIs tiling.intrs) 1);
qed_spec_mp "tiling_UnI";

Goal "t:tiling(domino) ==> Finite(t)";
by (eresolve_tac [tiling.induct] 1);
by (rtac Finite_0 1);
by (blast_tac (claset() addSIs [Finite_Un] addIs [domino_Finite]) 1);
qed "tiling_domino_Finite";

Goal "t: tiling(domino) ==> |evnodd(t,0)| = |evnodd(t,1)|";
by (eresolve_tac [tiling.induct] 1);
by (simp_tac (simpset() addsimps [evnodd_def]) 1);
by (res_inst_tac [("b1","0")] (domino_singleton RS exE) 1);
by (Simp_tac 2 THEN assume_tac 1);
by (res_inst_tac [("b1","1")] (domino_singleton RS exE) 1);
by (Simp_tac 2 THEN assume_tac 1);
by Safe_tac;
by (subgoal_tac "ALL p b. p:evnodd(a,b) --> p~:evnodd(t,b)" 1);
by (asm_simp_tac 
    (simpset() addsimps [evnodd_Un, Un_cons, tiling_domino_Finite,
			 evnodd_subset RS subset_Finite,
			 Finite_imp_cardinal_cons]) 1);
by (blast_tac (claset() addSDs [evnodd_subset RS subsetD]
                        addEs [equalityE]) 1);
qed "tiling_domino_0_1";

Goal "[| i: nat;  n: nat |] ==> {i} * (n #+ n) : tiling(domino)";
by (induct_tac "n" 1);
by (simp_tac (simpset() addsimps tiling.intrs) 1);
by (asm_simp_tac (simpset() addsimps [Un_assoc RS sym, Sigma_succ2]) 1);
by (resolve_tac tiling.intrs 1);
by (assume_tac 2);
by (rename_tac "n'" 1);
by (subgoal_tac    (*seems the easiest way of turning one to the other*)
    "{i}*{succ(n'#+n')} Un {i}*{n'#+n'} = {<i,n'#+n'>, <i,succ(n'#+n')>}" 1);
by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [domino.horiz]) 1);
by (blast_tac (claset() addEs [mem_irrefl, mem_asym]) 1);
qed "dominoes_tile_row";

Goal "[| m: nat;  n: nat |] ==> m * (n #+ n) : tiling(domino)";
by (induct_tac "m" 1);
by (simp_tac (simpset() addsimps tiling.intrs) 1);
by (asm_simp_tac (simpset() addsimps [Sigma_succ1]) 1);
by (blast_tac (claset() addIs [tiling_UnI, dominoes_tile_row] 
                    addEs [mem_irrefl]) 1);
qed "dominoes_tile_matrix";

Goal "[| x=y; x<y |] ==> P";
by Auto_tac;
qed "eq_lt_E";

Goal "[| m: nat;  n: nat;                                 \
\        t = (succ(m)#+succ(m))*(succ(n)#+succ(n));       \
\        t' = t - {<0,0>} - {<succ(m#+m), succ(n#+n)>} |] \
\     ==> t' ~: tiling(domino)";
by (rtac notI 1);
by (dtac tiling_domino_0_1 1);
by (eres_inst_tac [("x", "|?A|")] eq_lt_E 1);
by (subgoal_tac "t : tiling(domino)" 1);
(*Requires a small simpset that won't move the succ applications*)
by (asm_simp_tac (ZF_ss addsimps [nat_succI, add_type, 
                                  dominoes_tile_matrix]) 2);
by (asm_full_simp_tac 
    (simpset() addsimps [evnodd_Diff, mod2_add_self,
                        mod2_succ_succ, tiling_domino_0_1 RS sym]) 1);
by (rtac lt_trans 1);
by (REPEAT
    (rtac Finite_imp_cardinal_Diff 1 
     THEN
     asm_simp_tac (simpset() addsimps [tiling_domino_Finite, Finite_evnodd, 
                                      Finite_Diff]) 1 
     THEN
     asm_simp_tac (simpset() addsimps [evnodd_iff, nat_0_le RS ltD, 
                                      mod2_add_self]) 1));
qed "mutil_not_tiling";
