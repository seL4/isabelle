(*  Title:      HOL/Induct/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Chess Board Problem, formalized inductively
*)

Addsimps tiling.intrs;

(** The union of two disjoint tilings is a tiling **)

goal thy "!!t. t: tiling A ==> \
\              u: tiling A --> t <= Compl u --> t Un u : tiling A";
by (etac tiling.induct 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [Un_assoc]) 1);
by (blast_tac (claset() addIs tiling.intrs) 1);
qed_spec_mp "tiling_UnI";


(*** Chess boards ***)

goalw thy [below_def] "(i: below k) = (i<k)";
by (Blast_tac 1);
qed "below_less_iff";
AddIffs [below_less_iff];

goalw thy [below_def] "below 0 = {}";
by (Simp_tac 1);
qed "below_0";
Addsimps [below_0];

goalw thy [below_def]
    "below(Suc n) Times B = ({n} Times B) Un ((below n) Times B)";
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (Blast_tac 1);
qed "Sigma_Suc1";

goalw thy [below_def]
    "A Times below(Suc n) = (A Times {n}) Un (A Times (below n))";
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (Blast_tac 1);
qed "Sigma_Suc2";

goal thy "{i} Times below(n+n) : tiling domino";
by (nat_ind_tac "n" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Un_assoc RS sym, Sigma_Suc2])));
by (resolve_tac tiling.intrs 1);
by (assume_tac 2);
by (subgoal_tac    (*seems the easiest way of turning one to the other*)
    "({i} Times {Suc(n+n)}) Un ({i} Times {n+n}) = \
\    {(i, n+n), (i, Suc(n+n))}" 1);
by (Blast_tac 2);
by (asm_simp_tac (simpset() addsimps [domino.horiz]) 1);
by Auto_tac;
qed "dominoes_tile_row";

goal thy "(below m) Times below(n+n) : tiling domino";
by (nat_ind_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Sigma_Suc1])));
by (blast_tac (claset() addSIs [tiling_UnI, dominoes_tile_row]
                       addSEs [below_less_iff RS iffD1 RS less_irrefl]) 1);
qed "dominoes_tile_matrix";


(*** Basic properties of evnodd ***)

goalw thy [evnodd_def] "(i,j): evnodd A b = ((i,j): A  &  (i+j) mod 2 = b)";
by (Simp_tac 1);
qed "evnodd_iff";

goalw thy [evnodd_def] "evnodd A b <= A";
by (rtac Int_lower1 1);
qed "evnodd_subset";

(* finite X ==> finite(evnodd X b) *)
bind_thm("finite_evnodd", evnodd_subset RS finite_subset);

goalw thy [evnodd_def] "evnodd (A Un B) b = evnodd A b Un evnodd B b";
by (Blast_tac 1);
qed "evnodd_Un";

goalw thy [evnodd_def] "evnodd (A - B) b = evnodd A b - evnodd B b";
by (Blast_tac 1);
qed "evnodd_Diff";

goalw thy [evnodd_def] "evnodd {} b = {}";
by (Simp_tac 1);
qed "evnodd_empty";

goalw thy [evnodd_def]
    "evnodd (insert (i,j) C) b = \
\      (if (i+j) mod 2 = b then insert (i,j) (evnodd C b) else evnodd C b)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "evnodd_insert";

Addsimps [finite_evnodd, evnodd_Un, evnodd_Diff, evnodd_empty, evnodd_insert];


(*** Dominoes ***)

goal thy "!!d. [| d:domino; b<2 |] ==> EX i j. evnodd d b = {(i,j)}";
by (eresolve_tac [domino.elim] 1);
by (res_inst_tac [("k1", "i+j")] (mod2_cases RS disjE) 2);
by (res_inst_tac [("k1", "i+j")] (mod2_cases RS disjE) 1);
by (REPEAT_FIRST assume_tac);
(*Four similar cases: case (i+j) mod 2 = b, 2#-b, ...*)
by (REPEAT (asm_full_simp_tac (simpset() addsimps [less_Suc_eq, mod_Suc]) 1
           THEN Blast_tac 1));
qed "domino_singleton";

goal thy "!!d. d:domino ==> finite d";
by (blast_tac (claset() addSEs [domino.elim]) 1);
qed "domino_finite";


(*** Tilings of dominoes ***)

goal thy "!!t. t:tiling domino ==> finite t";
by (eresolve_tac [tiling.induct] 1);
by (rtac Finites.emptyI 1);
by (blast_tac (claset() addSIs [finite_UnI] addIs [domino_finite]) 1);
qed "tiling_domino_finite";

goal thy "!!t. t: tiling domino ==> card(evnodd t 0) = card(evnodd t 1)";
by (eresolve_tac [tiling.induct] 1);
by (simp_tac (simpset() addsimps [evnodd_def]) 1);
by (res_inst_tac [("b1","0")] (domino_singleton RS exE) 1);
by (Simp_tac 2 THEN assume_tac 1);
by (res_inst_tac [("b1","1")] (domino_singleton RS exE) 1);
by (Simp_tac 2 THEN assume_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "ALL p b. p : evnodd a b --> p ~: evnodd ta b" 1);
by (asm_simp_tac (simpset() addsimps [tiling_domino_finite]) 1);
by (blast_tac (claset() addSDs [evnodd_subset RS subsetD] 
                        addEs  [equalityE]) 1);
qed "tiling_domino_0_1";

(*Final argument is surprisingly complex.  Note the use of small simpsets
  to avoid moving Sucs, etc.*)
goal thy "!!m n. [| t = below(Suc m + Suc m) Times below(Suc n + Suc n);   \
\                   t' = t - {(0,0)} - {(Suc(m+m), Suc(n+n))}              \
\                |] ==> t' ~: tiling domino";
by (rtac notI 1);
by (subgoal_tac "card(evnodd t' 0) < card(evnodd t' 1)" 1);
by (asm_full_simp_tac (HOL_ss addsimps [less_not_refl, tiling_domino_0_1]) 1);
by (subgoal_tac "t : tiling domino" 1);
by (asm_simp_tac (HOL_ss addsimps [dominoes_tile_matrix]) 2);
by (asm_full_simp_tac (simpset() 
		       addsimps [mod_less, tiling_domino_0_1 RS sym]) 1);
(*Cardinality is smaller because of the two elements fewer*)
by (rtac less_trans 1);
by (REPEAT
    (rtac card_Diff 1 
     THEN asm_simp_tac (simpset() addsimps [tiling_domino_finite]) 1 
     THEN asm_simp_tac (simpset() addsimps [mod_less, evnodd_iff]) 1));
qed "mutil_not_tiling";
