(*  Title:      HOL/ex/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Checkerboard Problem, formalized inductively
*)

open Mutil;

(*SHOULD NOT BE NECESSARY!*)
Addsimps [ball_rew,mem_Sigma_iff];

(** Basic properties of evnodd **)

goalw thy [evnodd_def]
    "(i,j): evnodd A b = ((i,j): A  &  (i+j) mod 2 = b)";
by (Simp_tac 1);
qed "evnodd_iff";

goalw thy [evnodd_def] "evnodd A b <= A";
by (rtac Int_lower1 1);
qed "evnodd_subset";

(* finite X ==> finite(evnodd X b) *)
bind_thm("finite_evnodd", evnodd_subset RS finite_subset);

goalw thy [evnodd_def] "evnodd (A Un B) b = evnodd A b Un evnodd B b";
by (fast_tac eq_cs 1);
qed "evnodd_Un";

goalw thy [evnodd_def] "evnodd (A - B) b = evnodd A b - evnodd B b";
by (fast_tac eq_cs 1);
qed "evnodd_Diff";

goalw thy [evnodd_def]
    "evnodd (insert (i,j) C) b = \
\    (if (i+j) mod 2 = b then insert (i,j) (evnodd C b) else evnodd C b)";
by (asm_full_simp_tac (!simpset addsimps [evnodd_def] 
             setloop (split_tac [expand_if] THEN' step_tac eq_cs)) 1);
qed "evnodd_insert";

goalw thy [evnodd_def] "evnodd {} b = {}";
by (Simp_tac 1);
qed "evnodd_empty";


(*** Evens and Odds ***)

val less_cs = set_cs addSEs [less_zeroE, less_SucE];

goal thy "!!k b. b<2 ==> k mod 2 = b | k mod 2 = (if b=1 then 0 else 1)";
by (subgoal_tac "k mod 2 < 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor]) 2);
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (fast_tac less_cs 1);
qed "mod2_cases";

goal thy "Suc(Suc(m)) mod 2 = m mod 2";
by (subgoal_tac "m mod 2 < 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor]) 2);
by (safe_tac less_cs);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mod_Suc])));
qed "mod2_Suc_Suc";
Addsimps [mod2_Suc_Suc];

goal thy "(m+m) mod 2 = 0";
by (nat_ind_tac "m" 1);
by (simp_tac (!simpset addsimps [mod_less]) 1);
by (asm_simp_tac (!simpset addsimps [mod2_Suc_Suc, add_Suc_right]) 1);
qed "mod2_add_self";
Addsimps [mod2_add_self];


(*** Dominoes ***)

goal thy "!!d. d:domino ==> finite d";
by (fast_tac (set_cs addSIs [finite_insertI, finite_emptyI] addEs [domino.elim]) 1);
qed "domino_finite";

goal thy "!!d. [| d:domino; b<2 |] ==> EX i' j'. evnodd d b = {(i',j')}";
by (eresolve_tac [domino.elim] 1);
by (res_inst_tac [("k1", "i+j")] (mod2_cases RS disjE) 2);
by (res_inst_tac [("k1", "i+j")] (mod2_cases RS disjE) 1);
by (REPEAT_FIRST assume_tac);
(*Four similar cases: case (i+j) mod 2 = b, 2#-b, ...*)
by (REPEAT (asm_simp_tac (!simpset addsimps
                          [evnodd_insert, evnodd_empty, mod_Suc,
                           Suc_n_not_n] 
                          setloop split_tac [expand_if]) 1
           THEN fast_tac less_cs 1));
qed "domino_singleton";


(*** Tilings ***)

(** The union of two disjoint tilings is a tiling **)

goal thy "!!t. t: tiling A ==> \
\              ALL u: tiling A. t Int u = {} --> t Un u : tiling A";
by (etac tiling.induct 1);
by (simp_tac (!simpset addsimps tiling.intrs) 1);
by (asm_full_simp_tac (!simpset addsimps [Int_Un_distrib, Un_assoc]) 1);
by (safe_tac set_cs);
by (resolve_tac tiling.intrs 1);
by (assume_tac 1);
by (eresolve_tac ([bspec] RL [mp]) 1);
by (REPEAT (fast_tac (eq_cs addEs [equalityE]) 1));
val lemma = result();

goal thy "!!t u. [| t: tiling A;  u: tiling A;  t Int u = {} |] ==> \
\                t Un u : tiling A";
by (fast_tac (set_cs addIs [lemma RS bspec RS mp]) 1);
qed "tiling_UnI";

goal thy "!!t. t:tiling domino ==> finite t";
by (eresolve_tac [tiling.induct] 1);
by (rtac finite_emptyI 1);
by (fast_tac (set_cs addIs [domino_finite, finite_UnI]) 1);
qed "tiling_domino_finite";

goal thy "!!t. t: tiling domino ==> card(evnodd t 0) = card(evnodd t 1)";
by (eresolve_tac [tiling.induct] 1);
by (simp_tac (!simpset addsimps [evnodd_def]) 1);
by (res_inst_tac [("b1","0")] (domino_singleton RS exE) 1);
by (Simp_tac 2 THEN assume_tac 1);
by (res_inst_tac [("b1","1")] (domino_singleton RS exE) 1);
by (Simp_tac 2 THEN assume_tac 1);
by (step_tac HOL_cs 1);
by (subgoal_tac "ALL p b. p : evnodd a b --> p ~: evnodd ta b" 1);
by (asm_simp_tac (!simpset addsimps [evnodd_Un, Un_insert_left, 
                                     tiling_domino_finite,
                                     evnodd_subset RS finite_subset,
                                     card_insert_disjoint]) 1);
by (fast_tac (set_cs addSDs [evnodd_subset RS subsetD] addEs [equalityE]) 1);
qed "tiling_domino_0_1";


val [below_0, below_Suc] = nat_recs below_def;
Addsimps [below_0];
(*Strangely, below_Suc should NOT be added as rewrites -- 
  or Sigma_Suc1,2 cannot be used*)

goal thy "(i: below k) = (i<k)";
by (res_inst_tac [("x", "i")] spec 1);
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (asm_simp_tac (!simpset addsimps [below_Suc]) 1);
by (fast_tac set_cs 1);
qed "below_less_iff";

goal thy
    "Sigma (below (Suc A)) B = (Sigma {A} (%x. B(A))) Un Sigma (below A) B";
by (simp_tac (!simpset addsimps [below_Suc]) 1);
by (fast_tac (prod_cs addIs [equalityI]) 1);
qed "Sigma_Suc1";

goal thy
    "Sigma A (%x. below (Suc B)) = Sigma A (%x.{B}) Un Sigma A (%x.below B)";
by (simp_tac (!simpset addsimps [below_Suc]) 1);
by (fast_tac (prod_cs addIs [equalityI]) 1);
qed "Sigma_Suc2";

goal thy "Sigma {i} (%x. below (n + n)) : tiling domino";
by (nat_ind_tac "n" 1);
by (simp_tac (!simpset addsimps tiling.intrs) 1);
by (asm_simp_tac (!simpset addsimps [Un_assoc RS sym, Sigma_Suc2]) 1);
by (resolve_tac tiling.intrs 1);
by (assume_tac 2);
by (subgoal_tac    (*seems the easiest way of turning one to the other*)
    "Sigma {i} (%x. {Suc(n1+n1)}) Un Sigma {i} (%x. {n1+n1}) = \
\    {(i, n1+n1), (i, Suc(n1+n1))}" 1);
by (fast_tac (prod_cs addIs [equalityI]) 2);
by (asm_simp_tac (!simpset addsimps [domino.horiz]) 1);
by (fast_tac (prod_cs addIs [equalityI, lessI] addEs [less_irrefl, less_asym]
                      addDs [below_less_iff RS iffD1]) 1);
qed "dominoes_tile_row";

goal thy "Sigma (below m) (%x. below (n + n)) : tiling domino";
by (nat_ind_tac "m" 1);
by (simp_tac (!simpset addsimps (below_0::tiling.intrs)) 1);
by (asm_simp_tac (!simpset addsimps [Sigma_Suc1]) 1);
by (fast_tac (prod_cs addIs [equalityI, tiling_UnI, dominoes_tile_row] 
                      addEs [below_less_iff RS iffD1 RS less_irrefl]) 1);
qed "dominoes_tile_matrix";


goal thy "!!m n. [| m: nat;  n: nat;  \
\                   t = Sigma (below (Suc m + Suc m))\
\                             (%x. below (Suc n + Suc n));          \
\                   t' = t - {(0,0)} - {(Suc(m+m), Suc(n+n))}       \
\                |] ==> t' ~: tiling domino";
by (rtac notI 1);
by (dtac tiling_domino_0_1 1);
by (subgoal_tac "card(evnodd t' 0) < card(evnodd t' 1)" 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "t : tiling domino" 1);
(*Requires a small simpset that won't move the Suc applications*)
by (asm_simp_tac (HOL_ss addsimps [dominoes_tile_matrix]) 2);
by (subgoal_tac "(m+m)+(n+n) = (m+n)+(m+n)" 1);
by (asm_simp_tac (!simpset addsimps add_ac) 2);
by (asm_full_simp_tac 
    (!simpset addsimps [evnodd_Diff, evnodd_insert, evnodd_empty, 
                        mod_less, tiling_domino_0_1 RS sym]) 1);
by (rtac less_trans 1);
by (REPEAT
    (rtac card_Diff 1 
     THEN
     asm_simp_tac (!simpset addsimps [tiling_domino_finite, finite_evnodd]) 1 
     THEN
     asm_simp_tac (!simpset addsimps [mod_less, evnodd_iff, below_less_iff]) 1));
qed "mutil_not_tiling";

