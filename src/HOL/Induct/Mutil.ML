(*  Title:      HOL/Induct/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Chess Board Problem, formalized inductively
*)

Addsimps (tiling.intrs @ domino.intrs);
AddIs    tiling.intrs;

(** The union of two disjoint tilings is a tiling **)

Goal "t: tiling A ==> u: tiling A --> t <= -u --> t Un u : tiling A";
by (etac tiling.induct 1);
by (simp_tac (simpset() addsimps [Un_assoc]) 2);
by Auto_tac;
qed_spec_mp "tiling_UnI";

AddIs [tiling_UnI];

(*** Chess boards ***)

Goalw [lessThan_def]
    "lessThan(Suc n) <*> B = ({n} <*> B) Un ((lessThan n) <*> B)";
by Auto_tac;
qed "Sigma_Suc1";

Goalw [lessThan_def]
    "A <*> lessThan(Suc n) = (A <*> {n}) Un (A <*> (lessThan n))";
by Auto_tac;
qed "Sigma_Suc2";

Addsimps [Sigma_Suc1, Sigma_Suc2];

Goal "({i} <*> {n}) Un ({i} <*> {m}) = {(i,m), (i,n)}";
by Auto_tac;
qed "sing_Times_lemma";

Goal "{i} <*> lessThan(#2*n) : tiling domino";
by (induct_tac "n" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Un_assoc RS sym])));
by (rtac tiling.Un 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [sing_Times_lemma])));
qed "dominoes_tile_row";

AddSIs [dominoes_tile_row]; 

Goal "(lessThan m) <*> lessThan(#2*n) : tiling domino";
by (induct_tac "m" 1);
by Auto_tac;
qed "dominoes_tile_matrix";


(*** "colored" and Dominoes ***)

Goalw [colored_def]
    "colored b Int (insert (i,j) C) = \
\      (if (i+j) mod #2 = b then insert (i,j) (colored b Int C) \
\                          else colored b Int C)";
by Auto_tac;
qed "colored_insert";

Addsimps [colored_insert];

Goal "d:domino ==> finite d";
by (etac domino.elim 1);
by Auto_tac;
qed "domino_finite";
Addsimps [domino_finite];

Goal "d:domino ==> (EX i j. colored 0 Int d = {(i,j)}) & \
\                  (EX k l. colored 1 Int d = {(k,l)})";
by (etac domino.elim 1);
by (auto_tac (claset(), simpset() addsimps [mod_Suc]));
qed "domino_singletons";


(*** Tilings of dominoes ***)

Goal "t:tiling domino ==> finite t";
by (etac tiling.induct 1);
by Auto_tac;
qed "tiling_domino_finite";

Addsimps [tiling_domino_finite, Int_Un_distrib, Diff_Int_distrib];

Goal "t: tiling domino ==> card(colored 0 Int t) = card(colored 1 Int t)";
by (etac tiling.induct 1);
by (dtac domino_singletons 2);
by Auto_tac;
(*this lemma tells us that both "inserts" are non-trivial*)
by (subgoal_tac "ALL p C. C Int a = {p} --> p ~: t" 1);
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "tiling_domino_0_1";

(*Final argument is surprisingly complex*)
Goal "[| t : tiling domino;       \
\        (i+j) mod #2 = 0;  (k+l) mod #2 = 0;  \
\        {(i,j),(k,l)} <= t;  l ~= j |]    \
\     ==> (t - {(i,j)} - {(k,l)}) ~: tiling domino";
by (rtac notI 1);
by (subgoal_tac "card (colored 0 Int (t - {(i,j)} - {(k,l)})) < \
\                card (colored 1 Int (t - {(i,j)} - {(k,l)}))" 1);
by (force_tac (claset(), HOL_ss addsimps [tiling_domino_0_1]) 1);
by (asm_simp_tac (simpset() addsimps [tiling_domino_0_1 RS sym]) 1);
by (rtac less_trans 1);
by (ALLGOALS (force_tac (claset() addSIs [card_Diff1_less], 
			 simpset() addsimps [colored_def])));
qed "gen_mutil_not_tiling";

(*Apply the general theorem to the well-known case*)
Goal "[| t = lessThan(#2 * Suc m) <*> lessThan(#2 * Suc n) |] \
\     ==> t - {(0,0)} - {(Suc(#2*m), Suc(#2*n))} ~: tiling domino";
by (rtac gen_mutil_not_tiling 1);
by (blast_tac (claset() addSIs [dominoes_tile_matrix]) 1);
by Auto_tac;
qed "mutil_not_tiling";

