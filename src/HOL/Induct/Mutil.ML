(*  Title:      HOL/Induct/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Chess Board Problem, formalized inductively
*)

Addsimps tiling.intrs;
AddIs    tiling.intrs;

(** The union of two disjoint tilings is a tiling **)

Goal "t: tiling A ==> u: tiling A --> t <= -u --> t Un u : tiling A";
by (etac tiling.induct 1);
by (simp_tac (simpset() addsimps [Un_assoc]) 2);
by Auto_tac;
qed_spec_mp "tiling_UnI";

AddIs [tiling_UnI];

(*** Chess boards ***)

Goalw [below_def] "(i: below k) = (i<k)";
by Auto_tac;
qed "below_less_iff";
AddIffs [below_less_iff];

Goalw [below_def] "below 0 = {}";
by Auto_tac;
qed "below_0";
Addsimps [below_0];

Goalw [below_def]
    "below(Suc n) Times B = ({n} Times B) Un ((below n) Times B)";
by Auto_tac;
qed "Sigma_Suc1";

Goalw [below_def]
    "A Times below(Suc n) = (A Times {n}) Un (A Times (below n))";
by Auto_tac;
qed "Sigma_Suc2";

Addsimps [Sigma_Suc1, Sigma_Suc2];

Goal "({i} Times {n}) Un ({i} Times {m}) = {(i,m), (i,n)}";
by Auto_tac;
qed "sing_Times_lemma";

Goal "{i} Times below(n+n) : tiling domino";
by (induct_tac "n" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [Un_assoc RS sym])));
by (resolve_tac tiling.intrs 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [sing_Times_lemma, domino.horiz])));
qed "dominoes_tile_row";

AddSIs [dominoes_tile_row]; 

Goal "(below m) Times below(n+n) : tiling domino";
by (induct_tac "m" 1);
by Auto_tac;
qed "dominoes_tile_matrix";


(*** Basic properties of colored ***)

Goalw [colored_def] "finite X ==> finite(colored b X)";
by Auto_tac;
qed "finite_colored";

Goalw [colored_def] "colored b (A Un B) = colored b A Un colored b B";
by Auto_tac;
qed "colored_Un";

Goalw [colored_def] "colored b (A - B) = colored b A - colored b B";
by Auto_tac;
qed "colored_Diff";

Goalw [colored_def] "colored b {} = {}";
by Auto_tac;
qed "colored_empty";

Goalw [colored_def]
    "colored b (insert (i,j) C) = \
\      (if (i+j) mod 2 = b then insert (i,j) (colored b C) else colored b C)";
by Auto_tac;
qed "colored_insert";

Addsimps [finite_colored, colored_Un, colored_Diff, colored_empty, 
	  colored_insert];


(*** Dominoes ***)

Goal "d:domino ==> finite d";
by (etac domino.elim 1);
by Auto_tac;
qed "domino_finite";
Addsimps [domino_finite];

Goal "[| d:domino; b<2 |] ==> EX i j. colored b d = {(i,j)}";
by (etac domino.elim 1);
by (auto_tac (claset(), simpset() addsimps [mod_Suc]));
qed "domino_singleton";

Goal "d:domino \
\     ==> EX i j i' j'. colored 0 d = {(i,j)} & colored 1 d = {(i',j')}";
by (blast_tac (claset() addDs [domino_singleton]) 1);
qed "domino_singleton_01";

(*** Tilings of dominoes ***)

Goal "t:tiling domino ==> finite t";
by (eresolve_tac [tiling.induct] 1);
by Auto_tac;
qed "tiling_domino_finite";

Addsimps [tiling_domino_finite];

Goal "t: tiling domino ==> card(colored 0 t) = card(colored 1 t)";
by (eresolve_tac [tiling.induct] 1);
by (dtac domino_singleton_01 2);
by Auto_tac;
(*this lemma tells us that both "inserts" are non-trivial*)
by (subgoal_tac "ALL p b. p : colored b a --> p ~: colored b t" 1);
by (Asm_simp_tac 1);
by (auto_tac (claset(), simpset() addsimps [colored_def]));
qed "tiling_domino_0_1";

(*Final argument is surprisingly complex*)
Goal "[| t : tiling domino;       \
\        (i+j) mod 2 = 0;  (i'+j') mod 2 = 0;  \
\        {(i,j),(i',j')} <= t;  j' ~= j |]    \
\     ==> (t - {(i,j)} - {(i',j')}) ~: tiling domino";
by (rtac notI 1);
by (subgoal_tac "card (colored 0 (t - {(i,j)} - {(i',j')})) < \
\                card (colored 1 (t - {(i,j)} - {(i',j')}))" 1);
by (force_tac (claset(), HOL_ss addsimps [tiling_domino_0_1]) 1);
by (asm_simp_tac (simpset() addsimps [tiling_domino_0_1 RS sym]) 1);
by (rtac less_trans 1);
by (ALLGOALS (force_tac (claset() addSIs [card_Diff1_less], 
			 simpset() addsimps [colored_def])));
qed "gen_mutil_not_tiling";

(*Apply the general theorem to the well-known case*)
Goal "[| t = below(Suc m + Suc m) Times below(Suc n + Suc n) |] \
\     ==> t - {(0,0)} - {(Suc(m+m), Suc(n+n))} ~: tiling domino";
by (rtac gen_mutil_not_tiling 1);
by (blast_tac (claset() addSIs [dominoes_tile_matrix]) 1);
by Auto_tac;
qed "mutil_not_tiling";

