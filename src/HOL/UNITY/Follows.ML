(*  Title:      HOL/UNITY/Follows
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Follows relation of Charpentier and Sivilotte
*)

(*Does this hold for "invariant"?*)
Goal "mono h ==> Always {s. f s <= g s} <= Always {s. h (f s) <= h (g s)}";
by (asm_simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (blast_tac (claset() addIs [monoD]) 1);
qed "mono_Always_o";

Goalw [Follows_def]
    "mono (h::'a::order => 'b::order) \
\    ==> (INT j. {s. j <= g s} LeadsTo {s. j <= f s}) <= \
\        (INT k. {s. k <= h (g s)} LeadsTo {s. k <= h (f s)})";
by Auto_tac;
by (rtac single_LeadsTo_I 1);
by (dres_inst_tac [("x", "g s")] spec 1);
by (etac LeadsTo_weaken 1);
by (ALLGOALS (blast_tac (claset() addIs [monoD, order_trans])));
qed "mono_LeadsTo_o";

Goalw [Follows_def] "mono h ==> f Follows g <= (h o f) Follows (h o g)";
by (Clarify_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [impOfSubs mono_Increasing_o,
			 impOfSubs mono_Always_o,
			 impOfSubs mono_LeadsTo_o RS INT_D]) 1);
qed "mono_Follows_o";

Goalw [Follows_def]
     "[| F : f Follows g;  F: g Follows h |] ==> F : f Follows h";
by (asm_full_simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (blast_tac (claset() addIs [order_trans, LeadsTo_Trans]) 1);
qed "Follows_trans";


(*Can replace "Un" by any sup.  But existing max only works for linorders.*)

Goalw [increasing_def, stable_def, constrains_def]
    "[| F : increasing f;  F: increasing g |] \
\    ==> F : increasing (%s. (f s) Un (g s))";
by Auto_tac;
by (dres_inst_tac [("x","f xa")] spec 1);
by (dres_inst_tac [("x","g xa")] spec 1);
by (blast_tac (claset() addSDs [bspec]) 1);
qed "increasing_Un";

Goalw [Increasing_def, Stable_def, Constrains_def, stable_def, constrains_def]
    "[| F : Increasing f;  F: Increasing g |] \
\    ==> F : Increasing (%s. (f s) Un (g s))";
by Auto_tac;
by (dres_inst_tac [("x","f xa")] spec 1);
by (dres_inst_tac [("x","g xa")] spec 1);
by (blast_tac (claset() addSDs [bspec]) 1);
qed "Increasing_Un";


Goal "[| F : Always {s. f' s <= f s}; F : Always {s. g' s <= g s} |] \
\     ==> F : Always {s. f' s Un g' s <= f s Un g s}";
by (asm_full_simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (Blast_tac 1);
qed "Always_Un";



Goalw [Increasing_def]
     "F : Increasing f ==> F : Stable {s. x <= f s}";
by (Blast_tac 1);
qed "IncreasingD";


(*Lemma to re-use the argument that one variable increases (progress)
  while the other variable doesn't decrease (safety)*)
Goal "[| F : Increasing f; F : Increasing g; \
\        F : Increasing g'; F : Always {s. f' s <= f s};\
\        ALL k. F : {s. k <= f s} LeadsTo {s. k <= f' s} |]\
\     ==> F : {s. k <= f s Un g s} LeadsTo {s. k <= f' s Un g s}";
by (rtac single_LeadsTo_I 1);
by (dres_inst_tac [("x", "f s")] IncreasingD 1);
by (dres_inst_tac [("x", "g s")] IncreasingD 1);
by (rtac LeadsTo_weaken 1);
by (rtac PSP_Stable 1);
by (eres_inst_tac [("x", "f s")] spec 1);
by (etac Stable_Int 1);
by (assume_tac 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed "Follows_Un_lemma";

Goalw [Follows_def]
    "[| F : f' Follows f;  F: g' Follows g |] \
\    ==> F : (%s. (f' s) Un (g' s)) Follows (%s. (f s) Un (g s))";
by (asm_full_simp_tac (simpset() addsimps [Increasing_Un, Always_Un]) 1);
by Auto_tac;
by (rtac LeadsTo_Trans 1);
by (blast_tac (claset() addIs [Follows_Un_lemma]) 1);
(*Weakening is used to exchange Un's arguments*)
by (blast_tac (claset() addIs [Follows_Un_lemma RS LeadsTo_weaken]) 1);
qed "Follows_Un";

