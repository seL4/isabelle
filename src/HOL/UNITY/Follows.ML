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

Goal "mono (h::'a::order => 'b::order) \
\     ==> (INT j. {s. j <= g s} LeadsTo {s. j <= f s}) <= \
\         (INT k. {s. k <= h (g s)} LeadsTo {s. k <= h (f s)})";
by Auto_tac;
by (rtac single_LeadsTo_I 1);
by (dres_inst_tac [("x", "g s")] spec 1);
by (etac LeadsTo_weaken 1);
by (ALLGOALS (blast_tac (claset() addIs [monoD, order_trans])));
qed "mono_LeadsTo_o";

Goalw [Follows_def] "F : (%s. c) Fols (%s. c)";
by Auto_tac; 
qed "Follows_constant";
AddIffs [Follows_constant];

Goalw [Follows_def] "mono h ==> f Fols g <= (h o f) Fols (h o g)";
by (Clarify_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [impOfSubs mono_Increasing_o,
			 impOfSubs mono_Always_o,
			 impOfSubs mono_LeadsTo_o RS INT_D]) 1);
qed "mono_Follows_o";

Goal "mono h ==> f Fols g <= (%x. h (f x)) Fols (%x. h (g x))";
by (dtac mono_Follows_o 1);
by (force_tac (claset(), simpset() addsimps [o_def]) 1);
qed "mono_Follows_apply";

Goalw [Follows_def]
     "[| F : f Fols g;  F: g Fols h |] ==> F : f Fols h";
by (asm_full_simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (blast_tac (claset() addIs [order_trans, LeadsTo_Trans]) 1);
qed "Follows_trans";


(** Destructiom rules **)

Goalw [Follows_def]
     "F : f Fols g ==> F : Increasing f";
by (Blast_tac 1);
qed "Follows_Increasing1";

Goalw [Follows_def]
     "F : f Fols g ==> F : Increasing g";
by (Blast_tac 1);
qed "Follows_Increasing2";

Goalw [Follows_def]
     "F : f Fols g ==> F : Always {s. f s <= g s}";
by (Blast_tac 1);
qed "Follows_Bounded";

Goalw [Follows_def]
     "F : f Fols g ==> F : {s. k <= g s} LeadsTo {s. k <= f s}";
by (Blast_tac 1);
qed "Follows_LeadsTo";

Goal "F : f Fols g ==> F : {s. k pfixLe g s} LeadsTo {s. k pfixLe f s}";
by (rtac single_LeadsTo_I 1);
by (Clarify_tac 1);
by (dtac Follows_LeadsTo 1);
by (etac LeadsTo_weaken 1);
by (blast_tac set_cs 1);
by (blast_tac (claset() addIs [pfixLe_trans, prefix_imp_pfixLe]) 1);
qed "Follows_LeadsTo_pfixLe";

Goal "F : f Fols g ==> F : {s. k pfixGe g s} LeadsTo {s. k pfixGe f s}";
by (rtac single_LeadsTo_I 1);
by (Clarify_tac 1);
by (dtac Follows_LeadsTo 1);
by (etac LeadsTo_weaken 1);
by (blast_tac set_cs 1);
by (blast_tac (claset() addIs [pfixGe_trans, prefix_imp_pfixGe]) 1);
qed "Follows_LeadsTo_pfixGe";


Goalw [Follows_def, Increasing_def, Stable_def]
     "[| F : Always {s. f s = f' s}; F : f Fols g |] ==> F : f' Fols g"; 
by Auto_tac;
by (etac Always_LeadsTo_weaken 3);
by (eres_inst_tac [("A", "{s. z <= f s}"), ("A'", "{s. z <= f s}")] 
                  Always_Constrains_weaken 1);
by Auto_tac;
by (dtac Always_Int_I 1);
by (assume_tac 1);
by (force_tac (claset() addIs [Always_weaken], simpset()) 1);
qed "Always_Follows1";

Goalw [Follows_def, Increasing_def, Stable_def]
     "[| F : Always {s. g s = g' s}; F : f Fols g |] ==> F : f Fols g'"; 
by Auto_tac;
by (etac Always_LeadsTo_weaken 3);
by (eres_inst_tac [("A", "{s. z <= g s}"), ("A'", "{s. z <= g s}")] 
                  Always_Constrains_weaken 1);
by Auto_tac;
by (dtac Always_Int_I 1);
by (assume_tac 1);
by (force_tac (claset() addIs [Always_weaken], simpset()) 1);
qed "Always_Follows2";


(** Union properties (with the subset ordering) **)

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
    "[| F : f' Fols f;  F: g' Fols g |] \
\    ==> F : (%s. (f' s) Un (g' s)) Fols (%s. (f s) Un (g s))";
by (asm_full_simp_tac (simpset() addsimps [Increasing_Un, Always_Un]) 1);
by Auto_tac;
by (rtac LeadsTo_Trans 1);
by (blast_tac (claset() addIs [Follows_Un_lemma]) 1);
(*Weakening is used to exchange Un's arguments*)
by (blast_tac (claset() addIs [Follows_Un_lemma RS LeadsTo_weaken]) 1);
qed "Follows_Un";


(** Multiset union properties (with the multiset ordering) **)

Goalw [increasing_def, stable_def, constrains_def]
    "[| F : increasing f;  F: increasing g |] \
\    ==> F : increasing (%s. (f s) + (g s :: ('a::order) multiset))";
by Auto_tac;
by (dres_inst_tac [("x","f xa")] spec 1);
by (dres_inst_tac [("x","g xa")] spec 1);
by (ball_tac 1);
by (blast_tac (claset() addIs [union_le_mono, order_trans]) 1); 
qed "increasing_union";

Goalw [Increasing_def, Stable_def, Constrains_def, stable_def, constrains_def]
    "[| F : Increasing f;  F: Increasing g |] \
\    ==> F : Increasing (%s. (f s) + (g s :: ('a::order) multiset))";
by Auto_tac;
by (dres_inst_tac [("x","f xa")] spec 1);
by (dres_inst_tac [("x","g xa")] spec 1);
by (ball_tac 1);
by (blast_tac (claset()  addIs [union_le_mono, order_trans]) 1);
qed "Increasing_union";

Goal "[| F : Always {s. f' s <= f s}; F : Always {s. g' s <= g s} |] \
\     ==> F : Always {s. f' s + g' s <= f s + (g s :: ('a::order) multiset)}";
by (asm_full_simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (blast_tac (claset()  addIs [union_le_mono]) 1);
qed "Always_union";

(*Except the last line, IDENTICAL to the proof script for Follows_Un_lemma*)
Goal "[| F : Increasing f; F : Increasing g; \
\        F : Increasing g'; F : Always {s. f' s <= f s};\
\        ALL k::('a::order) multiset. \
\          F : {s. k <= f s} LeadsTo {s. k <= f' s} |]\
\     ==> F : {s. k <= f s + g s} LeadsTo {s. k <= f' s + g s}";
by (rtac single_LeadsTo_I 1);
by (dres_inst_tac [("x", "f s")] IncreasingD 1);
by (dres_inst_tac [("x", "g s")] IncreasingD 1);
by (rtac LeadsTo_weaken 1);
by (rtac PSP_Stable 1);
by (eres_inst_tac [("x", "f s")] spec 1);
by (etac Stable_Int 1);
by (assume_tac 1);
by (Blast_tac 1);
by (blast_tac (claset() addIs [union_le_mono, order_trans]) 1); 
qed "Follows_union_lemma";

(*The !! is there to influence to effect of permutative rewriting at the end*)
Goalw [Follows_def]
     "!!g g' ::'b => ('a::order) multiset. \
\       [| F : f' Fols f;  F: g' Fols g |] \
\       ==> F : (%s. (f' s) + (g' s)) Fols (%s. (f s) + (g s))";
by (asm_full_simp_tac (simpset() addsimps [Increasing_union, Always_union]) 1);
by Auto_tac;
by (rtac LeadsTo_Trans 1);
by (blast_tac (claset() addIs [Follows_union_lemma]) 1);
(*now exchange union's arguments*)
by (simp_tac (simpset() addsimps [union_commute]) 1); 
by (blast_tac (claset() addIs [Follows_union_lemma]) 1);
qed "Follows_union";

Goal "!!f ::['c,'b] => ('a::order) multiset. \
\       [| ALL i: I. F : f' i Fols f i;  finite I |] \
\       ==> F : (%s. setsum (%i. f' i s) I) Fols (%s. setsum (%i. f i s) I)";
by (etac rev_mp 1); 
by (etac finite_induct 1);
by (asm_simp_tac (simpset() addsimps [Follows_union]) 2);
by (Simp_tac 1); 
qed "Follows_setsum";


(*Currently UNUSED, but possibly of interest*)
Goal "F : Increasing func ==> F : Stable {s. h pfixGe (func s)}";
by (asm_full_simp_tac
    (simpset() addsimps [Increasing_def, Stable_def, Constrains_def, 
			 constrains_def]) 1); 
by (blast_tac (claset() addIs [trans_Ge RS trans_genPrefix RS transD,
			       prefix_imp_pfixGe]) 1);
qed "Increasing_imp_Stable_pfixGe";

(*Currently UNUSED, but possibly of interest*)
Goal "ALL z. F : {s. z <= f s} LeadsTo {s. z <= g s} \
\     ==> F : {s. z pfixGe f s} LeadsTo {s. z pfixGe g s}";
by (rtac single_LeadsTo_I 1);
by (dres_inst_tac [("x", "f s")] spec 1);
by (etac LeadsTo_weaken 1);
by (blast_tac (claset() addIs [trans_Ge RS trans_genPrefix RS transD,
			       prefix_imp_pfixGe]) 2);
by (Blast_tac 1);
qed "LeadsTo_le_imp_pfixGe";
