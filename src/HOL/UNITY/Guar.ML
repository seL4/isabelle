(*  Title:      HOL/UNITY/Guar.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition"
*)

(*** existential properties ***)

Goalw [ex_prop_def]
     "[| ex_prop X; finite GG |] ==> GG Int X ~= {} --> (JN G:GG. G) : X";
by (etac finite_induct 1);
by (auto_tac (claset(), simpset() addsimps [Int_insert_left]));
qed_spec_mp "ex1";

Goalw [ex_prop_def]
     "ALL GG. finite GG & GG Int X ~= {} --> (JN G:GG. G) : X ==> ex_prop X";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{F,G}")] spec 1);
by Auto_tac;
qed "ex2";

(*Chandy & Sanders take this as a definition*)
Goal "ex_prop X = (ALL GG. finite GG & GG Int X ~= {} --> (JN G:GG. G) : X)";
by (blast_tac (claset() addIs [ex1,ex2]) 1);
qed "ex_prop_finite";

(*Their "equivalent definition" given at the end of section 3*)
Goal "ex_prop X = (ALL G. G:X = (ALL H. G <= H --> H: X))";
by Auto_tac;
by (rewrite_goals_tac [ex_prop_def, component_def]);
by (Blast_tac 1);
by Safe_tac;
by (stac Join_commute 2);
by (ALLGOALS Blast_tac);
qed "ex_prop_equiv";


(*** universal properties ***)

Goalw [uv_prop_def]
     "[| uv_prop X; finite GG |] ==> GG <= X --> (JN G:GG. G) : X";
by (etac finite_induct 1);
by (auto_tac (claset(), simpset() addsimps [Int_insert_left]));
qed_spec_mp "uv1";

Goalw [uv_prop_def]
     "ALL GG. finite GG & GG <= X --> (JN G:GG. G) : X  ==> uv_prop X";
by (rtac conjI 1);
by (Clarify_tac 2);
by (dres_inst_tac [("x", "{F,G}")] spec 2);
by (dres_inst_tac [("x", "{}")] spec 1);
by Auto_tac;
qed "uv2";

(*Chandy & Sanders take this as a definition*)
Goal "uv_prop X = (ALL GG. finite GG & GG <= X --> (JN G:GG. G) : X)";
by (blast_tac (claset() addIs [uv1,uv2]) 1);
qed "uv_prop_finite";


(*** guarantees ***)

val prems = Goal
     "(!!G. [| G : preserves v; F Join G : X |] ==> F Join G : Y) \
\     ==> F : X guarantees[v] Y";
by (simp_tac (simpset() addsimps [guar_def, component_def]) 1);
by (blast_tac (claset() addIs prems) 1);
qed "guaranteesI";

Goalw [guar_def, component_def]
     "[| F : X guarantees[v] Y;  G : preserves v;  F Join G : X |] \
\     ==> F Join G : Y";
by (Blast_tac 1);
qed "guaranteesD";

(*This version of guaranteesD matches more easily in the conclusion
  The major premise can no longer be  F<=H since we need to reason about G*)
Goalw [guar_def]
     "[| F : X guarantees[v] Y;  F Join G = H;  H : X;  G : preserves v |] \
\     ==> H : Y";
by (Blast_tac 1);
qed "component_guaranteesD";

Goalw [guar_def]
     "[| F: X guarantees[v] X'; Y <= X; X' <= Y' |] ==> F: Y guarantees[v] Y'";
by (Blast_tac 1);
qed "guarantees_weaken";

Goalw [guar_def]
     "[| F: X guarantees[v] Y;  preserves w <= preserves v |] \
\     ==> F: X guarantees[w] Y";
by (Blast_tac 1);
qed "guarantees_weaken_var";

Goalw [guar_def] "X <= Y ==> X guarantees[v] Y = UNIV";
by (Blast_tac 1);
qed "subset_imp_guarantees_UNIV";

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
Goalw [guar_def] "X <= Y ==> F : X guarantees[v] Y";
by (Blast_tac 1);
qed "subset_imp_guarantees";

(*Remark at end of section 4.1
Goalw [guar_def] "ex_prop Y = (Y = UNIV guarantees[v] Y)";
by (simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by (blast_tac (claset() addEs [equalityE]) 1);
qed "ex_prop_equiv2";
*)

(** Distributive laws.  Re-orient to perform miniscoping **)

Goalw [guar_def]
     "(UN i:I. X i) guarantees[v] Y = (INT i:I. X i guarantees[v] Y)";
by (Blast_tac 1);
qed "guarantees_UN_left";

Goalw [guar_def]
    "(X Un Y) guarantees[v] Z = (X guarantees[v] Z) Int (Y guarantees[v] Z)";
by (Blast_tac 1);
qed "guarantees_Un_left";

Goalw [guar_def]
     "X guarantees[v] (INT i:I. Y i) = (INT i:I. X guarantees[v] Y i)";
by (Blast_tac 1);
qed "guarantees_INT_right";

Goalw [guar_def]
    "Z guarantees[v] (X Int Y) = (Z guarantees[v] X) Int (Z guarantees[v] Y)";
by (Blast_tac 1);
qed "guarantees_Int_right";

Goal "(F : X guarantees[v] (INTER I Y)) = \
\     (ALL i:I. F : X guarantees[v] (Y i))";
by (simp_tac (simpset() addsimps [guarantees_INT_right]) 1);
qed "guarantees_INT_right_iff";

Goalw [guar_def] "(X guarantees[v] Y) = (UNIV guarantees[v] (-X Un Y))";
by (Blast_tac 1);
qed "shunting";

Goalw [guar_def] "(X guarantees[v] Y) = -Y guarantees[v] -X";
by (Blast_tac 1);
qed "contrapositive";

(** The following two can be expressed using intersection and subset, which
    is more faithful to the text but looks cryptic.
**)

Goalw [guar_def]
    "[| F : V guarantees[v] X;  F : (X Int Y) guarantees[v] Z |]\
\    ==> F : (V Int Y) guarantees[v] Z";
by (Blast_tac 1);
qed "combining1";

Goalw [guar_def]
    "[| F : V guarantees[v] (X Un Y);  F : Y guarantees[v] Z |]\
\    ==> F : V guarantees[v] (X Un Z)";
by (Blast_tac 1);
qed "combining2";

(** The following two follow Chandy-Sanders, but the use of object-quantifiers
    does not suit Isabelle... **)

(*Premise should be (!!i. i: I ==> F: X guarantees[v] Y i) *)
Goalw [guar_def]
     "ALL i:I. F : X guarantees[v] (Y i) ==> F : X guarantees[v] (INT i:I. Y i)";
by (Blast_tac 1);
qed "all_guarantees";

(*Premises should be [| F: X guarantees[v] Y i; i: I |] *)
Goalw [guar_def]
     "EX i:I. F : X guarantees[v] (Y i) ==> F : X guarantees[v] (UN i:I. Y i)";
by (Blast_tac 1);
qed "ex_guarantees";

(*** Additional guarantees laws, by lcp ***)

Goalw [guar_def]
    "[| F: U guarantees[v] V;  G: X guarantees[v] Y; \
\       F : preserves v;  G : preserves v |] \
\    ==> F Join G: (U Int X) guarantees[v] (V Int Y)";
by (Simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_assoc]) 1);
by (subgoal_tac "F Join G Join Ga = G Join (F Join Ga)" 1);
by (Asm_full_simp_tac 1);
by (asm_simp_tac (simpset() addsimps Join_ac) 1);
qed "guarantees_Join_Int";

Goalw [guar_def]
    "[| F: U guarantees[v] V;  G: X guarantees[v] Y; \
\       F : preserves v;  G : preserves v |]  \
\    ==> F Join G: (U Un X) guarantees[v] (V Un Y)";
by (Simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_assoc]) 1);
by (subgoal_tac "F Join G Join Ga = G Join (F Join Ga)" 1);
by (Asm_full_simp_tac 1);
by (asm_simp_tac (simpset() addsimps Join_ac) 1);
qed "guarantees_Join_Un";

Goalw [guar_def]
    "[| ALL i:I. F i : X i guarantees[v] Y i;  \
\       ALL i:I. F i : preserves v |] \
\    ==> (JOIN I F) : (INTER I X) guarantees[v] (INTER I Y)";
by Auto_tac;
by (ball_tac 1);
by (dres_inst_tac [("x", "JOIN I F Join G")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [Join_assoc RS sym, JN_absorb]) 1);
qed "guarantees_JN_INT";

Goalw [guar_def]
    "[| ALL i:I. F i : X i guarantees[v] Y i;  \
\       ALL i:I. F i : preserves v |] \
\    ==> (JOIN I F) : (UNION I X) guarantees[v] (UNION I Y)";
by Auto_tac;
by (ball_tac 1);
by (dres_inst_tac [("x", "JOIN I F Join G")] spec 1);
by (auto_tac
    (claset(),
     simpset() addsimps [Join_assoc RS sym, JN_absorb]));
qed "guarantees_JN_UN";


(*** guarantees[v] laws for breaking down the program, by lcp ***)

Goalw [guar_def]
     "[| F: X guarantees[v] Y;  G: preserves v |] \
\     ==> F Join G: X guarantees[v] Y";
by (Simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_assoc]) 1);
qed "guarantees_Join_I1";

Goal "[| G: X guarantees[v] Y;  F: preserves v |] \
\    ==> F Join G: X guarantees[v] Y";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [guarantees_Join_I1]) 1);
qed "guarantees_Join_I2";

Goalw [guar_def]
     "[| i : I;  F i: X guarantees[v] Y;  \
\        ALL j:I. i~=j --> F j : preserves v |] \
\     ==> (JN i:I. (F i)) : X guarantees[v] Y";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "JOIN (I-{i}) F Join G")] spec 1);
by (auto_tac (claset(),
	      simpset() addsimps [JN_Join_diff, Join_assoc RS sym]));
qed "guarantees_JN_I";


(*** well-definedness ***)

Goalw [welldef_def] "F Join G: welldef ==> F: welldef";
by Auto_tac;
qed "Join_welldef_D1";

Goalw [welldef_def] "F Join G: welldef ==> G: welldef";
by Auto_tac;
qed "Join_welldef_D2";

(*** refinement ***)

Goalw [refines_def] "F refines F wrt X";
by (Blast_tac 1);
qed "refines_refl";

Goalw [refines_def]
     "[| H refines G wrt X;  G refines F wrt X |] ==> H refines F wrt X";
by Auto_tac;
qed "refines_trans";

Goalw [strict_ex_prop_def]
     "strict_ex_prop X \
\     ==> (ALL H. F Join H : X --> G Join H : X) = (F:X --> G:X)";
by (Blast_tac 1);
qed "strict_ex_refine_lemma";

Goalw [strict_ex_prop_def]
     "strict_ex_prop X \
\     ==> (ALL H. F Join H : welldef & F Join H : X --> G Join H : X) = \
\         (F: welldef Int X --> G:X)";
by Safe_tac;
by (eres_inst_tac [("x","SKIP"), ("P", "%H. ?PP H --> ?RR H")] allE 1);
by (auto_tac (claset() addDs [Join_welldef_D1, Join_welldef_D2], simpset()));
qed "strict_ex_refine_lemma_v";

Goal "[| strict_ex_prop X;  \
\        ALL H. F Join H : welldef Int X --> G Join H : welldef |] \
\     ==> (G refines F wrt X) = (G iso_refines F wrt X)";
by (res_inst_tac [("x","SKIP")] allE 1
    THEN assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [refines_def, iso_refines_def,
			 strict_ex_refine_lemma_v]) 1);
qed "ex_refinement_thm";


Goalw [strict_uv_prop_def]
     "strict_uv_prop X \
\     ==> (ALL H. F Join H : X --> G Join H : X) = (F:X --> G:X)";
by (Blast_tac 1);
qed "strict_uv_refine_lemma";

Goalw [strict_uv_prop_def]
     "strict_uv_prop X \
\     ==> (ALL H. F Join H : welldef & F Join H : X --> G Join H : X) = \
\         (F: welldef Int X --> G:X)";
by Safe_tac;
by (eres_inst_tac [("x","SKIP"), ("P", "%H. ?PP H --> ?RR H")] allE 1);
by (auto_tac (claset() addDs [Join_welldef_D1, Join_welldef_D2],
	      simpset()));
qed "strict_uv_refine_lemma_v";

Goal "[| strict_uv_prop X;  \
\        ALL H. F Join H : welldef Int X --> G Join H : welldef |] \
\     ==> (G refines F wrt X) = (G iso_refines F wrt X)";
by (res_inst_tac [("x","SKIP")] allE 1
    THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [refines_def, iso_refines_def,
					   strict_uv_refine_lemma_v]) 1);
qed "uv_refinement_thm";
