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
     "(!!G. [| F Join G : X;  Disjoint F G |] ==> F Join G : Y) \
\     ==> F : X guarantees Y";
by (simp_tac (simpset() addsimps [guar_def, component_eq]) 1);
by (blast_tac (claset() addIs prems) 1);
qed "guaranteesI";

Goalw [guar_def, component_def]
     "[| F : X guarantees Y;  F Join G : X |] ==> F Join G : Y";
by (Blast_tac 1);
qed "guaranteesD";

(*This version of guaranteesD matches more easily in the conclusion*)
Goalw [guar_def]
     "[| F : X guarantees Y;  H : X;  F <= H |] ==> H : Y";
by (Blast_tac 1);
qed "component_guaranteesD";

(*This equation is more intuitive than the official definition*)
Goal "(F : X guarantees Y) = \
\     (ALL G. F Join G : X & Disjoint F G --> F Join G : Y)";
by (simp_tac (simpset() addsimps [guar_def, component_eq]) 1);
by (Blast_tac 1);
qed "guarantees_eq";

Goalw [guar_def]
     "[| F: X guarantees X'; Y <= X; X' <= Y' |] ==> F: Y guarantees Y'";
by (Blast_tac 1);
qed "guarantees_weaken";

Goalw [guar_def]
     "[| F: X guarantees Y; F <= F' |] ==> F': X guarantees Y";
by (blast_tac (claset() addIs [component_trans]) 1);
qed "guarantees_weaken_prog";

Goalw [guar_def] "X <= Y ==> X guarantees Y = UNIV";
by (Blast_tac 1);
qed "subset_imp_guarantees_UNIV";

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
Goalw [guar_def] "X <= Y ==> F : X guarantees Y";
by (Blast_tac 1);
qed "subset_imp_guarantees";

(*Remark at end of section 4.1*)
Goalw [guar_def] "ex_prop Y = (Y = UNIV guarantees Y)";
by (simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by (blast_tac (claset() addEs [equalityE]) 1);
qed "ex_prop_equiv2";

(** Distributive laws.  Re-orient to perform miniscoping **)

Goalw [guar_def]
     "(UN i:I. X i) guarantees Y = (INT i:I. X i guarantees Y)";
by (Blast_tac 1);
qed "guarantees_UN_left";

Goalw [guar_def]
    "(X Un Y) guarantees Z = (X guarantees Z) Int (Y guarantees Z)";
by (Blast_tac 1);
qed "guarantees_Un_left";

Goalw [guar_def]
     "X guarantees (INT i:I. Y i) = (INT i:I. X guarantees Y i)";
by (Blast_tac 1);
qed "guarantees_INT_right";

Goalw [guar_def]
    "Z guarantees (X Int Y) = (Z guarantees X) Int (Z guarantees Y)";
by (Blast_tac 1);
qed "guarantees_Int_right";

Goalw [guar_def] "(X guarantees Y) = (UNIV guarantees (-X Un Y))";
by (Blast_tac 1);
qed "shunting";

Goalw [guar_def] "(X guarantees Y) = -Y guarantees -X";
by (Blast_tac 1);
qed "contrapositive";

(** The following two can be expressed using intersection and subset, which
    is more faithful to the text but looks cryptic.
**)

Goalw [guar_def]
    "[| F : V guarantees X;  F : (X Int Y) guarantees Z |]\
\    ==> F : (V Int Y) guarantees Z";
by (Blast_tac 1);
qed "combining1";

Goalw [guar_def]
    "[| F : V guarantees (X Un Y);  F : Y guarantees Z |]\
\    ==> F : V guarantees (X Un Z)";
by (Blast_tac 1);
qed "combining2";

(** The following two follow Chandy-Sanders, but the use of object-quantifiers
    does not suit Isabelle... **)

(*Premise should be (!!i. i: I ==> F: X guarantees Y i) *)
Goalw [guar_def]
     "ALL i:I. F : X guarantees (Y i) ==> F : X guarantees (INT i:I. Y i)";
by (Blast_tac 1);
qed "all_guarantees";

(*Premises should be [| F: X guarantees Y i; i: I |] *)
Goalw [guar_def]
     "EX i:I. F : X guarantees (Y i) ==> F : X guarantees (UN i:I. Y i)";
by (Blast_tac 1);
qed "ex_guarantees";

(*** Additional guarantees laws, by lcp ***)

Goalw [guar_def]
    "[| F: U guarantees V;  G: X guarantees Y |] \
\    ==> F Join G: (U Int X) guarantees (V Int Y)";
by (simp_tac (simpset() addsimps [Join_component_iff]) 1);
by (Blast_tac 1);
qed "guarantees_Join_Int";

Goalw [guar_def]
    "[| F: U guarantees V;  G: X guarantees Y |]  \
\    ==> F Join G: (U Un X) guarantees (V Un Y)";
by (simp_tac (simpset() addsimps [Join_component_iff]) 1);
by (Blast_tac 1);
qed "guarantees_Join_Un";

Goal "((JOIN I F) <= H) = (ALL i: I. F i <= H)";
by (simp_tac (simpset() addsimps [component_eq_subset, Acts_JN]) 1);
by (Blast_tac 1);
qed "JN_component_iff";

Goalw [guar_def]
    "[| ALL i:I. F i : X i guarantees Y i |] \
\    ==> (JOIN I F) : (INTER I X) guarantees (INTER I Y)";
by (simp_tac (simpset() addsimps [JN_component_iff]) 1);
by (Blast_tac 1);
bind_thm ("guarantees_JN_INT", ballI RS result());

Goalw [guar_def]
    "[| ALL i:I. F i : X i guarantees Y i |] \
\    ==> (JOIN I F) : (UNION I X) guarantees (UNION I Y)";
by (simp_tac (simpset() addsimps [JN_component_iff]) 1);
by (Blast_tac 1);
bind_thm ("guarantees_JN_UN", ballI RS result());


(*** guarantees laws for breaking down the program, by lcp ***)

Goalw [guar_def]
    "F: X guarantees Y | G: X guarantees Y ==> F Join G: X guarantees Y";
by (simp_tac (simpset() addsimps [Join_component_iff]) 1);
by (Blast_tac 1);
qed "guarantees_Join_I";

Goalw [guar_def]
     "[| i : I;  F i: X guarantees Y |] ==> (JN i:I. (F i)) : X guarantees Y";
by (simp_tac (simpset() addsimps [JN_component_iff]) 1);
by (Blast_tac 1);
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
