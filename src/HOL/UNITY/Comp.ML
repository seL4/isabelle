(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition

From Chandy and Sanders, "Reasoning About Program Composition"
*)

(*** component ***)

Goalw [component_def]
     "(F component G) = (Init G <= Init F & Acts F <= Acts G)";
by (force_tac (claset() addSIs [exI, program_equalityI], 
	       simpset() addsimps [Acts_Join]) 1);
qed "component_eq_subset";

Goalw [component_def] "SKIP component F";
by (force_tac (claset() addIs [Join_SKIP_left], simpset()) 1);
qed "component_SKIP";

Goalw [component_def] "F component F";
by (blast_tac (claset() addIs [Join_SKIP_right]) 1);
qed "component_refl";

AddIffs [component_SKIP, component_refl];

Goal "F component SKIP ==> F = SKIP";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [component_eq_subset]));
qed "SKIP_minimal";

Goalw [component_def] "F component (F Join G)";
by (Blast_tac 1);
qed "component_Join1";

Goalw [component_def] "G component (F Join G)";
by (simp_tac (simpset() addsimps [Join_commute]) 1);
by (Blast_tac 1);
qed "component_Join2";

Goalw [component_def] "i : I ==> (F i) component (JN i:I. (F i))";
by (blast_tac (claset() addIs [JN_absorb]) 1);
qed "component_JN";

Goalw [component_def] "[| F component G; G component H |] ==> F component H";
by (blast_tac (claset() addIs [Join_assoc RS sym]) 1);
qed "component_trans";

Goal "[| F component G; G component F |] ==> F=G";
by (full_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by (blast_tac (claset() addSIs [program_equalityI]) 1);
qed "component_antisym";

Goalw [component_def]
      "F component H = (EX G. F Join G = H & Disjoint F G)";
by (blast_tac (claset() addSIs [Diff_Disjoint, Join_Diff2]) 1);
qed "component_eq";

Goal "((F Join G) component H) = (F component H & G component H)";
by (simp_tac (simpset() addsimps [component_eq_subset, Acts_Join]) 1);
by (Blast_tac 1);
qed "Join_component_iff";


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
Goal "ex_prop X = (ALL G. G:X = (ALL H. G component H --> H: X))";
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
\     ==> F : X guar Y";
by (simp_tac (simpset() addsimps [guarantees_def, component_eq]) 1);
by (blast_tac (claset() addIs prems) 1);
qed "guaranteesI";

Goalw [guarantees_def, component_def]
     "[| F : X guar Y;  F Join G : X |] ==> F Join G : Y";
by (Blast_tac 1);
qed "guaranteesD";

(*This equation is more intuitive than the official definition*)
Goal "(F : X guar Y) = \
\     (ALL G. F Join G : X & Disjoint F G --> F Join G : Y)";
by (simp_tac (simpset() addsimps [guarantees_def, component_eq]) 1);
by (Blast_tac 1);
qed "guarantees_eq";

Goalw [guarantees_def] "[| F: X guar X'; Y <= X; X' <= Y' |] ==> F: Y guar Y'";
by (Blast_tac 1);
qed "guarantees_weaken";

Goalw [guarantees_def] "[| F: X guar Y; F component F' |] ==> F': X guar Y";
by (blast_tac (claset() addIs [component_trans]) 1);
qed "guarantees_weaken_prog";

Goalw [guarantees_def] "X <= Y ==> X guar Y = UNIV";
by (Blast_tac 1);
qed "subset_imp_guarantees_UNIV";

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
Goalw [guarantees_def] "X <= Y ==> F : X guar Y";
by (Blast_tac 1);
qed "subset_imp_guarantees";

(*Remark at end of section 4.1*)
Goalw [guarantees_def] "ex_prop Y = (Y = UNIV guar Y)";
by (simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by (blast_tac (claset() addEs [equalityE]) 1);
qed "ex_prop_equiv2";

(** Distributive laws.  Re-orient to perform miniscoping **)

Goalw [guarantees_def]
     "(UN X:XX. X) guar Y = (INT X:XX. X guar Y)";
by (Blast_tac 1);
qed "guarantees_UN_left";

Goalw [guarantees_def]
    "(X Un Y) guar Z = (X guar Z) Int (Y guar Z)";
by (Blast_tac 1);
qed "guarantees_Un_left";

Goalw [guarantees_def]
     "X guar (INT Y:YY. Y) = (INT Y:YY. X guar Y)";
by (Blast_tac 1);
qed "guarantees_INT_right";

Goalw [guarantees_def]
    "Z guar (X Int Y) = (Z guar X) Int (Z guar Y)";
by (Blast_tac 1);
qed "guarantees_Int_right";

Goalw [guarantees_def] "(X guar Y) = (UNIV guar (-X Un Y))";
by (Blast_tac 1);
qed "shunting";

Goalw [guarantees_def] "(X guar Y) = -Y guar -X";
by (Blast_tac 1);
qed "contrapositive";

(** The following two can be expressed using intersection and subset, which
    is more faithful to the text but looks cryptic.
**)

Goalw [guarantees_def]
    "[| F : V guar X;  F : (X Int Y) guar Z |]\
\    ==> F : (V Int Y) guar Z";
by (Blast_tac 1);
qed "combining1";

Goalw [guarantees_def]
    "[| F : V guar (X Un Y);  F : Y guar Z |]\
\    ==> F : V guar (X Un Z)";
by (Blast_tac 1);
qed "combining2";

(** The following two follow Chandy-Sanders, but the use of object-quantifiers
    does not suit Isabelle... **)

(*Premise should be (!!i. i: I ==> F: X guar Y i) *)
Goalw [guarantees_def]
     "ALL i:I. F : X guar (Y i) ==> F : X guar (INT i:I. Y i)";
by (Blast_tac 1);
qed "all_guarantees";

(*Premises should be [| F: X guar Y i; i: I |] *)
Goalw [guarantees_def]
     "EX i:I. F : X guar (Y i) ==> F : X guar (UN i:I. Y i)";
by (Blast_tac 1);
qed "ex_guarantees";

(*** Additional guarantees laws, by lcp ***)

Goalw [guarantees_def]
    "[| F: U guar V;  G: X guar Y |] ==> F Join G: (U Int X) guar (V Int Y)";
by (simp_tac (simpset() addsimps [Join_component_iff]) 1);
by (Blast_tac 1);
qed "guarantees_Join_Int";

Goalw [guarantees_def]
    "[| F: U guar V;  G: X guar Y |] ==> F Join G: (U Un X) guar (V Un Y)";
by (simp_tac (simpset() addsimps [Join_component_iff]) 1);
by (Blast_tac 1);
qed "guarantees_Join_Un";

Goal "((JOIN I F) component H) = (ALL i: I. F i component H)";
by (simp_tac (simpset() addsimps [component_eq_subset, Acts_JN]) 1);
by (Blast_tac 1);
qed "JN_component_iff";

Goalw [guarantees_def]
    "[| ALL i:I. F i : X i guar Y i |] \
\    ==> (JOIN I F) : (INTER I X) guar (INTER I Y)";
by (simp_tac (simpset() addsimps [JN_component_iff]) 1);
by (Blast_tac 1);
bind_thm ("guarantees_JN_INT", ballI RS result());

Goalw [guarantees_def]
    "[| ALL i:I. F i : X i guar Y i |] \
\    ==> (JOIN I F) : (UNION I X) guar (UNION I Y)";
by (simp_tac (simpset() addsimps [JN_component_iff]) 1);
by (Blast_tac 1);
bind_thm ("guarantees_JN_UN", ballI RS result());


(*** guarantees laws for breaking down the program, by lcp ***)

Goalw [guarantees_def]
    "F: X guar Y | G: X guar Y ==> F Join G: X guar Y";
by (simp_tac (simpset() addsimps [Join_component_iff]) 1);
by (Blast_tac 1);
qed "guarantees_Join_I";

Goalw [guarantees_def]
     "[| i : I;  F i: X guar Y |] ==> (JN i:I. (F i)) : X guar Y";
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
