(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition

From Chandy and Sanders, "Reasoning About Program Composition"
*)

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper record_split_name;

Delsimps [split_paired_All];


(*** component ***)

Goalw [component_def] "component SKIP F";
by (force_tac (claset() addIs [Join_SKIP_left], simpset()) 1);
qed "component_SKIP";

Goalw [component_def] "component F F";
by (blast_tac (claset() addIs [Join_SKIP_right]) 1);
qed "component_refl";

AddIffs [component_SKIP, component_refl];

Goalw [component_def] "component F (F Join G)";
by (Blast_tac 1);
qed "component_Join1";

Goalw [component_def] "component G (F Join G)";
by (simp_tac (simpset() addsimps [Join_commute]) 1);
by (Blast_tac 1);
qed "component_Join2";

Goalw [component_def] "i : I ==> component (F i) (JN i:I. (F i))";
by (blast_tac (claset() addIs [JN_absorb]) 1);
qed "component_JN";

Goalw [component_def] "[| component F G; component G H |] ==> component F H";
by (blast_tac (claset() addIs [Join_assoc RS sym]) 1);
qed "component_trans";

Goalw [component_def] "component F G ==> Acts F <= Acts G";
by (force_tac (claset(), simpset() addsimps [Acts_Join]) 1);
qed "component_Acts";

Goalw [component_def,Join_def] "component F G ==> Init G <= Init F";
by Auto_tac;
qed "component_Init";

Goal "[| component F G; component G F |] ==> F=G";
by (blast_tac (claset() addSIs [program_equalityI, 
				component_Init, component_Acts]) 1);
qed "component_anti_sym";

Goalw [component_def]
      "component F H = (EX G. F Join G = H & Disjoint F G)";
by (blast_tac (claset() addSIs [Diff_Disjoint, Join_Diff2]) 1);
qed "component_eq";


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
Goal "ex_prop X = (ALL G. G:X = (ALL H. component G H --> H: X))";
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

(*This equation is more intuitive than the official definition*)
Goal "(F : X guarantees Y) = \
\     (ALL G. F Join G : X & Disjoint F G --> F Join G : Y)";
by (simp_tac (simpset() addsimps [guarantees_def, component_eq]) 1);
by (Blast_tac 1);
qed "guarantees_eq";

Goalw [guarantees_def] "X <= Y ==> X guarantees Y = UNIV";
by (Blast_tac 1);
qed "subset_imp_guarantees";

(*Remark at end of section 4.1*)
Goalw [guarantees_def] "ex_prop Y = (Y = UNIV guarantees Y)";
by (simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by (blast_tac (claset() addEs [equalityE]) 1);
qed "ex_prop_equiv2";

Goalw [guarantees_def]
     "(INT X:XX. X guarantees Y) = (UN X:XX. X) guarantees Y";
by (Blast_tac 1);
qed "INT_guarantees_left";

Goalw [guarantees_def]
     "(INT Y:YY. X guarantees Y) = X guarantees (INT Y:YY. Y)";
by (Blast_tac 1);
qed "INT_guarantees_right";

Goalw [guarantees_def] "(X guarantees Y) = (UNIV guarantees (-X Un Y))";
by (Blast_tac 1);
qed "shunting";

Goalw [guarantees_def] "(X guarantees Y) = -Y guarantees -X";
by (Blast_tac 1);
qed "contrapositive";

Goalw [guarantees_def]
    "V guarantees X Int ((X Int Y) guarantees Z) <= (V Int Y) guarantees Z";
by (Blast_tac 1);
qed "combining1";

Goalw [guarantees_def]
    "V guarantees (X Un Y) Int (Y guarantees Z) <= V guarantees (X Un Z)";
by (Blast_tac 1);
qed "combining2";

Goalw [guarantees_def]
     "ALL i:I. F : X guarantees (Y i) ==> F : X guarantees (INT i:I. Y i)";
by (Blast_tac 1);
qed "all_guarantees";

Goalw [guarantees_def]
     "EX i:I. F : X guarantees (Y i) ==> F : X guarantees (UN i:I. Y i)";
by (Blast_tac 1);
qed "ex_guarantees";

val prems = Goal
     "(!!G. [| F Join G : X;  Disjoint F G |] ==> F Join G : Y) \
\     ==> F : X guarantees Y";
by (simp_tac (simpset() addsimps [guarantees_def, component_eq]) 1);
by (blast_tac (claset() addIs prems) 1);
qed "guaranteesI";

Goalw [guarantees_def, component_def]
     "[| F : X guarantees Y;  F Join G : X;  compatible{F,G} |] \
\     ==> F Join G : Y";
by (Blast_tac 1);
qed "guaranteesD";


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
