(*  Title:      HOL/UNITY/Guar.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition"
Revised by Sidi Ehmety on January 2001
*)

Goal "(OK (insert i I) F) = (if i:I then OK I F else OK I F & (F i ok JOIN I F))";
by (auto_tac (claset() addIs [ok_sym], 
              simpset() addsimps [OK_iff_ok]));
qed "OK_insert_iff";



(*** existential properties ***)
Goalw [ex_prop_def]
 "[| ex_prop X; finite GG |] ==> \
\    GG Int X ~= {}--> OK GG (%G. G) -->(JN G:GG. G) : X";
by (etac finite_induct 1);
by (auto_tac (claset(), simpset() addsimps [OK_insert_iff,Int_insert_left]));
qed_spec_mp "ex1";


Goalw [ex_prop_def]
     "ALL GG. finite GG & GG Int X ~= {} --> OK GG (%G. G) -->(JN G:GG. G):X ==> ex_prop X";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{F,G}")] spec 1);
by (auto_tac (claset() addDs [ok_sym], 
              simpset() addsimps [OK_iff_ok]));
qed "ex2";


(*Chandy & Sanders take this as a definition*)
Goal "ex_prop X = (ALL GG. finite GG & GG Int X ~= {} & OK GG (%G. G)--> (JN G:GG. G) : X)";
by (blast_tac (claset() addIs [ex1,ex2]) 1);
qed "ex_prop_finite";


(*Their "equivalent definition" given at the end of section 3*)
Goal
 "ex_prop X = (ALL G. G:X = (ALL H. (G component_of H) --> H: X))";
by Auto_tac;
by (rewrite_goals_tac 
          [ex_prop_def, component_of_def]);
by Safe_tac;
by (stac Join_commute 3);
by (dtac  ok_sym 3);
by (REPEAT(Blast_tac 1));
qed "ex_prop_equiv";


(*** universal properties ***)
Goalw [uv_prop_def]
     "[| uv_prop X; finite GG |] ==>  \
\  GG <= X & OK GG (%G. G) --> (JN G:GG. G) : X";
by (etac finite_induct 1);
by (auto_tac (claset(), simpset() addsimps 
           [Int_insert_left, OK_insert_iff]));
qed_spec_mp "uv1";

Goalw [uv_prop_def]
     "ALL GG. finite GG & GG <= X & OK GG (%G. G)-->(JN G:GG. G):X  ==> uv_prop X";
by (rtac conjI 1);
by (Clarify_tac 2);
by (dres_inst_tac [("x", "{F,G}")] spec 2);
by (dres_inst_tac [("x", "{}")] spec 1);
by (auto_tac (claset() addDs [ok_sym], simpset() addsimps [OK_iff_ok]));
qed "uv2";

(*Chandy & Sanders take this as a definition*)
Goal "uv_prop X = (ALL GG. finite GG & GG <= X & OK GG (%G. G)--> (JN G:GG. G): X)";
by (blast_tac (claset() addIs [uv1,uv2]) 1);
qed "uv_prop_finite";

(*** guarantees ***)

val prems = Goal
     "(!!G. [| F ok G; F Join G : X |] ==> F Join G : Y) \
\     ==> F : X guarantees Y";
by (simp_tac (simpset() addsimps [guar_def, component_def]) 1);
by (blast_tac (claset() addIs prems) 1);
qed "guaranteesI";

Goalw [guar_def, component_def]
     "[| F : X guarantees Y;  F ok G;  F Join G : X |] \
\     ==> F Join G : Y";
by (Blast_tac 1);
qed "guaranteesD";

(*This version of guaranteesD matches more easily in the conclusion
  The major premise can no longer be  F<=H since we need to reason about G*)
Goalw [guar_def]
     "[| F : X guarantees Y;  F Join G = H;  H : X;  F ok G |] \
\     ==> H : Y";
by (Blast_tac 1);
qed "component_guaranteesD";

Goalw [guar_def]
     "[| F: X guarantees X'; Y <= X; X' <= Y' |] ==> F: Y guarantees Y'";
by (Blast_tac 1);
qed "guarantees_weaken";

Goalw [guar_def] "X <= Y ==> X guarantees Y = UNIV";
by (Blast_tac 1);
qed "subset_imp_guarantees_UNIV";

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
Goalw [guar_def] "X <= Y ==> F : X guarantees Y";
by (Blast_tac 1);
qed "subset_imp_guarantees";

(*Remark at end of section 4.1 *)

Goalw [guar_def] "ex_prop Y ==> (Y = UNIV guarantees Y)";
by (full_simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by Safe_tac;
by (dres_inst_tac [("x", "x")] spec 1);
by (dres_inst_tac [("x", "x")] spec 2);
by (dtac sym 2);
by (ALLGOALS(etac iffE));
by (ALLGOALS(full_simp_tac (simpset() addsimps [component_of_def])));
by (REPEAT(Blast_tac 1));
qed "ex_prop_imp";

Goalw [guar_def] "(Y = UNIV guarantees Y) ==> ex_prop(Y)";
by (simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by Safe_tac;
by (ALLGOALS(full_simp_tac (simpset() addsimps [component_of_def])));
by (dtac sym 2);
by (ALLGOALS(etac equalityE));
by (REPEAT(Blast_tac 1));
qed "guarantees_imp";

Goal "(ex_prop Y) = (Y = UNIV guarantees Y)";
by (rtac iffI 1);
by (rtac ex_prop_imp 1);
by (rtac guarantees_imp 2);
by (ALLGOALS(Asm_simp_tac));
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

Goal "[| F : Z guarantees X;  F : Z guarantees Y |] \
\    ==> F : Z guarantees (X Int Y)";
by (asm_simp_tac (simpset() addsimps [guarantees_Int_right]) 1);
qed "guarantees_Int_right_I";

Goal "(F : X guarantees (INTER I Y)) = \
\     (ALL i:I. F : X guarantees (Y i))";
by (simp_tac (simpset() addsimps [guarantees_INT_right]) 1);
qed "guarantees_INT_right_iff";

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
    "[| F: U guarantees V;  G: X guarantees Y; F ok G |] \
\    ==> F Join G: (U Int X) guarantees (V Int Y)"; 
by (Simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_assoc]) 1);
by (subgoal_tac "F Join G Join Ga = G Join (F Join Ga)" 1);
by (asm_full_simp_tac (simpset() addsimps [ok_commute]) 1); 
by (asm_simp_tac (simpset() addsimps Join_ac) 1);
qed "guarantees_Join_Int";

Goalw [guar_def]
    "[| F: U guarantees V;  G: X guarantees Y; F ok G |]  \
\    ==> F Join G: (U Un X) guarantees (V Un Y)";
by (Simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_assoc]) 1);
by (subgoal_tac "F Join G Join Ga = G Join (F Join Ga)" 1);
by (asm_full_simp_tac (simpset() addsimps [ok_commute]) 1);
by (asm_simp_tac (simpset() addsimps Join_ac) 1);
qed "guarantees_Join_Un";

Goalw [guar_def]
     "[| ALL i:I. F i : X i guarantees Y i;  OK I F |] \
\     ==> (JOIN I F) : (INTER I X) guarantees (INTER I Y)";
by Auto_tac;
by (ball_tac 1);
by (rename_tac "i" 1);
by (dres_inst_tac [("x", "JOIN (I-{i}) F Join G")] spec 1);
by (auto_tac
    (claset() addIs [OK_imp_ok],
     simpset() addsimps [Join_assoc RS sym, JN_Join_diff, JN_absorb]));
qed "guarantees_JN_INT";

Goalw [guar_def]
    "[| ALL i:I. F i : X i guarantees Y i;  OK I F |] \
\    ==> (JOIN I F) : (INTER I X) guarantees (INTER I Y)";
by Auto_tac;
by (ball_tac 1);
by (rename_tac "i" 1);
by (dres_inst_tac [("x", "JOIN (I-{i}) F Join G")] spec 1);
by (auto_tac
    (claset() addIs [OK_imp_ok],
     simpset() addsimps [Join_assoc RS sym, JN_Join_diff, JN_absorb]));
qed "guarantees_JN_INT";

Goalw [guar_def]
    "[| ALL i:I. F i : X i guarantees Y i;  OK I F |] \
\    ==> (JOIN I F) : (UNION I X) guarantees (UNION I Y)";
by Auto_tac;
by (ball_tac 1);
by (rename_tac "i" 1);
by (dres_inst_tac [("x", "JOIN (I-{i}) F Join G")] spec 1);
by (auto_tac
    (claset() addIs [OK_imp_ok],
     simpset() addsimps [Join_assoc RS sym, JN_Join_diff, JN_absorb]));
qed "guarantees_JN_UN";


(*** guarantees laws for breaking down the program, by lcp ***)

Goalw [guar_def]
     "[| F: X guarantees Y;  F ok G |] ==> F Join G: X guarantees Y";
by (Simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_assoc]) 1);
qed "guarantees_Join_I1";

Goal "[| G: X guarantees Y;  F ok G |] ==> F Join G: X guarantees Y";
by (asm_full_simp_tac (simpset() addsimps [inst "G" "G" Join_commute, 
                                           inst "G" "G" ok_commute]) 1);
by (blast_tac (claset() addIs [guarantees_Join_I1]) 1);
qed "guarantees_Join_I2";

Goalw [guar_def]
     "[| i : I;  F i: X guarantees Y;  OK I F |] \
\     ==> (JN i:I. (F i)) : X guarantees Y";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "JOIN (I-{i}) F Join G")] spec 1);
by (auto_tac (claset() addIs [OK_imp_ok],
	      simpset() addsimps [JN_Join_diff, JN_Join_diff, Join_assoc RS sym]));
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

(* Goalw [refines_def]
     "[| H refines G wrt X;  G refines F wrt X |] ==> H refines F wrt X"; 
by Auto_tac;
qed "refines_trans"; *)



Goalw [strict_ex_prop_def]
     "strict_ex_prop X \
\     ==> (ALL H. F ok H & G ok H & F Join H : X --> G Join H : X) \
\             = (F:X --> G:X)";
by Auto_tac;
qed "strict_ex_refine_lemma";

Goalw [strict_ex_prop_def]
     "strict_ex_prop X \
\     ==> (ALL H. F ok H & G ok H & F Join H : welldef & F Join H : X --> G Join H : X) = \
\         (F: welldef Int X --> G:X)";
by Safe_tac;
by (eres_inst_tac [("x","SKIP"), ("P", "%H. ?PP H --> ?RR H")] allE 1);
by (auto_tac (claset() addDs [Join_welldef_D1, Join_welldef_D2], simpset()));
qed "strict_ex_refine_lemma_v";

Goal "[| strict_ex_prop X;  \
\        ALL H. F ok H & G ok H & F Join H : welldef Int X --> G Join H : welldef |] \
\     ==> (G refines F wrt X) = (G iso_refines F wrt X)";
by (res_inst_tac [("x","SKIP")] allE 1
    THEN assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [refines_def, iso_refines_def,
			 strict_ex_refine_lemma_v]) 1);
qed "ex_refinement_thm";


Goalw [strict_uv_prop_def]
     "strict_uv_prop X \
\     ==> (ALL H. F ok H & G ok H & F Join H : X --> G Join H : X) = (F:X --> G:X)";
by (Blast_tac 1);
qed "strict_uv_refine_lemma";

Goalw [strict_uv_prop_def]
     "strict_uv_prop X \
\     ==> (ALL H. F ok H & G ok H & F Join H : welldef & F Join H : X --> G Join H : X) = \
\         (F: welldef Int X --> G:X)";
by Safe_tac;
by (eres_inst_tac [("x","SKIP"), ("P", "%H. ?PP H --> ?RR H")] allE 1);
by (auto_tac (claset() addDs [Join_welldef_D1, Join_welldef_D2],
	      simpset()));
qed "strict_uv_refine_lemma_v";

Goal "[| strict_uv_prop X;  \
\        ALL H. F ok H & G ok H & F Join H : welldef Int X --> G Join H : welldef |] \
\     ==> (G refines F wrt X) = (G iso_refines F wrt X)";
by (res_inst_tac [("x","SKIP")] allE 1
    THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [refines_def, iso_refines_def,
					   strict_uv_refine_lemma_v]) 1);
qed "uv_refinement_thm";

(* Added by Sidi Ehmety from Chandy & Sander, section 6 *)
Goalw [guar_def, component_of_def]
"(F:X guarantees Y) = (ALL H. H:X \\<longrightarrow> (F component_of H \\<longrightarrow> H:Y))";
by Auto_tac;
qed "guarantees_equiv";

Goalw [wg_def] "!!X. F:(X guarantees Y) ==> X <= (wg F Y)";
by Auto_tac;
qed "wg_weakest";

Goalw [wg_def, guar_def] "F:((wg F Y) guarantees Y)";
by (Blast_tac 1);
qed "wg_guarantees";

Goalw [wg_def]
  "(H: wg F X) = (F component_of H --> H:X)";
by (simp_tac (simpset() addsimps [guarantees_equiv]) 1);
by (rtac iffI 1);
by (res_inst_tac [("x", "{H}")] exI 2);
by (REPEAT(Blast_tac 1));
qed "wg_equiv";


Goal
"F component_of H ==> (H:wg F X) = (H:X)";
by (asm_simp_tac (simpset() addsimps [wg_equiv]) 1);
qed "component_of_wg";


Goal
"ALL FF. finite FF & FF Int X ~= {} --> OK FF (%F. F) \
\  --> (ALL F:FF. ((JN F:FF. F): wg F X) = ((JN F:FF. F):X))";
by (Clarify_tac 1);
by (subgoal_tac "F component_of (JN F:FF. F)" 1);
by (dres_inst_tac [("X", "X")] component_of_wg 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [component_of_def]) 1);
by (res_inst_tac [("x", "JN F:(FF-{F}). F")] exI 1);
by (auto_tac (claset() addIs [JN_Join_diff] addDs [ok_sym], 
              simpset() addsimps [OK_iff_ok]));
qed "wg_finite";

Goal "ex_prop X ==> (F:X) = (ALL H. H : wg F X)";
by (full_simp_tac (simpset() addsimps [ex_prop_equiv, wg_equiv]) 1);
by (Blast_tac 1);
qed "wg_ex_prop";

(** From Charpentier and Chandy "Theorems About Composition" **)
(* Proposition 2 *)
Goalw [wx_def] "(wx X)<=X";
by Auto_tac;
qed "wx_subset";

Goalw [wx_def]
"ex_prop (wx X)";
by (simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by Safe_tac;
by (Blast_tac 1);
by Auto_tac;
qed "wx_ex_prop";

Goalw [wx_def]
"ALL Z. Z<= X --> ex_prop Z --> Z <= wx X";
by Auto_tac;
qed "wx_weakest";


(* Proposition 6 *)
Goalw [ex_prop_def]
 "ex_prop({F. ALL G. F ok G --> F Join G:X})";
by Safe_tac;
by (dres_inst_tac [("x", "G Join Ga")] spec 1);
by (force_tac (claset(), simpset() addsimps [ok_Join_iff1, Join_assoc]) 1);
by (dres_inst_tac [("x", "F Join Ga")] spec 1);
by (full_simp_tac (simpset() addsimps [ok_Join_iff1]) 1);
by Safe_tac;
by (asm_simp_tac (simpset() addsimps [ok_commute]) 1);
by (subgoal_tac "F Join G = G Join F" 1);
by (asm_simp_tac (simpset() addsimps [Join_assoc]) 1);
by (simp_tac (simpset() addsimps [Join_commute]) 1);
qed "wx'_ex_prop";

(* Equivalence with the other definition of wx *)

Goalw [wx_def]
 "wx X = {F. ALL G. F ok G --> (F Join G):X}";
by Safe_tac;
by (full_simp_tac (simpset() addsimps [ex_prop_def]) 1);
by (dres_inst_tac [("x", "x")] spec 1);
by (dres_inst_tac [("x", "G")] spec 1);
by (forw_inst_tac [("c", "x Join G")] subsetD 1);
by Safe_tac;
by (Simp_tac 1);
by (res_inst_tac [("x", "{F. ALL G. F ok G --> F Join G:X}")] exI 1);
by Safe_tac;
by (rtac wx'_ex_prop 2);
by (rotate_tac 1 1);
by (dres_inst_tac [("x", "SKIP")] spec 1);
by Auto_tac;
qed "wx_equiv";


(* Propositions 7 to 11 are about this second definition of wx. And
   they are the same as the ones proved for the first definition of wx by equivalence *)
   
(* Proposition 12 *)
(* Main result of the paper *)
Goalw [guar_def] 
   "(X guarantees Y) = wx(-X Un Y)";
by (simp_tac (simpset() addsimps [wx_equiv]) 1);
qed "guarantees_wx_eq";

(* {* Corollary, but this result has already been proved elsewhere *}
 "ex_prop(X guarantees Y)";
  by (simp_tac (simpset() addsimps [guar_wx_iff, wx_ex_prop]) 1);
  qed "guarantees_ex_prop";
*)

(* Rules given in section 7 of Chandy and Sander's
    Reasoning About Program composition paper *)

Goal "Init F <= A ==> F:(stable A) guarantees (Always A)";
by (rtac guaranteesI 1);
by (simp_tac (simpset() addsimps [Join_commute]) 1);
by (rtac stable_Join_Always1 1);
by (ALLGOALS(asm_full_simp_tac (simpset() 
     addsimps [invariant_def, Join_stable])));
qed "stable_guarantees_Always";

(* To be moved to WFair.ML *)
Goal "[| F:A co A Un B; F:transient A |] ==> F:A leadsTo B";
by (dres_inst_tac [("B", "A-B")] constrains_weaken_L 1);
by (dres_inst_tac [("B", "A-B")] transient_strengthen 2);
by (rtac (ensuresI RS leadsTo_Basis) 3);
by (ALLGOALS(Blast_tac));
qed "leadsTo_Basis'";



Goal "F:transient A ==> F: (A co A Un B) guarantees (A leadsTo (B-A))";
by (rtac guaranteesI 1);
by (rtac leadsTo_Basis' 1);
by (dtac constrains_weaken_R 1);
by (assume_tac 2);
by (Blast_tac 1);
by (blast_tac (claset() addIs [Join_transient_I1]) 1);
qed "constrains_guarantees_leadsTo";







