(*  Title:      ZF/UNITY/Guar.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition"
Revised by Sidi Ehmety on January 2001

Proofs ported from HOL.
*)

Goal "OK(cons(i, I), F) <-> \
\ (i:I & OK(I, F)) | (i~:I & OK(I, F) & F(i) ok JOIN(I,F))";
by (asm_full_simp_tac (simpset() addsimps [OK_iff_ok]) 1);
(** Auto_tac proves the goal in one-step, but takes more time **)
by Safe_tac;
by (ALLGOALS(Clarify_tac));
by (REPEAT(blast_tac (claset() addIs [ok_sym]) 10));
by (REPEAT(Blast_tac 1));
qed "OK_cons_iff";

(*** existential properties ***)

Goalw [ex_prop_def] "ex_prop(X) ==> X<=program";
by (Asm_simp_tac 1);
qed "ex_imp_subset_program";

Goalw [ex_prop_def]
 "GG:Fin(program) ==> (ex_prop(X) \
\ --> GG Int X~=0 --> OK(GG, (%G. G)) -->(JN G:GG. G):X)";
by (etac Fin_induct 1);
by (ALLGOALS(asm_full_simp_tac 
         (simpset() addsimps [OK_cons_iff])));
(* Auto_tac proves the goal in one step *)
by Safe_tac;
by (ALLGOALS(Asm_full_simp_tac));
by (Fast_tac 1);
qed_spec_mp "ex1";

Goalw [ex_prop_def]
"X<=program ==> \
\(ALL GG. GG:Fin(program) & GG Int X ~= 0 --> OK(GG,(%G. G))-->(JN G:GG. G):X)\
\  --> ex_prop(X)";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{F,G}")] spec 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [OK_iff_ok])));
by Safe_tac;
by (auto_tac (claset() addIs [ok_sym], simpset()));
qed "ex2";

(*Chandy & Sanders take this as a definition*)

Goal "ex_prop(X) <-> (X<=program & \
\ (ALL GG. GG:Fin(program) & GG Int X ~= 0& OK(GG,( %G. G))-->(JN G:GG. G):X))";
by Auto_tac;
by (ALLGOALS(blast_tac (claset() addIs [ex1, ex2 RS mp] 
                                 addDs [ex_imp_subset_program])));
qed "ex_prop_finite";

(* Equivalent definition of ex_prop given at the end of section 3*)
Goalw [ex_prop_def, component_of_def]
"ex_prop(X) <-> \
\ X<=program & (ALL G:program. (G:X <-> (ALL H:program. (G component_of H) --> H:X)))";
by Safe_tac;
by (stac Join_commute 4);
by (dtac  ok_sym 4);
by (dres_inst_tac [("x", "G")] bspec 4);
by (dres_inst_tac [("x", "F")] bspec 3);
by Safe_tac;
by (REPEAT(Force_tac 1));
qed "ex_prop_equiv";

(*** universal properties ***)

Goalw [uv_prop_def] "uv_prop(X)==> X<=program";
by (Asm_simp_tac 1);
qed "uv_imp_subset_program";

Goalw [uv_prop_def]
     "GG:Fin(program) ==> \
\ (uv_prop(X)--> GG <= X & OK(GG, (%G. G)) --> (JN G:GG. G):X)";
by (etac Fin_induct 1);
by (auto_tac (claset(), simpset() addsimps 
           [OK_cons_iff]));
qed_spec_mp "uv1";

Goalw [uv_prop_def]
"X<=program  ==> (ALL GG. GG:Fin(program) & GG <= X & OK(GG,(%G. G)) \
\ --> (JN G:GG. G):X)  --> uv_prop(X)";
by Auto_tac;
by (Clarify_tac 2);
by (dres_inst_tac [("x", "{F,G}")] spec 2);
by (dres_inst_tac [("x", "0")] spec 1);
by (auto_tac (claset() addDs [ok_sym], 
    simpset() addsimps [OK_iff_ok]));
qed "uv2";

(*Chandy & Sanders take this as a definition*)
Goal 
"uv_prop(X) <-> X<=program & \
\ (ALL GG. GG:Fin(program) & GG <= X & OK(GG, %G. G) --> (JN G:GG. G): X)";
by Auto_tac;
by (REPEAT(blast_tac (claset() addIs [uv1,uv2 RS mp]
                               addDs [uv_imp_subset_program]) 1));
qed "uv_prop_finite";

(*** guarantees ***)
val major::prems = Goal
     "[| (!!G. [| F ok G; F Join G:X; G:program |] ==> F Join G : Y); F:program |]  \
\   ==> F : X guarantees Y";
by (cut_facts_tac prems 1);
by (simp_tac (simpset() addsimps [guar_def, component_def]) 1);
by (blast_tac (claset() addIs [major]) 1);
qed "guaranteesI";

Goalw [guar_def, component_def]
     "[| F : X guarantees Y;  F ok G;  F Join G:X; G:program |] \
\     ==> F Join G : Y";
by (Asm_full_simp_tac 1);
qed "guaranteesD";

(*This version of guaranteesD matches more easily in the conclusion
  The major premise can no longer be  F<=H since we need to reason about G*)

Goalw [guar_def]
     "[| F : X guarantees Y;  F Join G = H;  H : X;  F ok G; G:program |] \
\     ==> H : Y";
by (Blast_tac 1);
qed "component_guaranteesD";

Goalw [guar_def]
     "[| F: X guarantees X'; Y <= X; X' <= Y' |] ==> F: Y guarantees Y'";
by Auto_tac;
qed "guarantees_weaken";

Goalw [guar_def] "X <= Y \
\  ==> X guarantees Y = program";
by (Blast_tac 1);
qed "subset_imp_guarantees_program";

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
Goalw [guar_def] "[| X <= Y; F:program |] \
\  ==> F : X guarantees Y";
by (Blast_tac 1);
qed "subset_imp_guarantees";

Goalw [component_of_def] 
"F ok G ==> F component_of (F Join G)";
by (Blast_tac 1);
qed "component_of_Join1";

Goal "F ok G ==> G component_of (F Join G)";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [ok_sym, component_of_Join1]) 1);
qed "component_of_Join2";

(*Remark at end of section 4.1 *)
Goalw [guar_def, component_of_def] 
"ex_prop(Y) ==> (Y = (program guarantees Y))";
by (full_simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by (Clarify_tac 1);
by (rtac equalityI 1);
by Safe_tac;
by (dres_inst_tac [("x", "x")] bspec 2);
by (dres_inst_tac [("x", "x")] bspec 4);
by (dtac iff_sym 5);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [component_of_Join1])));
by (etac iffE 3);
by (ALLGOALS(full_simp_tac (simpset() addsimps [component_of_def])));
by Safe_tac;
by (REPEAT(Force_tac 1));
qed "ex_prop_imp";

Goalw [guar_def] "(Y = program guarantees Y) ==> ex_prop(Y)";
by (asm_simp_tac (simpset() addsimps [ex_prop_equiv]) 1);
by Safe_tac;
by (ALLGOALS(full_simp_tac (simpset() addsimps [component_of_def])));
by (dtac sym 2);
by (ALLGOALS(etac equalityE));
by (REPEAT(Force_tac 1));
qed "guarantees_imp";

Goal "(ex_prop(Y)) <-> (Y = program guarantees Y)";
by (blast_tac (claset() addIs [ex_prop_imp, guarantees_imp]) 1);
qed "ex_prop_equiv2";

(** Distributive laws.  Re-orient to perform miniscoping **)

Goalw [guar_def]
     "i:I ==>(UN i:I. X(i)) guarantees Y = (INT i:I. X(i) guarantees Y)";
by (rtac equalityI 1);
by Safe_tac;
by (Force_tac 2);
by (REPEAT(Blast_tac 1));
qed "guarantees_UN_left";

Goalw [guar_def]
     "(X Un Y) guarantees Z = (X guarantees Z) Int (Y guarantees Z)";
by (rtac equalityI 1);
by Safe_tac;
by (REPEAT(Blast_tac 1));
qed "guarantees_Un_left";

Goalw [guar_def]
     "i:I ==> X guarantees (INT i:I. Y(i)) = (INT i:I. X guarantees Y(i))";
by (rtac equalityI 1);
by Safe_tac;
by (REPEAT(Blast_tac 1));
qed "guarantees_INT_right";

Goalw [guar_def]
     "Z guarantees (X Int Y) = (Z guarantees X) Int (Z guarantees Y)";
by (Blast_tac 1);
qed "guarantees_Int_right";

Goal "[| F : Z guarantees X;  F : Z guarantees Y |] \
\    ==> F : Z guarantees (X Int Y)";
by (asm_simp_tac (simpset() addsimps [guarantees_Int_right]) 1);
qed "guarantees_Int_right_I";

Goal "i:I==> (F : X guarantees (INT i:I. Y(i))) <-> \
\     (ALL i:I. F : X guarantees Y(i))";
by (asm_simp_tac (simpset() addsimps [guarantees_INT_right, INT_iff]) 1);
by (Blast_tac 1);
qed "guarantees_INT_right_iff";


Goalw [guar_def] "(X guarantees Y) = (program guarantees ((program-X) Un Y))";
by Auto_tac;
qed "shunting";

Goalw [guar_def] "(X guarantees Y) = (program - Y) guarantees (program -X)";
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
     "[| ALL i:I. F : X guarantees Y(i); i:I |] \
\   ==> F : X guarantees (INT i:I. Y(i))";
by (Blast_tac 1);
qed "all_guarantees";

(*Premises should be [| F: X guarantees Y i; i: I |] *)
Goalw [guar_def]
     "EX i:I. F : X guarantees Y(i) ==> F : X guarantees (UN i:I. Y(i))";
by (Blast_tac 1);
qed "ex_guarantees";


(*** Additional guarantees laws, by lcp ***)

Goalw [guar_def]
    "[| F: U guarantees V;  G: X guarantees Y; F ok G |] \
\    ==> F Join G: (U Int X) guarantees (V Int Y)"; 
by (Simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_assoc]) 1);
by (subgoal_tac "F Join G Join x = G Join (F Join x)" 1);
by (asm_full_simp_tac (simpset() addsimps [ok_commute]) 1); 
by (asm_simp_tac (simpset() addsimps Join_ac) 1);
qed "guarantees_Join_Int";

Goalw [guar_def]
    "[| F: U guarantees V;  G: X guarantees Y; F ok G |]  \
\    ==> F Join G: (U Un X) guarantees (V Un Y)";
by (Simp_tac 1);
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [Join_assoc]) 1);
by (subgoal_tac "F Join G Join x = G Join (F Join x)" 1);
by (rotate_tac 4 1);
by (dres_inst_tac [("x", "F Join x")] bspec 1);
by (Simp_tac 1);
by (force_tac (claset(), simpset() addsimps [ok_commute]) 1);
by (asm_simp_tac (simpset() addsimps Join_ac) 1);
qed "guarantees_Join_Un";

Goalw [guar_def]
     "[| ALL i:I. F(i) : X(i) guarantees Y(i);  OK(I,F); i:I |] \
\     ==> (JN i:I. F(i)) : (INT i:I. X(i)) guarantees (INT i:I. Y(i))";
by Safe_tac;
by (Blast_tac 2);
by (dres_inst_tac [("x", "xa")] bspec 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [INT_iff])));
by Safe_tac;
by (rotate_tac ~1 1);
by (dres_inst_tac [("x", "(JN x:(I-{xa}). F(x)) Join G")] bspec 1);
by (auto_tac
    (claset() addIs [OK_imp_ok],
     simpset() addsimps [Join_assoc RS sym, JN_Join_diff, JN_absorb]));
qed "guarantees_JN_INT";

Goalw [guar_def]
    "[| ALL i:I. F(i) : X(i) guarantees Y(i);  OK(I,F) |] \
\    ==> JOIN(I,F) : (UN i:I. X(i)) guarantees (UN i:I. Y(i))";
by Auto_tac;
by (dres_inst_tac [("x", "xa")] bspec 1);
by (ALLGOALS(Asm_full_simp_tac));
by Safe_tac;
by (rotate_tac ~1 1);
by (dres_inst_tac [("x", "JOIN(I-{xa}, F) Join x")] bspec 1);
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
     "[| i:I; F(i): X guarantees Y;  OK(I,F) |] \
\     ==> (JN i:I. F(i)) : X guarantees Y";
by Safe_tac;
by (dres_inst_tac [("x", "JOIN(I-{i},F) Join G")] bspec 1);
by (Simp_tac 1);
by (auto_tac (claset() addIs [OK_imp_ok],
              simpset() addsimps [JN_Join_diff, Join_assoc RS sym]));
qed "guarantees_JN_I";

(*** well-definedness ***)

Goalw [welldef_def] "F Join G: welldef ==> programify(F): welldef";
by Auto_tac;
qed "Join_welldef_D1";

Goalw [welldef_def] "F Join G: welldef ==> programify(G): welldef";
by Auto_tac;
qed "Join_welldef_D2";

(*** refinement ***)

Goalw [refines_def] "F refines F wrt X";
by (Blast_tac 1);
qed "refines_refl";

(* More results on guarantees, added by Sidi Ehmety from Chandy & Sander, section 6 *)

Goalw [wg_def] "wg(F, X) <= program";
by Auto_tac;
qed "wg_type";

Goalw [guar_def] "X guarantees Y <= program";
by Auto_tac;
qed "guarantees_type";

Goalw [wg_def] "G:wg(F, X) ==> G:program & F:program";
by Auto_tac;
by (blast_tac (claset() addDs [guarantees_type RS subsetD]) 1);
qed "wgD2";

Goalw [guar_def, component_of_def]
"(F:X guarantees Y) <-> \
\  F:program & (ALL H:program. H:X --> (F component_of H --> H:Y))";
by Safe_tac;
by (REPEAT(Force_tac 1));
qed "guarantees_equiv";

Goalw [wg_def] "!!X. [| F:(X guarantees Y); X <= program |] ==> X <= wg(F,Y)";
by Auto_tac;
qed "wg_weakest";

Goalw [wg_def, guar_def] 
"F:program ==> F:wg(F,Y) guarantees Y";
by (Blast_tac 1);
qed "wg_guarantees";

Goalw [wg_def] "(H: wg(F,X)) <-> ((F component_of H --> H:X) & F:program & H:program)";
by (simp_tac (simpset() addsimps [guarantees_equiv]) 1);
by (rtac iffI 1);
by Safe_tac;
by (res_inst_tac [("x", "{H}")] bexI 4);
by (res_inst_tac [("x", "{H}")] bexI 3);
by (REPEAT(Blast_tac 1));
qed "wg_equiv";

Goal
"F component_of H ==> H:wg(F,X) <-> (H:X & F:program & H:program)";
by (asm_simp_tac (simpset() addsimps [wg_equiv]) 1);
qed "component_of_wg";

Goal
"ALL FF:Fin(program). FF Int X ~= 0 --> OK(FF, %F. F) \
\  --> (ALL F:FF. ((JN F:FF. F): wg(F,X)) <-> ((JN F:FF. F):X))";
by (Clarify_tac 1);
by (subgoal_tac "F component_of (JN F:FF. F)" 1);
by (dres_inst_tac [("X", "X")] component_of_wg 1);
by (force_tac (claset() addSDs [Fin.dom_subset RS subsetD RS PowD],
               simpset()) 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [component_of_def])));
by (res_inst_tac [("x", "JN F:(FF-{F}). F")] exI 1);
by (auto_tac (claset() addIs [JN_Join_diff] addDs [ok_sym], 
              simpset() addsimps [OK_iff_ok]));
qed "wg_finite";


(* "!!FF. [| FF:Fin(program); FF Int X ~=0; OK(FF, %F. F); G:FF |] 
   ==> JOIN(FF, %F. F):wg(G, X) <-> JOIN(FF, %F. F):X"  *)
val wg_finite2 = wg_finite RS bspec RS mp RS mp RS bspec;

Goal "ex_prop(X) ==> (F:X) <-> (ALL H:program. H : wg(F,X) & F:program)";
by (full_simp_tac (simpset() addsimps [ex_prop_equiv, wg_equiv]) 1);
by (Blast_tac 1);
qed "wg_ex_prop";

(** From Charpentier and Chandy "Theorems About Composition" **)
(* Proposition 2 *)
Goalw [wx_def] "wx(X)<=X";
by Auto_tac;
qed "wx_subset";

Goal
"ex_prop(wx(X))";
by (full_simp_tac (simpset() 
        addsimps [ex_prop_def, wx_def]) 1);
by Safe_tac;
by (Blast_tac 1);
by (ALLGOALS(res_inst_tac [("x", "xb")] bexI));
by (REPEAT(Force_tac 1));
qed "wx_ex_prop";

Goalw [wx_def]
"ALL Z. Z<=program --> Z<= X --> ex_prop(Z) --> Z <= wx(X)";
by Auto_tac;
qed "wx_weakest";

(* Proposition 6 *)
Goalw [ex_prop_def]
 "ex_prop({F:program. ALL G:program. F ok G --> F Join G:X})";
by Safe_tac;
by (dres_inst_tac [("x", "G Join Ga")] bspec 1);
by (Simp_tac 1);
by (force_tac (claset(), simpset() addsimps [Join_assoc]) 1);
by (dres_inst_tac [("x", "F Join Ga")] bspec 1);
by (Simp_tac 1);
by (Full_simp_tac 1);
by Safe_tac;
by (asm_simp_tac (simpset() addsimps [ok_commute]) 1);
by (subgoal_tac "F Join G = G Join F" 1);
by (asm_simp_tac (simpset() addsimps [Join_assoc]) 1);
by (simp_tac (simpset() addsimps [Join_commute]) 1);
qed "wx'_ex_prop";

(* Equivalence with the other definition of wx *)

Goalw [wx_def]
 "wx(X) = {F:program. ALL G:program. F ok G --> (F Join G):X}";
by (rtac equalityI 1);
by Safe_tac;
by (Blast_tac 1);
by (full_simp_tac (simpset() addsimps [ex_prop_def]) 1);
by Safe_tac;
by (dres_inst_tac [("x", "x")] bspec 1);
by (dres_inst_tac [("x", "G")] bspec 2);
by (forw_inst_tac [("c", "x Join G")] subsetD 3);
by Safe_tac;
by (Blast_tac 1);
by (Blast_tac 1);
by (res_inst_tac [("B", "{F:program. ALL G:program. F ok G --> F Join G:X}")] 
                   UnionI 1);
by Safe_tac;
by (rtac wx'_ex_prop 2);
by (rotate_tac 2 1);
by (dres_inst_tac [("x", "SKIP")] bspec 1);
by Auto_tac;
qed "wx_equiv";

(* Propositions 7 to 11 are all about this second definition of wx. And
   by equivalence between the two definition, they are the same as the ones proved *)


(* Proposition 12 *)
(* Main result of the paper *)
Goalw [guar_def]  "(X guarantees Y) = wx((program-X) Un Y)";
by (simp_tac (simpset() addsimps [wx_equiv]) 1);
by Auto_tac;
qed "guarantees_wx_eq";

(* 
{* Corollary, but this result has already been proved elsewhere *}
 "ex_prop(X guarantees Y)";
  by (simp_tac (simpset() addsimps [guar_wx_iff, wx_ex_prop]) 1);
  qed "guarantees_ex_prop";
*)

(* Rules given in section 7 of Chandy and Sander's
    Reasoning About Program composition paper *)

Goal "[| Init(F) <= A; F:program |] ==> F:(stable(A)) guarantees (Always(A))";
by (rtac guaranteesI 1);
by (assume_tac 2);
by (simp_tac (simpset() addsimps [Join_commute]) 1);
by (rtac stable_Join_Always1 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [invariant_def])));
by (auto_tac (claset(), simpset() addsimps [programify_def, initially_def]));
qed "stable_guarantees_Always";

(* To be moved to WFair.ML *)
Goal "[| F:A co A Un B; F:transient(A); st_set(B) |] ==> F:A leadsTo B";
by (ftac constrainsD2 1);
by (dres_inst_tac [("B", "A-B")] constrains_weaken_L 1);
by (dres_inst_tac [("B", "A-B")] transient_strengthen 2);
by (rtac (ensuresI RS leadsTo_Basis) 3);
by (ALLGOALS(Blast_tac));
qed "leadsTo_Basis'";

Goal "[| F:transient(A); st_set(B) |] ==> F: (A co A Un B) guarantees (A leadsTo (B-A))";
by (rtac guaranteesI 1);
by (blast_tac (claset() addDs [transient_type RS subsetD]) 2);
by (rtac leadsTo_Basis' 1);
by (Blast_tac 3);
by (dtac constrains_weaken_R 1);
by (assume_tac 2);
by (rtac Join_transient_I1 2);
by (REPEAT(Blast_tac 1));
qed "constrains_guarantees_leadsTo";


