(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition

From Chandy and Sanders, "Reasoning About Program Composition"
*)

Addsimps [Join_SKIP, Join_absorb];

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

Delsimps [split_paired_All];


(*** component ***)

Goalw [component_def] "component F F";
by (blast_tac (claset() addIs [Join_SKIP]) 1);
qed "component_refl";

AddIffs [component_refl];

Goalw [component_def] "[| component F G; component G H |] ==> component F H";
by (blast_tac (claset() addIs [Join_assoc RS sym]) 1);
qed "component_trans";

Goalw [component_def,Join_def] "component F G ==> Acts F <= Acts G";
auto();
qed "componet_Acts";

Goalw [component_def,Join_def] "component F G ==> Init G <= Init F";
auto();
qed "componet_Init";

Goal "[| component F G; component G F |] ==> F=G";
by (asm_simp_tac (simpset() addsimps [program_equalityI, equalityI, 
				      componet_Acts, componet_Init]) 1);
qed "component_anti_sym";


(*** existential properties ***)

Goalw [ex_prop_def]
     "[| ex_prop X; finite GG |] ==> GG Int X ~= {} --> (JN G:GG. G) : X";
by (etac finite_induct 1);
by (auto_tac (claset(), simpset() addsimps [Int_insert_left]));
qed_spec_mp "ex1";

Goalw [ex_prop_def]
     "ALL GG. finite GG & GG Int X ~= {} --> (JN G:GG. G) : X  \
\      ==> ex_prop X";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{F,G}")] spec 1);
auto();
qed "ex2";

(*Chandy & Sanders take this as a definition*)
Goal "ex_prop X = (ALL GG. finite GG & GG Int X ~= {} --> (JN G:GG. G) : X)";
by (blast_tac (claset() addIs [ex1,ex2]) 1);
qed "ex_prop_finite";

(*Their "equivalent definition" given at the end of section 3*)
Goal "ex_prop X = (ALL G. G:X = (ALL H. component G H --> H: X))";
auto();
bws [ex_prop_def, component_def];
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
br conjI 1;
by (Clarify_tac 2);
by (dres_inst_tac [("x", "{F,G}")] spec 2);
by (dres_inst_tac [("x", "{}")] spec 1);
auto();
qed "uv2";

(*Chandy & Sanders take this as a definition*)
Goal "uv_prop X = (ALL GG. finite GG & GG <= X --> (JN G:GG. G) : X)";
by (blast_tac (claset() addIs [uv1,uv2]) 1);
qed "uv_prop_finite";


(*** guarantees ***)

Goalw [guarantees_def] "X <= Y ==> X guarantees Y = UNIV";
by (Blast_tac 1);
qed "subset_imp_guarantees";

Goalw [guarantees_def] "ex_prop Y = (Y = UNIV guarantees Y)";
ex_prop_equiv
by (Blast_tac 1);
qed "subset_imp_guarantees";
