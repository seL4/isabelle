(*  Title:      Redex.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Addsimps redexes.intrs;

fun rotate n i = EVERY(replicate n (etac revcut_rl i));    
(* ------------------------------------------------------------------------- *)
(*    Specialisation of comp-rules                                           *)
(* ------------------------------------------------------------------------- *)

val compD1 = Scomp.dom_subset RS subsetD RS SigmaD1;
val compD2 = Scomp.dom_subset RS subsetD RS SigmaD2;

val regD = Sreg.dom_subset RS subsetD;

(* ------------------------------------------------------------------------- *)
(*    Equality rules for union                                               *)
(* ------------------------------------------------------------------------- *)

Goal "n:nat==>Var(n) un Var(n)=Var(n)";
by (asm_simp_tac (simpset() addsimps [union_def]) 1);
qed "union_Var";

Goal "[|u:redexes; v:redexes|]==>Fun(u) un Fun(v)=Fun(u un v)";
by (asm_simp_tac (simpset() addsimps [union_def]) 1);
qed "union_Fun";
 
Goal "[|b1:bool; b2:bool; u1:redexes; v1:redexes; u2:redexes; v2:redexes|]==> \
\     App(b1,u1,v1) un App(b2,u2,v2)=App(b1 or b2,u1 un u2,v1 un v2)";
by (asm_simp_tac (simpset() addsimps [union_def]) 1);
qed "union_App";

Addsimps (Ssub.intrs@bool_typechecks@
	  Sreg.intrs@Scomp.intrs@
	  [or_1 RSN (3,or_commute RS trans),
	   or_0 RSN (3,or_commute RS trans),
	   union_App,union_Fun,union_Var,compD2,compD1,regD]);

AddIs Scomp.intrs;
AddSEs [Sreg.mk_cases "regular(App(b,f,a))",
	Sreg.mk_cases "regular(Fun(b))",
	Sreg.mk_cases "regular(Var(b))",
	Scomp.mk_cases "Fun(u) ~ Fun(t)",
	Scomp.mk_cases "u ~ Fun(t)",
	Scomp.mk_cases "u ~ Var(n)",
	Scomp.mk_cases "u ~ App(b,t,a)",
	Scomp.mk_cases "Fun(t) ~ v",
	Scomp.mk_cases "App(b,f,a) ~ v",
	Scomp.mk_cases "Var(n) ~ u"];



(* ------------------------------------------------------------------------- *)
(*    comp proofs                                                            *)
(* ------------------------------------------------------------------------- *)

Goal "u:redexes ==> u ~ u";
by (etac redexes.induct 1);
by (ALLGOALS Fast_tac);
qed "comp_refl";

Goal "u ~ v ==> v ~ u";
by (etac Scomp.induct 1);
by (ALLGOALS Fast_tac);
qed "comp_sym";

Goal "u ~ v <-> v ~ u";
by (fast_tac (claset() addIs [comp_sym]) 1);
qed "comp_sym_iff";


Goal "u ~ v ==> ALL w. v ~ w-->u ~ w";
by (etac Scomp.induct 1);
by (ALLGOALS Fast_tac);
qed_spec_mp "comp_trans";

(* ------------------------------------------------------------------------- *)
(*   union proofs                                                            *)
(* ------------------------------------------------------------------------- *)

Goal "u ~ v ==> u <== (u un v)";
by (etac Scomp.induct 1);
by (etac boolE 3);
by (ALLGOALS Asm_simp_tac);
qed "union_l";

Goal "u ~ v ==> v <== (u un v)";
by (etac Scomp.induct 1);
by (eres_inst_tac [("c","b2")] boolE 3);
by (ALLGOALS Asm_simp_tac);
qed "union_r";

Goal "u ~ v ==> u un v = v un u";
by (etac Scomp.induct 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [or_commute])));
qed "union_sym";

(* ------------------------------------------------------------------------- *)
(*      regular proofs                                                       *)
(* ------------------------------------------------------------------------- *)

Goal "u ~ v ==> regular(u)-->regular(v)-->regular(u un v)";
by (etac Scomp.induct 1);
by Auto_tac;
by (dres_inst_tac [("psi", "regular(Fun(?u) un ?v)")] asm_rl 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "union_preserve_regular";
