(*  Title:      SubUnion.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open SubUnion;

fun rotate n i = EVERY(replicate n (etac revcut_rl i));    
(* ------------------------------------------------------------------------- *)
(*    Specialisation of comp-rules                                           *)
(* ------------------------------------------------------------------------- *)

val comp_induct = standard
    (Scomp.mutual_induct RS spec RS spec RSN (2,rev_mp));

val compD1 =Scomp.dom_subset RS subsetD RS SigmaD1;
val compD2 =Scomp.dom_subset RS subsetD RS SigmaD2;

val regD =Sreg.dom_subset RS subsetD;

(* ------------------------------------------------------------------------- *)
(*    Equality rules for union                                               *)
(* ------------------------------------------------------------------------- *)

goalw SubUnion.thy [union_def]
    "!!u.n:nat==>Var(n) un Var(n)=Var(n)";
by (asm_simp_tac redexes_ss 1);
by (simp_tac (rank_ss addsimps redexes.con_defs)  1);
val union_Var = result();

goalw SubUnion.thy [union_def]
    "!!u.[|u:redexes; v:redexes|]==>Fun(u) un Fun(v)=Fun(u un v)";
by (asm_simp_tac redexes_ss 1);
by (simp_tac (rank_ss addsimps redexes.con_defs)  1);
val union_Fun = result();
 
goalw SubUnion.thy [union_def]
 "!!u.[|b1:bool; b2:bool; u1:redexes; v1:redexes; u2:redexes; v2:redexes|]==> \
\     App(b1,u1,v1) un App(b2,u2,v2)=App(b1 or b2,u1 un u2,v1 un v2)";
by (asm_simp_tac redexes_ss 1);
by (simp_tac (rank_ss addsimps redexes.con_defs)  1);
val union_App = result();

val union_ss = redexes_ss addsimps 
                (Ssub.intrs@bool_simps@bool_typechecks@
                 Sreg.intrs@Scomp.intrs@
                 [or_1 RSN (3,or_commute RS trans),
                  or_0 RSN (3,or_commute RS trans),
                  union_App,union_Fun,union_Var,compD2,compD1,regD]);

val union_cs = (ZF_cs addIs Scomp.intrs addSEs 
                [Sreg.mk_cases redexes.con_defs "regular(App(b,f,a))",
                 Sreg.mk_cases redexes.con_defs "regular(Fun(b))",
                 Sreg.mk_cases redexes.con_defs "regular(Var(b))",
                 Scomp.mk_cases redexes.con_defs "Fun(u) ~ Fun(t)",
                 Scomp.mk_cases redexes.con_defs "u ~ Fun(t)",
                 Scomp.mk_cases redexes.con_defs "u ~ Var(n)",
                 Scomp.mk_cases redexes.con_defs "u ~ App(b,t,a)",
                 Scomp.mk_cases redexes.con_defs "Fun(t) ~ v",
                 Scomp.mk_cases redexes.con_defs "App(b,f,a) ~ v",
                 Scomp.mk_cases redexes.con_defs "Var(n) ~ u"
                 ]);



(* ------------------------------------------------------------------------- *)
(*    comp proofs                                                            *)
(* ------------------------------------------------------------------------- *)

goal SubUnion.thy "!!u.u:redexes ==> u ~ u";
by (eresolve_tac [redexes.induct] 1);
by (ALLGOALS(fast_tac union_cs));
val comp_refl = result();

goal SubUnion.thy 
    "!!u.u ~ v ==> v ~ u";
by (etac comp_induct 1);
by (ALLGOALS(fast_tac union_cs));
val comp_sym = result();

goal SubUnion.thy 
    "u ~ v <-> v ~ u";
by (fast_tac (ZF_cs addIs [comp_sym]) 1);
val comp_sym_iff = result();


goal SubUnion.thy 
    "!!u.u ~ v ==> ALL w.v ~ w-->u ~ w";
by (etac comp_induct 1);
by (ALLGOALS(fast_tac union_cs));
val comp_trans1 = result();

val comp_trans = comp_trans1 RS spec RS mp;

(* ------------------------------------------------------------------------- *)
(*   union proofs                                                            *)
(* ------------------------------------------------------------------------- *)

val sub_induct = standard
    (Ssub.mutual_induct RS spec RS spec RSN (2,rev_mp));

goal SubUnion.thy 
    "!!u.u ~ v ==> u <== (u un v)";
by (etac comp_induct 1);
by (etac boolE 3);
by (ALLGOALS(asm_full_simp_tac union_ss));
val union_l = result();

goal SubUnion.thy 
    "!!u.u ~ v ==> v <== (u un v)";
by (etac comp_induct 1);
by (eres_inst_tac [("c","b2")] boolE 3);
by (ALLGOALS(asm_full_simp_tac union_ss));
val union_r = result();

goal SubUnion.thy 
    "!!u.u ~ v ==> u un v = v un u";
by (etac comp_induct 1);
by (ALLGOALS(asm_simp_tac (union_ss addsimps [or_commute])));
val union_sym = result();

(* ------------------------------------------------------------------------- *)
(*      regular proofs                                                       *)
(* ------------------------------------------------------------------------- *)

goal SubUnion.thy 
    "!!u.u ~ v ==> regular(u)-->regular(v)-->regular(u un v)";
by (etac comp_induct 1);
by (ALLGOALS(asm_full_simp_tac
             (union_ss setloop(SELECT_GOAL (safe_tac union_cs)))));
by (dres_inst_tac [("psi", "regular(Fun(?u) un ?v)")] asm_rl 1);
by (asm_full_simp_tac union_ss 1);
val union_preserve_regular = result();
