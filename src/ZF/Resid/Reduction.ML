(*  Title:      Reduction.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

(* ------------------------------------------------------------------------- *)
(*     Setting up rulelists for reduction                                    *)
(* ------------------------------------------------------------------------- *)

val red1D1     = Sred1.dom_subset RS subsetD RS SigmaD1;
val red1D2     = Sred1.dom_subset RS subsetD RS SigmaD2;
val redD1      = Sred.dom_subset RS subsetD RS SigmaD1;
val redD2      = Sred.dom_subset RS subsetD RS SigmaD2;
val par_red1D1 = Spar_red1.dom_subset RS subsetD RS SigmaD1;
val par_red1D2 = Spar_red1.dom_subset RS subsetD RS SigmaD2;
val par_redD1  = Spar_red.dom_subset RS subsetD RS SigmaD1;
val par_redD2  = Spar_red.dom_subset RS subsetD RS SigmaD2;


AddIs (Sred1.intrs@[Sred.one_step, Sred.refl]@Spar_red1.intrs@
       [Spar_red.one_step, lambda.dom_subset RS subsetD,
	unmark_type]@lambda.intrs@bool_typechecks);
AddSEs [Spar_red1.mk_cases "Fun(t) =1=> Fun(u)"];

Addsimps (Sred1.intrs@[Sred.one_step, Sred.refl]@Spar_red1.intrs@
	  [Spar_red.one_step, substL_type, redD1, redD2, par_redD1, 
	   par_redD2, par_red1D2, unmark_type]);


(* ------------------------------------------------------------------------- *)
(*     Lemmas for reduction                                                  *)
(* ------------------------------------------------------------------------- *)

Goal  "m--->n ==> Fun(m) ---> Fun(n)";
by (etac Sred.induct 1);
by (resolve_tac [Sred.trans] 3);
by (ALLGOALS (Asm_simp_tac ));
qed "red_Fun";

Goal "[|n \\<in> lambda; m ---> m'|]==> Apl(m,n)--->Apl(m',n)";
by (etac Sred.induct 1);
by (resolve_tac [Sred.trans] 3);
by (ALLGOALS (Asm_simp_tac ));
qed "red_Apll";

Goal "[|n \\<in> lambda; m ---> m'|]==> Apl(n,m)--->Apl(n,m')";
by (etac Sred.induct 1);
by (resolve_tac [Sred.trans] 3);
by (ALLGOALS (Asm_simp_tac ));
qed "red_Aplr";

Goal "[|m ---> m'; n--->n'|]==> Apl(m,n)--->Apl(m',n')";
by (res_inst_tac [("n","Apl(m',n)")] Sred.trans 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [red_Apll,red_Aplr]) ));
qed "red_Apl";

Goal "[|m \\<in> lambda; m':lambda; n \\<in> lambda; n':lambda; m ---> m'; n--->n'|]==> \
\              Apl(Fun(m),n)---> n'/m'";
by (res_inst_tac [("n","Apl(Fun(m'),n')")] Sred.trans 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [red_Apl,red_Fun]) ));
qed "red_beta";


(* ------------------------------------------------------------------------- *)
(*      Lemmas for parallel reduction                                        *)
(* ------------------------------------------------------------------------- *)


Goal "m \\<in> lambda==> m =1=> m";
by (etac lambda.induct 1);
by (ALLGOALS (Asm_simp_tac ));
qed "refl_par_red1";

Goal "m-1->n ==> m=1=>n";
by (etac Sred1.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [refl_par_red1]) ));
qed "red1_par_red1";

Goal "m--->n ==> m===>n";
by (etac Sred.induct 1);
by (resolve_tac [Spar_red.trans] 3);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [refl_par_red1,red1_par_red1]) ));
qed "red_par_red";

Goal "m===>n ==> m--->n";
by (etac Spar_red.induct 1);
by (etac Spar_red1.induct 1);
by (resolve_tac [Sred.trans] 5);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [red_Fun,red_beta,red_Apl]) ));
qed "par_red_red";


(* ------------------------------------------------------------------------- *)
(*      Simulation                                                           *)
(* ------------------------------------------------------------------------- *)

Goal "m=1=>n ==> \\<exists>v. m|>v = n & m~v & regular(v)";
by (etac Spar_red1.induct 1);
by Safe_tac;
by (ALLGOALS (REPEAT o (resolve_tac [exI,conjI])));
by (TRYALL(resolve_tac [res_redex,res_App,res_Fun,res_Var]));
by (ALLGOALS (asm_simp_tac (simpset())));
qed "simulation";


(* ------------------------------------------------------------------------- *)
(*           commuting of unmark and subst                                   *)
(* ------------------------------------------------------------------------- *)

Goal "u \\<in> redexes ==> \\<forall>k \\<in> nat. unmark(lift_rec(u,k)) = lift_rec(unmark(u),k)";
by (etac redexes.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lift_rec_Var])));
qed "unmmark_lift_rec";

Goal "v \\<in> redexes ==> \\<forall>k \\<in> nat. \\<forall>u \\<in> redexes.  \
\         unmark(subst_rec(u,v,k)) = subst_rec(unmark(u),unmark(v),k)";
by (etac redexes.induct 1);
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps [unmmark_lift_rec, subst_Var])));
qed "unmmark_subst_rec";


(* ------------------------------------------------------------------------- *)
(*        Completeness                                                       *)
(* ------------------------------------------------------------------------- *)

Goal "u~v ==> regular(v) --> unmark(u) =1=> unmark(u|>v)";
by (etac Scomp.induct 1);
by (auto_tac (claset(),
	      simpset() addsimps [unmmark_subst_rec]));
by (dres_inst_tac [("psi", "Fun(?u) =1=> ?w")] asm_rl 1);
by Auto_tac;
qed_spec_mp "completeness_l";

Goal "[|u \\<in> lambda; u~v; regular(v)|]==> u =1=> unmark(u|>v)";
by (dtac completeness_l 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [lambda_unmark]) ));
qed "completeness";

