(*  Title:      Reduction.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Reduction;


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


val reduc_cs = res_cs 
           addIs (Sred1.intrs@[Sred.one_step,Sred.refl]@Spar_red1.intrs@
                  [Spar_red.one_step,lambda.dom_subset RS subsetD,
                   unmark_type]@lambda.intrs@bool_typechecks)
           addSEs [Spar_red1.mk_cases redexes.con_defs "Fun(t) =1=> Fun(u)"];

val reduc_ss = term_ss addsimps
                   (Sred1.intrs@[Sred.one_step,Sred.refl]@Spar_red1.intrs@
                    [Spar_red.one_step,substL_type,redD1,redD2,par_redD1,
                     par_redD2,par_red1D2,unmark_type]);

val reducL_ss = reduc_ss setloop (SELECT_GOAL (safe_tac reduc_cs));

(* ------------------------------------------------------------------------- *)
(*     Lemmas for reduction                                                  *)
(* ------------------------------------------------------------------------- *)

goal Reduction.thy  "!!u. m--->n ==> Fun(m) ---> Fun(n)";
by (etac Sred.induct 1);
by (resolve_tac [Sred.trans] 3);
by (ALLGOALS (asm_simp_tac reduc_ss ));
val red_Fun = result();

goal Reduction.thy  
    "!!u.[|n:lambda; m ---> m'|]==> Apl(m,n)--->Apl(m',n)";
by (etac Sred.induct 1);
by (resolve_tac [Sred.trans] 3);
by (ALLGOALS (asm_simp_tac reduc_ss ));
val red_Apll = result();

goal Reduction.thy  
    "!!u.[|n:lambda; m ---> m'|]==> Apl(n,m)--->Apl(n,m')";
by (etac Sred.induct 1);
by (resolve_tac [Sred.trans] 3);
by (ALLGOALS (asm_simp_tac reduc_ss ));
val red_Aplr = result();

goal Reduction.thy  
    "!!u.[|m ---> m'; n--->n'|]==> Apl(m,n)--->Apl(m',n')";
by (res_inst_tac [("n","Apl(m',n)")] Sred.trans 1);
by (ALLGOALS (asm_simp_tac (reduc_ss addsimps [red_Apll,red_Aplr]) ));
val red_Apl = result();

goal Reduction.thy  
    "!!u.[|m:lambda; m':lambda; n:lambda; n':lambda; m ---> m'; n--->n'|]==> \
\              Apl(Fun(m),n)---> n'/m'";
by (res_inst_tac [("n","Apl(Fun(m'),n')")] Sred.trans 1);
by (ALLGOALS (asm_simp_tac (reduc_ss addsimps [red_Apl,red_Fun]) ));
val red_beta = result();


(* ------------------------------------------------------------------------- *)
(*      Lemmas for parallel reduction                                        *)
(* ------------------------------------------------------------------------- *)


goal Reduction.thy "!!u.m:lambda==> m =1=> m";
by (eresolve_tac [lambda.induct] 1);
by (ALLGOALS (asm_simp_tac reduc_ss ));
val refl_par_red1 = result();

goal Reduction.thy "!!u.m-1->n ==> m=1=>n";
by (etac Sred1.induct 1);
by (ALLGOALS (asm_simp_tac (reduc_ss addsimps [refl_par_red1]) ));
val red1_par_red1 = result();

goal Reduction.thy "!!u.m--->n ==> m===>n";
by (etac Sred.induct 1);
by (resolve_tac [Spar_red.trans] 3);
by (ALLGOALS (asm_simp_tac (reduc_ss addsimps [refl_par_red1,red1_par_red1]) ));
val red_par_red = result();

goal Reduction.thy "!!u.m===>n ==> m--->n";
by (etac Spar_red.induct 1);
by (etac Spar_red1.induct 1);
by (resolve_tac [Sred.trans] 5);
by (ALLGOALS (asm_simp_tac (reduc_ss addsimps [red_Fun,red_beta,red_Apl]) ));
val par_red_red = result();


(* ------------------------------------------------------------------------- *)
(*      Simulation                                                           *)
(* ------------------------------------------------------------------------- *)

goal Reduction.thy  
    "!!u.m=1=>n ==> EX v. m|>v = n & m~v & regular(v)";
by (etac Spar_red1.induct 1);
by (step_tac ZF_cs 1);
by (ALLGOALS (REPEAT o (resolve_tac [exI,conjI])));
by (TRYALL(resolve_tac [res_redex,res_App,res_Fun,res_Var]));
by (ALLGOALS (asm_simp_tac (reduc_ss)));
val simulation = result();


(* ------------------------------------------------------------------------- *)
(*           commuting of unmark and subst                                   *)
(* ------------------------------------------------------------------------- *)

goal Reduction.thy  
    "!!u.u:redexes ==> \
\           ALL k:nat. unmark(lift_rec(u,k)) = lift_rec(unmark(u),k)";
by (eresolve_tac [redexes.induct] 1);
by (ALLGOALS (asm_full_simp_tac (addsplit reduc_ss)));
val unmmark_lift_rec = result();

goal Reduction.thy  
    "!!u.v:redexes ==> ALL k:nat.ALL u:redexes.  \
\         unmark(subst_rec(u,v,k)) = subst_rec(unmark(u),unmark(v),k)";
by (eresolve_tac [redexes.induct] 1);
by (ALLGOALS (asm_full_simp_tac 
             ((addsplit reduc_ss) addsimps [unmmark_lift_rec])));
val unmmark_subst_rec = result();


(* ------------------------------------------------------------------------- *)
(*        Completeness                                                       *)
(* ------------------------------------------------------------------------- *)

goal Reduction.thy  
    "!!u.u~v ==> regular(v) --> unmark(u) =1=> unmark(u|>v)";
by (etac Scomp.induct 1);
by (ALLGOALS (asm_full_simp_tac (reducL_ss addsimps [unmmark_subst_rec]) ));
by (dres_inst_tac [("psi", "Fun(?u) =1=> ?w")] asm_rl 1);
by (asm_full_simp_tac reducL_ss 1);
val completeness_l = result();

goal Reduction.thy  
    "!!u.[|u:lambda; u~v; regular(v)|]==> u =1=> unmark(u|>v)";
by (dres_inst_tac [("u1","u")] (completeness_l RS mp) 1);
by (ALLGOALS (asm_full_simp_tac (reduc_ss addsimps [lambda_unmark]) ));
val completeness = result();
