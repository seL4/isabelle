(*  Title:      Confluence.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Confluence;

(* ------------------------------------------------------------------------- *)
(*        Confluence                                                         *)
(* ------------------------------------------------------------------------- *)

goalw Confluence.thy [confluence_def] 
    "!!u.[|confluence(Spar_red)|]==> confluence(Sred)";
by (step_tac ZF_cs 1);
by (dres_inst_tac [("x4","x"),("x3","y"),("x1","z")] 
    (spec RS spec RS mp RS spec RS mp) 1);
by (ALLGOALS(asm_simp_tac (reduc_ss addsimps [red_par_red])));
by (fast_tac (reduc_cs addIs [par_red_red])  1);
val lemma1 = result();

(* ------------------------------------------------------------------------- *)
(*        strip lemmas                                                       *)
(* ------------------------------------------------------------------------- *)

goalw Confluence.thy [confluence_def,strip_def] 
    "!!u.[|confluence(Spar_red1)|]==> strip";
by (resolve_tac [impI RS allI RS allI] 1);
by (etac Spar_red.induct 1);
by (fast_tac reduc_cs  1);
by (fast_tac (ZF_cs addIs [Spar_red.trans]) 1);
val strip_lemma_r = result();


goalw Confluence.thy [confluence_def,strip_def] 
    "!!u.strip==> confluence(Spar_red)";
by (resolve_tac [impI RS allI RS allI] 1);
by (etac Spar_red.induct 1);
by (fast_tac reduc_cs  1);
by (step_tac ZF_cs 1);
by (dres_inst_tac [("x1","z")] (spec RS mp) 1);
by (REPEAT(eresolve_tac [exE,conjE] 2));
by (dres_inst_tac [("x1","ua")] (spec RS mp) 2);
by (fast_tac (ZF_cs addIs [Spar_red.trans]) 3);
by (TRYALL assume_tac );
val strip_lemma_l = result();

(* ------------------------------------------------------------------------- *)
(*      Confluence                                                           *)
(* ------------------------------------------------------------------------- *)


goal Confluence.thy  
    "!!u.confluence(Spar_red1)==> confluence(Spar_red)";
by (resolve_tac [strip_lemma_r RS strip_lemma_l] 1);
by (assume_tac 1);
val lemma2 = result();


goalw Confluence.thy [confluence_def] "confluence(Spar_red1)";
by (step_tac ZF_cs 1);
by (forward_tac [simulation] 1);
by (forw_inst_tac [("n","z")] simulation 1);
by (step_tac ZF_cs 1);
by (forw_inst_tac [("v","va")] paving 1);
by (TRYALL assume_tac);
by (REPEAT(step_tac ZF_cs 1));
by (res_inst_tac [("v","vu")] completeness 1);
by (ALLGOALS(asm_simp_tac (reduc_ss addsimps [completeness])));
val parallel_moves = result();

goal Confluence.thy  "confluence(Spar_red)";
by (resolve_tac [parallel_moves RS lemma2] 1);
val confluence_parallel_reduction = result();

goal Confluence.thy  "confluence(Sred)";
by (resolve_tac [confluence_parallel_reduction RS lemma1] 1);
val confluence_beta_reduction = result();
