(*  Title:      Confluence.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Confluence;

(* ------------------------------------------------------------------------- *)
(*        strip lemmas                                                       *)
(* ------------------------------------------------------------------------- *)

goalw Confluence.thy [confluence_def,strip_def] 
    "!!u.[|confluence(Spar_red1)|]==> strip";
by (resolve_tac [impI RS allI RS allI] 1);
by (etac Spar_red.induct 1);
by (Fast_tac  1);
by (fast_tac (!claset addIs [Spar_red.trans]) 1);
qed "strip_lemma_r";


goalw Confluence.thy [confluence_def,strip_def] 
    "!!u.strip==> confluence(Spar_red)";
by (resolve_tac [impI RS allI RS allI] 1);
by (etac Spar_red.induct 1);
by (Fast_tac  1);
by (Clarify_tac 1);
by (dres_inst_tac [("x1","z")] (spec RS mp) 1);
by (REPEAT(eresolve_tac [exE,conjE] 2));
by (dres_inst_tac [("x1","ua")] (spec RS mp) 2);
by (fast_tac (!claset addIs [Spar_red.trans]) 3);
by (TRYALL assume_tac );
qed "strip_lemma_l";

(* ------------------------------------------------------------------------- *)
(*      Confluence                                                           *)
(* ------------------------------------------------------------------------- *)


goalw Confluence.thy [confluence_def] "confluence(Spar_red1)";
by (Clarify_tac 1);
by (forward_tac [simulation] 1);
by (forw_inst_tac [("n","z")] simulation 1);
by (Clarify_tac 1);
by (forw_inst_tac [("v","va")] paving 1);
by (TRYALL assume_tac);
by (fast_tac (!claset addIs [completeness] addss (!simpset)) 1);
qed "parallel_moves";

bind_thm ("confluence_parallel_reduction",
	  parallel_moves RS strip_lemma_r RS strip_lemma_l);

goalw Confluence.thy [confluence_def] 
    "!!u.[|confluence(Spar_red)|]==> confluence(Sred)";
by(blast_tac (!claset addIs [par_red_red, red_par_red]) 1);
val lemma1 = result();

bind_thm ("confluence_beta_reduction",
	  confluence_parallel_reduction RS lemma1);

