(*  Title:      Conversion.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Conversion;

AddIs (Sconv.intrs @ Sconv1.intrs);

goal Conversion.thy  
    "!!u. m<--->n ==> n<--->m";
by (etac Sconv.induct 1);
by (etac Sconv1.induct 1);
by (ALLGOALS Blast_tac);
qed "conv_sym";

(* ------------------------------------------------------------------------- *)
(*      Church_Rosser Theorem                                                *)
(* ------------------------------------------------------------------------- *)

goal Conversion.thy  
    "!!u. m<--->n ==> EX p.(m --->p) & (n ---> p)";
by (etac Sconv.induct 1);
by (etac Sconv1.induct 1);
by (blast_tac (!claset addIs [red1D1,redD2]) 1);
by (blast_tac (!claset addIs [red1D1,redD2]) 1);
by (blast_tac (!claset addIs [red1D1,redD2]) 1);
by (cut_facts_tac [confluence_beta_reduction]  1);
by (rewtac confluence_def);
by (blast_tac (!claset addIs [Sred.trans]) 1);
qed "Church_Rosser";

