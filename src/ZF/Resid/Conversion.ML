(*  Title:      Conversion.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Conversion;

val (!simpset) = (!simpset) addsimps (Sconv1.intrs@[Sconv.one_step,Sconv.refl]);

goal Conversion.thy  
    "!!u.m<--->n ==> n<--->m";
by (etac Sconv.induct 1);
by (etac Sconv1.induct 1);
by (resolve_tac [Sconv.trans] 4);
by (ALLGOALS(asm_simp_tac (!simpset) ));
val conv_sym = result();

(* ------------------------------------------------------------------------- *)
(*      Church_Rosser Theorem                                                *)
(* ------------------------------------------------------------------------- *)

goal Conversion.thy  
    "!!u.m<--->n ==> EX p.(m --->p) & (n ---> p)";
by (etac Sconv.induct 1);
by (etac Sconv1.induct 1);
by (fast_tac (!claset addIs [red1D1,redD2]) 1);
by (fast_tac (!claset addIs [red1D1,redD2]) 1);
by (fast_tac (!claset addIs [red1D1,redD2]) 1);
by (cut_facts_tac [confluence_beta_reduction]  1);
by (rewtac confluence_def);
by (step_tac (!claset) 1);
by (dres_inst_tac [("x4","n"),("x3","pa"),("x1","pb")] 
    (spec RS spec RS mp RS spec RS mp) 1);
by (TRYALL assume_tac);
by (step_tac (!claset) 1);
by (step_tac (!claset) 1);
by (step_tac (!claset) 1);
by (res_inst_tac [("n","pa")]Sred.trans 1);
by (res_inst_tac [("n","pb"),("p","ua")] Sred.trans 3);
by (TRYALL assume_tac);
val Church_Rosser = result();

