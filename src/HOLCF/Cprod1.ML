(*  Title: 	HOLCF/cprod1.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for theory cprod1.thy 
*)

open Cprod1;

qed_goalw "less_cprod1b" Cprod1.thy [less_cprod_def]
 "less_cprod(p1,p2) = ( fst(p1) << fst(p2) & snd(p1) << snd(p2))"
 (fn prems =>
	[
	(rtac refl 1)
	]);

qed_goalw "less_cprod2a" Cprod1.thy [less_cprod_def]
 "less_cprod(<x,y>,<UU,UU>) ==> x = UU & y = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac conjE 1),
	(dtac (fst_conv RS subst) 1),
	(dtac (fst_conv RS subst) 1),
	(dtac (fst_conv RS subst) 1),
	(dtac (snd_conv RS subst) 1),
	(dtac (snd_conv RS subst) 1),
	(dtac (snd_conv RS subst) 1),
	(rtac conjI 1),
	(etac UU_I 1),
	(etac UU_I 1)
	]);

qed_goal "less_cprod2b" Cprod1.thy 
 "less_cprod(p,<UU,UU>) ==> p=<UU,UU>"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","p")] PairE 1),
	(hyp_subst_tac 1),
	(dtac less_cprod2a 1),
	(asm_simp_tac HOL_ss 1)
	]);

qed_goalw "less_cprod2c" Cprod1.thy [less_cprod_def]
 "less_cprod(<x1,y1>,<x2,y2>) ==> x1 << x2 & y1 << y2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac conjE 1),
	(dtac (fst_conv RS subst) 1),
	(dtac (fst_conv RS subst) 1),
	(dtac (fst_conv RS subst) 1),
	(dtac (snd_conv RS subst) 1),
	(dtac (snd_conv RS subst) 1),
	(dtac (snd_conv RS subst) 1),
	(rtac conjI 1),
	(atac 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* less_cprod is a partial order on 'a * 'b                                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "refl_less_cprod" Cprod1.thy [less_cprod_def] "less_cprod(p,p)"
 (fn prems =>
	[
	(res_inst_tac [("p","p")] PairE 1),
	(hyp_subst_tac 1),
	(simp_tac prod_ss 1),
	(simp_tac Cfun_ss 1)
	]);

qed_goal "antisym_less_cprod" Cprod1.thy 
 "[|less_cprod(p1,p2);less_cprod(p2,p1)|] ==> p1=p2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","p1")] PairE 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p2")] PairE 1),
	(hyp_subst_tac 1),
	(dtac less_cprod2c 1),
	(dtac less_cprod2c 1),
	(etac conjE 1),
	(etac conjE 1),
	(rtac (Pair_eq RS ssubst) 1),
	(fast_tac (HOL_cs addSIs [antisym_less]) 1)
	]);


qed_goal "trans_less_cprod" Cprod1.thy 
 "[|less_cprod(p1,p2);less_cprod(p2,p3)|] ==> less_cprod(p1,p3)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","p1")] PairE 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p3")] PairE 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p2")] PairE 1),
	(hyp_subst_tac 1),
	(dtac less_cprod2c 1),
	(dtac less_cprod2c 1),
	(rtac (less_cprod1b RS ssubst) 1),
	(simp_tac prod_ss 1),
	(etac conjE 1),
	(etac conjE 1),
	(rtac conjI 1),
	(etac trans_less 1),
	(atac 1),
	(etac trans_less 1),
	(atac 1)
	]);

