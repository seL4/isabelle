(*  Title: 	HOLCF/cprod2.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for cprod2.thy 
*)

open Cprod2;

qed_goal "less_cprod3a" Cprod2.thy 
	"p1=<UU,UU> ==> p1 << p2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (inst_cprod_po RS ssubst) 1),
	(rtac (less_cprod1b RS ssubst) 1),
	(hyp_subst_tac 1),
	(asm_simp_tac prod_ss  1),
	(rtac conjI 1),
	(rtac minimal 1),
	(rtac minimal 1)
	]);

qed_goal "less_cprod3b" Cprod2.thy
 "(p1 << p2) = (fst(p1)<<fst(p2) & snd(p1)<<snd(p2))"
 (fn prems =>
	[
	(rtac (inst_cprod_po RS ssubst) 1),
	(rtac less_cprod1b 1)
	]);

qed_goal "less_cprod4a" Cprod2.thy 
	"<x1,x2> << <UU,UU> ==> x1=UU & x2=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac less_cprod2a 1),
	(etac (inst_cprod_po RS subst) 1)
	]);

qed_goal "less_cprod4b" Cprod2.thy 
	"p << <UU,UU> ==> p = <UU,UU>"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac less_cprod2b 1),
	(etac (inst_cprod_po RS subst) 1)
	]);

qed_goal "less_cprod4c" Cprod2.thy
 " <xa,ya> << <x,y> ==> xa<<x & ya << y"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac less_cprod2c 1),
	(etac (inst_cprod_po RS subst) 1),
	(REPEAT (atac 1))
	]);

(* ------------------------------------------------------------------------ *)
(* type cprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_cprod" Cprod2.thy  "<UU,UU><<p"
(fn prems =>
	[
	(rtac less_cprod3a 1),
	(rtac refl 1)
	]);

(* ------------------------------------------------------------------------ *)
(* Pair <_,_>  is monotone in both arguments                                *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_pair1" Cprod2.thy [monofun] "monofun(Pair)"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac (less_fun RS iffD2) 1),
	(strip_tac 1),
	(rtac (less_cprod3b RS iffD2) 1),
	(simp_tac prod_ss 1),
	(asm_simp_tac Cfun_ss 1)
	]);

qed_goalw "monofun_pair2" Cprod2.thy [monofun] "monofun(Pair(x))"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac (less_cprod3b RS iffD2) 1),
	(simp_tac prod_ss 1),
	(asm_simp_tac Cfun_ss 1)
	]);

qed_goal "monofun_pair" Cprod2.thy 
 "[|x1<<x2; y1<<y2|] ==> <x1,y1> << <x2,y2>"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac trans_less 1),
	(rtac (monofun_pair1 RS monofunE RS spec RS spec RS mp RS 
	(less_fun RS iffD1 RS spec)) 1),
	(rtac (monofun_pair2 RS monofunE RS spec RS spec RS mp) 2),
	(atac 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* fst and snd are monotone                                                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_fst" Cprod2.thy [monofun] "monofun(fst)"
 (fn prems =>
	[
	(strip_tac 1),
	(res_inst_tac [("p","x")] PairE 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","y")] PairE 1),
	(hyp_subst_tac 1),
	(asm_simp_tac prod_ss  1),
	(etac (less_cprod4c RS conjunct1) 1)
	]);

qed_goalw "monofun_snd" Cprod2.thy [monofun] "monofun(snd)"
 (fn prems =>
	[
	(strip_tac 1),
	(res_inst_tac [("p","x")] PairE 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","y")] PairE 1),
	(hyp_subst_tac 1),
	(asm_simp_tac prod_ss  1),
	(etac (less_cprod4c RS conjunct2) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* the type 'a * 'b is a cpo                                                *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_cprod" Cprod2.thy 
" is_chain(S) ==> range(S) <<| \
\   < lub(range(%i.fst(S(i)))),lub(range(%i.snd(S(i))))> "
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_lubI 1),
	(rtac conjI 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(res_inst_tac [("t","S(i)")] (surjective_pairing RS ssubst) 1),
	(rtac monofun_pair 1),
	(rtac is_ub_thelub 1),
	(etac (monofun_fst RS ch2ch_monofun) 1),
	(rtac is_ub_thelub 1),
	(etac (monofun_snd RS ch2ch_monofun) 1),
	(strip_tac 1),
	(res_inst_tac [("t","u")] (surjective_pairing RS ssubst) 1),
	(rtac monofun_pair 1),
	(rtac is_lub_thelub 1),
	(etac (monofun_fst RS ch2ch_monofun) 1),
	(etac (monofun_fst RS ub2ub_monofun) 1),
	(rtac is_lub_thelub 1),
	(etac (monofun_snd RS ch2ch_monofun) 1),
	(etac (monofun_snd RS ub2ub_monofun) 1)
	]);

val thelub_cprod = (lub_cprod RS thelubI);
(* "is_chain(?S1) ==> lub(range(?S1)) =                                *)
(*  <lub(range(%i. fst(?S1(i)))), lub(range(%i. snd(?S1(i))))>"        *)


qed_goal "cpo_cprod" Cprod2.thy 
	"is_chain(S::nat=>'a*'b)==>? x.range(S)<<| x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac exI 1),
	(etac lub_cprod 1)
	]);

