(*  Title: 	HOLCF/cprod3.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for Cprod3.thy 
*)

open Cprod3;

(* ------------------------------------------------------------------------ *)
(* continuity of (_,_) , fst, snd                                           *)
(* ------------------------------------------------------------------------ *)

qed_goal "Cprod3_lemma1" Cprod3.thy 
"is_chain(Y::(nat=>'a)) ==>\
\ (lub(range(Y)),(x::'b)) =\
\ (lub(range(%i. fst(Y i,x))),lub(range(%i. snd(Y i,x))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("f1","Pair")] (arg_cong RS cong) 1),
	(rtac lub_equal 1),
	(atac 1),
	(rtac (monofun_fst RS ch2ch_monofun) 1),
	(rtac ch2ch_fun 1),
	(rtac (monofun_pair1 RS ch2ch_monofun) 1),
	(atac 1),
	(rtac allI 1),
	(simp_tac prod_ss 1),
	(rtac sym 1),
	(simp_tac prod_ss 1),
	(rtac (lub_const RS thelubI) 1)
	]);

qed_goal "contlub_pair1" Cprod3.thy "contlub(Pair)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (expand_fun_eq RS iffD2) 1),
	(strip_tac 1),
	(rtac (lub_fun RS thelubI RS ssubst) 1),
	(etac (monofun_pair1 RS ch2ch_monofun) 1),
	(rtac trans 1),
	(rtac (thelub_cprod RS sym) 2),
	(rtac ch2ch_fun 2),
	(etac (monofun_pair1 RS ch2ch_monofun) 2),
	(etac Cprod3_lemma1 1)
	]);

qed_goal "Cprod3_lemma2" Cprod3.thy 
"is_chain(Y::(nat=>'a)) ==>\
\ ((x::'b),lub(range Y)) =\
\ (lub(range(%i. fst(x,Y i))),lub(range(%i. snd(x, Y i))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("f1","Pair")] (arg_cong RS cong) 1),
	(rtac sym 1),
	(simp_tac prod_ss 1),
	(rtac (lub_const RS thelubI) 1),
	(rtac lub_equal 1),
	(atac 1),
	(rtac (monofun_snd RS ch2ch_monofun) 1),
	(rtac (monofun_pair2 RS ch2ch_monofun) 1),
	(atac 1),
	(rtac allI 1),
	(simp_tac prod_ss 1)
	]);

qed_goal "contlub_pair2" Cprod3.thy "contlub(Pair(x))"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_cprod RS sym) 2),
	(etac (monofun_pair2 RS ch2ch_monofun) 2),
	(etac Cprod3_lemma2 1)
	]);

qed_goal "cont_pair1" Cprod3.thy "cont(Pair)"
(fn prems =>
	[
	(rtac monocontlub2cont 1),
	(rtac monofun_pair1 1),
	(rtac contlub_pair1 1)
	]);

qed_goal "cont_pair2" Cprod3.thy "cont(Pair(x))"
(fn prems =>
	[
	(rtac monocontlub2cont 1),
	(rtac monofun_pair2 1),
	(rtac contlub_pair2 1)
	]);

qed_goal "contlub_fst" Cprod3.thy "contlub(fst)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (lub_cprod RS thelubI RS ssubst) 1),
	(atac 1),
	(simp_tac prod_ss 1)
	]);

qed_goal "contlub_snd" Cprod3.thy "contlub(snd)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (lub_cprod RS thelubI RS ssubst) 1),
	(atac 1),
	(simp_tac prod_ss 1)
	]);

qed_goal "cont_fst" Cprod3.thy "cont(fst)"
(fn prems =>
	[
	(rtac monocontlub2cont 1),
	(rtac monofun_fst 1),
	(rtac contlub_fst 1)
	]);

qed_goal "cont_snd" Cprod3.thy "cont(snd)"
(fn prems =>
	[
	(rtac monocontlub2cont 1),
	(rtac monofun_snd 1),
	(rtac contlub_snd 1)
	]);

(* 
 -------------------------------------------------------------------------- 
 more lemmas for Cprod3.thy 
 
 -------------------------------------------------------------------------- 
*)

(* ------------------------------------------------------------------------ *)
(* convert all lemmas to the continuous versions                            *)
(* ------------------------------------------------------------------------ *)

qed_goalw "beta_cfun_cprod" Cprod3.thy [cpair_def]
	"(LAM x y.(x,y))`a`b = (a,b)"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(cont_tac 1),
	(rtac cont_pair2 1),
	(rtac cont2cont_CF1L 1),
	(rtac cont_pair1 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_pair2 1),
	(rtac refl 1)
	]);

qed_goalw "inject_cpair" Cprod3.thy [cpair_def]
	" <a,b>=<aa,ba>  ==> a=aa & b=ba"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(dtac (beta_cfun_cprod RS subst) 1),
	(dtac (beta_cfun_cprod RS subst) 1),
	(etac Pair_inject 1),
	(fast_tac HOL_cs 1)
	]);

qed_goalw "inst_cprod_pcpo2" Cprod3.thy [cpair_def] "UU = <UU,UU>"
 (fn prems =>
	[
	(rtac sym 1),
	(rtac trans 1),
	(rtac beta_cfun_cprod 1),
	(rtac sym 1),
	(rtac inst_cprod_pcpo 1)
	]);

qed_goal "defined_cpair_rev" Cprod3.thy
 "<a,b> = UU ==> a = UU & b = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(dtac (inst_cprod_pcpo2 RS subst) 1),
	(etac inject_cpair 1)
	]);

qed_goalw "Exh_Cprod2" Cprod3.thy [cpair_def]
	"? a b. z=<a,b>"
 (fn prems =>
	[
	(rtac PairE 1),
	(rtac exI 1),
	(rtac exI 1),
	(etac (beta_cfun_cprod RS ssubst) 1)
	]);

qed_goalw "cprodE" Cprod3.thy [cpair_def]
"[|!!x y. [|p=<x,y> |] ==> Q|] ==> Q"
 (fn prems =>
	[
	(rtac PairE 1),
	(resolve_tac prems 1),
	(etac (beta_cfun_cprod RS ssubst) 1)
	]);

qed_goalw "cfst2" Cprod3.thy [cfst_def,cpair_def] 
	"cfst`<x,y>=x"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun_cprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_fst 1),
	(simp_tac prod_ss  1)
	]);

qed_goalw "csnd2" Cprod3.thy [csnd_def,cpair_def] 
	"csnd`<x,y>=y"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun_cprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_snd 1),
	(simp_tac prod_ss  1)
	]);

qed_goalw "surjective_pairing_Cprod2" Cprod3.thy 
	[cfst_def,csnd_def,cpair_def] "<cfst`p , csnd`p> = p"
 (fn prems =>
	[
	(rtac (beta_cfun_cprod RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_snd 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_fst 1),
	(rtac (surjective_pairing RS sym) 1)
	]);


qed_goalw "less_cprod5b" Cprod3.thy [cfst_def,csnd_def,cpair_def]
 " (p1 << p2) = (cfst`p1 << cfst`p2 & csnd`p1 << csnd`p2)"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_snd 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_snd 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_fst 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac cont_fst 1),
	(rtac less_cprod3b 1)
	]);

qed_goalw "less_cprod5c" Cprod3.thy [cfst_def,csnd_def,cpair_def]
 "<xa,ya> << <x,y> ==> xa<<x & ya << y"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac less_cprod4c 1),
	(dtac (beta_cfun_cprod RS subst) 1),
	(dtac (beta_cfun_cprod RS subst) 1),
	(atac 1)
	]);


qed_goalw "lub_cprod2" Cprod3.thy [cfst_def,csnd_def,cpair_def]
"[|is_chain(S)|] ==> range(S) <<| \
\ <(lub(range(%i.cfst`(S i)))) , lub(range(%i.csnd`(S i)))>"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun_cprod RS ssubst) 1),
	(rtac (beta_cfun RS ext RS ssubst) 1),
	(rtac cont_snd 1),
	(rtac (beta_cfun RS ext RS ssubst) 1),
	(rtac cont_fst 1),
	(rtac lub_cprod 1),
	(atac 1)
	]);

val thelub_cprod2 = (lub_cprod2 RS thelubI);
(*
is_chain ?S1 ==>
 lub (range ?S1) =
 <lub (range (%i. cfst`(?S1 i))), lub (range (%i. csnd`(?S1 i)))>" 
*)
qed_goalw "csplit2" Cprod3.thy [csplit_def]
	"csplit`f`<x,y> = f`x`y"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(cont_tacR 1),
	(simp_tac Cfun_ss 1),
	(simp_tac (Cfun_ss addsimps [cfst2,csnd2]) 1)
	]);

qed_goalw "csplit3" Cprod3.thy [csplit_def]
  "csplit`cpair`z=z"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(cont_tacR 1),
	(simp_tac (Cfun_ss addsimps [surjective_pairing_Cprod2]) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* install simplifier for Cprod                                             *)
(* ------------------------------------------------------------------------ *)

val Cprod_rews = [cfst2,csnd2,csplit2];

val Cprod_ss = Cfun_ss addsimps Cprod_rews;

