(*  Title: 	HOLCF/porder.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for theory porder.thy 
*)

open Porder0;
open Porder;

val box_less = prove_goal Porder.thy 
"[| a << b; c << a; b << d|] ==> c << d"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac trans_less 1),
	(etac trans_less 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* lubs are unique                                                          *)
(* ------------------------------------------------------------------------ *)

val unique_lub  = prove_goalw Porder.thy [is_lub, is_ub] 
	"[| S <<| x ; S <<| y |] ==> x=y"
( fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac conjE 1),
	(etac conjE 1),
	(rtac antisym_less 1),
	(rtac mp 1),((etac allE 1) THEN (atac 1) THEN (atac 1)),
	(rtac mp 1),((etac allE 1) THEN (atac 1) THEN (atac 1))
	]);

(* ------------------------------------------------------------------------ *)
(* chains are monotone functions                                            *)
(* ------------------------------------------------------------------------ *)

val chain_mono = prove_goalw Porder.thy [is_chain]
	" is_chain(F) ==> x<y --> F(x)<<F(y)"
( fn prems =>
	[
	(cut_facts_tac prems 1),
	(nat_ind_tac "y" 1),
	(rtac impI 1),
	(etac less_zeroE 1),
	(rtac (less_Suc_eq RS ssubst) 1),
	(strip_tac 1),
	(etac disjE 1),
	(rtac trans_less 1),
	(etac allE 2),
	(atac 2),
	(fast_tac HOL_cs 1),
	(hyp_subst_tac 1),
	(etac allE 1),
	(atac 1)
	]);

val chain_mono3 = prove_goal  Porder.thy 
	"[| is_chain(F); x <= y |] ==> F(x) << F(y)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (le_imp_less_or_eq RS disjE) 1),
	(atac 1),
	(etac (chain_mono RS mp) 1),
	(atac 1),
	(hyp_subst_tac 1),
	(rtac refl_less 1)
	]);

(* ------------------------------------------------------------------------ *)
(* Lemma for reasoning by cases on the natural numbers                      *)
(* ------------------------------------------------------------------------ *)

val nat_less_cases = prove_goal Porder.thy 
	"[| (m::nat) < n ==> P(n,m); m=n ==> P(n,m);n < m ==> P(n,m)|]==>P(n,m)"
( fn prems =>
	[
	(res_inst_tac [("m1","n"),("n1","m")] (less_linear RS disjE) 1),
	(etac disjE 2),
	(etac (hd (tl (tl prems))) 1),
	(etac (sym RS hd (tl prems)) 1),
	(etac (hd prems) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* The range of a chain is a totaly ordered     <<                           *)
(* ------------------------------------------------------------------------ *)

val chain_is_tord = prove_goalw Porder.thy [is_tord]
	"is_chain(F) ==> is_tord(range(F))"
( fn prems =>
	[
	(cut_facts_tac prems 1),
	(rewrite_goals_tac [range_def]),
	(rtac allI 1 ),
	(rtac allI 1 ),
	(rtac (mem_Collect_eq RS ssubst) 1),
	(rtac (mem_Collect_eq RS ssubst) 1),
	(strip_tac 1),
	(etac conjE 1),
	(etac exE 1),
	(etac exE 1),
	(hyp_subst_tac 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("m","xa"),("n","xb")] (nat_less_cases) 1),
	(rtac disjI1 1),
	(rtac (chain_mono RS mp) 1),
	(atac 1),
	(atac 1),
	(rtac disjI1 1),
	(hyp_subst_tac 1),
	(rtac refl_less 1),
	(rtac disjI2 1),
	(rtac (chain_mono RS mp) 1),
	(atac 1),
	(atac 1)
	]);


(* ------------------------------------------------------------------------ *)
(* technical lemmas about lub and is_lub, use above results about @         *)
(* ------------------------------------------------------------------------ *)

val lubI = prove_goal Porder.thy "(? x. M <<| x) ==> M <<| lub(M)"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (lub RS ssubst) 1),
	(etac selectI2 1)
	]);

val lubE = prove_goal Porder.thy " M <<| lub(M) ==>  ? x. M <<| x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exI 1)
	]);

val lub_eq = prove_goal Porder.thy 
	"(? x. M <<| x)  = M <<| lub(M)"
(fn prems => 
	[
	(rtac (lub RS ssubst) 1),
	(rtac (select_eq_Ex RS subst) 1),
	(rtac refl 1)
	]);


val thelubI = prove_goal  Porder.thy " M <<| l ==> lub(M) = l"
(fn prems =>
	[
	(cut_facts_tac prems 1), 
	(rtac unique_lub 1),
	(rtac (lub RS ssubst) 1),
	(etac selectI 1),
	(atac 1)
	]);


(* ------------------------------------------------------------------------ *)
(* access to some definition as inference rule                              *)
(* ------------------------------------------------------------------------ *)

val is_lubE = prove_goalw  Porder.thy [is_lub]
	"S <<| x  ==> S <| x & (! u. S <| u  --> x << u)"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(atac 1)
	]);

val is_lubI = prove_goalw  Porder.thy [is_lub]
	"S <| x & (! u. S <| u  --> x << u) ==> S <<| x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(atac 1)
	]);

val is_chainE = prove_goalw Porder.thy [is_chain] 
 "is_chain(F) ==> ! i. F(i) << F(Suc(i))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(atac 1)]);

val is_chainI = prove_goalw Porder.thy [is_chain] 
 "! i. F(i) << F(Suc(i)) ==> is_chain(F) "
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(atac 1)]);

(* ------------------------------------------------------------------------ *)
(* technical lemmas about (least) upper bounds of chains                    *)
(* ------------------------------------------------------------------------ *)

val ub_rangeE = prove_goalw  Porder.thy [is_ub]
	"range(S) <| x  ==> ! i. S(i) << x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(rtac mp 1),
	(etac spec 1),
	(rtac rangeI 1)
	]);

val ub_rangeI = prove_goalw Porder.thy [is_ub]
	"! i. S(i) << x  ==> range(S) <| x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(etac rangeE 1),
	(hyp_subst_tac 1),
	(etac spec 1)
	]);

val is_ub_lub = (is_lubE RS conjunct1 RS ub_rangeE RS spec);
(* range(?S1) <<| ?x1 ==> ?S1(?x) << ?x1                                    *)

val is_lub_lub = (is_lubE RS conjunct2 RS spec RS mp);
(* [| ?S3 <<| ?x3; ?S3 <| ?x1 |] ==> ?x3 << ?x1                             *)

(* ------------------------------------------------------------------------ *)
(* Prototype lemmas for class pcpo                                          *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* a technical argument about << on void                                    *)
(* ------------------------------------------------------------------------ *)

val less_void = prove_goal Porder.thy "((u1::void) << u2) = (u1 = u2)"
(fn prems =>
	[
	(rtac (inst_void_po RS ssubst) 1),
	(rewrite_goals_tac [less_void_def]),
	(rtac iffI 1),
	(rtac injD 1),
	(atac 2),
	(rtac inj_inverseI 1),
	(rtac Rep_Void_inverse 1),
	(etac arg_cong 1)
	]);

(* ------------------------------------------------------------------------ *)
(* void is pointed. The least element is UU_void                            *)
(* ------------------------------------------------------------------------ *)

val minimal_void = prove_goal Porder.thy  	"UU_void << x"
(fn prems =>
	[
	(rtac (inst_void_po RS ssubst) 1),
	(rewrite_goals_tac [less_void_def]),
	(simp_tac (HOL_ss addsimps [unique_void]) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* UU_void is the trivial lub of all chains in void                         *)
(* ------------------------------------------------------------------------ *)

val lub_void = prove_goalw  Porder.thy [is_lub] "M <<| UU_void"
(fn prems =>
	[
	(rtac conjI 1),
	(rewrite_goals_tac [is_ub]),
	(strip_tac 1),
	(rtac (inst_void_po RS ssubst) 1),
	(rewrite_goals_tac [less_void_def]),
	(simp_tac (HOL_ss addsimps [unique_void]) 1),
	(strip_tac 1),
	(rtac minimal_void 1)
	]);

(* ------------------------------------------------------------------------ *)
(* lub(?M) = UU_void                                                        *)
(* ------------------------------------------------------------------------ *)

val thelub_void = (lub_void RS thelubI);

(* ------------------------------------------------------------------------ *)
(* void is a cpo wrt. countable chains                                      *)
(* ------------------------------------------------------------------------ *)

val cpo_void = prove_goal Porder.thy
	"is_chain((S::nat=>void)) ==> ? x. range(S) <<| x "
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("x","UU_void")] exI 1),
	(rtac lub_void 1)
	]);

(* ------------------------------------------------------------------------ *)
(* end of prototype lemmas for class pcpo                                   *)
(* ------------------------------------------------------------------------ *)


(* ------------------------------------------------------------------------ *)
(* the reverse law of anti--symmetrie of <<                                 *)
(* ------------------------------------------------------------------------ *)

val antisym_less_inverse = prove_goal Porder.thy "x=y ==> x << y & y << x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac conjI 1),
	((rtac subst 1) THEN (rtac refl_less 2) THEN (atac 1)),
	((rtac subst 1) THEN (rtac refl_less 2) THEN (etac sym 1))
	]);

(* ------------------------------------------------------------------------ *)
(* results about finite chains                                              *)
(* ------------------------------------------------------------------------ *)

val lub_finch1 = prove_goalw Porder.thy [max_in_chain_def]
	"[| is_chain(C) ; max_in_chain(i,C)|] ==> range(C) <<| C(i)"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_lubI 1),
	(rtac conjI 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(res_inst_tac [("m","i")] nat_less_cases 1),
	(rtac (antisym_less_inverse RS conjunct2) 1),
	(etac (disjI1 RS less_or_eq_imp_le RS rev_mp) 1),
	(etac spec 1),
	(rtac (antisym_less_inverse RS conjunct2) 1),
	(etac (disjI2 RS less_or_eq_imp_le RS rev_mp) 1),
	(etac spec 1),
	(etac (chain_mono RS mp) 1),
	(atac 1),
	(strip_tac 1),
	(etac (ub_rangeE RS spec) 1)
	]);	

val lub_finch2 = prove_goalw Porder.thy [finite_chain_def]
	"finite_chain(C) ==> range(C) <<| C(@ i. max_in_chain(i,C))"
 (fn prems=>
	[
	(cut_facts_tac prems 1),
	(rtac lub_finch1 1),
	(etac conjunct1 1),
	(rtac selectI2 1),
	(etac conjunct2 1)
	]);


val bin_chain = prove_goal Porder.thy "x<<y ==> is_chain(%i. if(i=0,x,y))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_chainI 1),
	(rtac allI 1),
	(nat_ind_tac "i" 1),
	(asm_simp_tac nat_ss 1),
	(asm_simp_tac nat_ss 1),
	(rtac refl_less 1)
	]);

val bin_chainmax = prove_goalw Porder.thy [max_in_chain_def,le_def]
	"x<<y ==> max_in_chain(Suc(0),%i. if(i=0,x,y))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac allI 1),
	(nat_ind_tac "j" 1),
	(asm_simp_tac nat_ss 1),
	(asm_simp_tac nat_ss 1)
	]);

val lub_bin_chain = prove_goal Porder.thy 
	"x << y ==> range(%i. if(i = 0,x,y)) <<| y"
(fn prems=>
	[ (cut_facts_tac prems 1),
	(res_inst_tac [("s","if(Suc(0) = 0,x,y)")] subst 1),
	(rtac lub_finch1 2),
	(etac bin_chain 2),
	(etac bin_chainmax 2),
	(simp_tac nat_ss  1)
	]);

(* ------------------------------------------------------------------------ *)
(* the maximal element in a chain is its lub                                *)
(* ------------------------------------------------------------------------ *)

val lub_chain_maxelem = prove_goal Porder.thy
"[|is_chain(Y);? i.Y(i)=c;!i.Y(i)<<c|] ==> lub(range(Y)) = c"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac thelubI 1),
	(rtac is_lubI 1),
	(rtac conjI 1),
	(etac ub_rangeI 1),
	(strip_tac 1),
	(res_inst_tac [("P","%i.Y(i)=c")] exE 1),
	(atac 1),
	(hyp_subst_tac 1),
	(etac (ub_rangeE RS spec) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* the lub of a constant chain is the constant                              *)
(* ------------------------------------------------------------------------ *)

val lub_const = prove_goal Porder.thy "range(%x.c) <<| c"
 (fn prems =>
	[
	(rtac is_lubI 1),
	(rtac conjI 1),
	(rtac ub_rangeI 1),
	(strip_tac 1),
	(rtac refl_less 1),
	(strip_tac 1),
	(etac (ub_rangeE RS spec) 1)
	]);



