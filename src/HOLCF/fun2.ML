(*  Title: 	HOLCF/fun2.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for fun2.thy 
*)

open Fun2;

(* ------------------------------------------------------------------------ *)
(* Type 'a::term => 'b::pcpo is pointed                                     *)
(* ------------------------------------------------------------------------ *)

val minimal_fun = prove_goalw  Fun2.thy [UU_fun_def] "UU_fun << f"
(fn prems =>
	[
	(rtac (inst_fun_po RS ssubst) 1),
	(rewrite_goals_tac [less_fun_def]),
	(fast_tac (HOL_cs addSIs [minimal]) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* make the symbol << accessible for type fun                               *)
(* ------------------------------------------------------------------------ *)

val less_fun = prove_goal  Fun2.thy  "(f1 << f2) = (! x. f1(x) << f2(x))"
(fn prems =>
	[
	(rtac (inst_fun_po RS ssubst) 1),
	(fold_goals_tac [less_fun_def]),
	(rtac refl 1)
	]);

(* ------------------------------------------------------------------------ *)
(* chains of functions yield chains in the po range                         *)
(* ------------------------------------------------------------------------ *)

val ch2ch_fun = prove_goal  Fun2.thy 
	"is_chain(S::nat=>('a::term => 'b::po)) ==> is_chain(% i.S(i)(x))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rewrite_goals_tac [is_chain]),
	(rtac allI 1),
	(rtac spec 1),
	(rtac (less_fun RS subst) 1),
	(etac allE 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* upper bounds of function chains yield upper bound in the po range        *)
(* ------------------------------------------------------------------------ *)

val ub2ub_fun = prove_goal Fun2.thy 
   " range(S::nat=>('a::term => 'b::po)) <| u ==> range(%i. S(i,x)) <| u(x)"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(rtac allE 1),
	(rtac (less_fun RS subst) 1),
	(etac (ub_rangeE RS spec) 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* Type 'a::term => 'b::pcpo is chain complete                              *)
(* ------------------------------------------------------------------------ *)

val lub_fun = prove_goal  Fun2.thy
	"is_chain(S::nat=>('a::term => 'b::pcpo)) ==> \
\        range(S) <<| (% x.lub(range(% i.S(i)(x))))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_lubI 1),
	(rtac conjI 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(rtac (less_fun RS ssubst) 1),
	(rtac allI 1),
	(rtac is_ub_thelub 1),
	(etac ch2ch_fun 1),
	(strip_tac 1),
	(rtac (less_fun RS ssubst) 1),
	(rtac allI 1),
	(rtac is_lub_thelub 1),
	(etac ch2ch_fun 1),
	(etac ub2ub_fun 1)
	]);

val thelub_fun = (lub_fun RS thelubI);
(* is_chain(?S1) ==> lub(range(?S1)) = (%x. lub(range(%i. ?S1(i,x)))) *)

val cpo_fun = prove_goal  Fun2.thy
	"is_chain(S::nat=>('a::term => 'b::pcpo)) ==> ? x. range(S) <<| x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac exI 1),
	(etac lub_fun 1)
	]);

