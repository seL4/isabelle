(*  Title: 	HOLCF/lift2.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for lift2.thy 
*)

open Lift2;

(* -------------------------------------------------------------------------*)
(* type ('a)u is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_lift" Lift2.thy "UU_lift << z"
 (fn prems =>
	[
	(rtac (inst_lift_po RS ssubst) 1),
	(rtac less_lift1a 1)
	]);

(* -------------------------------------------------------------------------*)
(* access to less_lift in class po                                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_lift2b" Lift2.thy "~ Iup(x) << UU_lift"
 (fn prems =>
	[
	(rtac (inst_lift_po RS ssubst) 1),
	(rtac less_lift1b 1)
	]);

qed_goal "less_lift2c" Lift2.thy "(Iup(x)<<Iup(y)) = (x<<y)"
 (fn prems =>
	[
	(rtac (inst_lift_po RS ssubst) 1),
	(rtac less_lift1c 1)
	]);

(* ------------------------------------------------------------------------ *)
(* Iup and Ilift are monotone                                               *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_Iup" Lift2.thy [monofun] "monofun(Iup)"
 (fn prems =>
	[
	(strip_tac 1),
	(etac (less_lift2c RS iffD2) 1)
	]);

qed_goalw "monofun_Ilift1" Lift2.thy [monofun] "monofun(Ilift)"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac (less_fun RS iffD2) 1),
	(strip_tac 1),
	(res_inst_tac [("p","xa")] liftE 1),
	(asm_simp_tac Lift_ss 1),
	(asm_simp_tac Lift_ss 1),
	(etac monofun_cfun_fun 1)
	]);

qed_goalw "monofun_Ilift2" Lift2.thy [monofun] "monofun(Ilift(f))"
 (fn prems =>
	[
	(strip_tac 1),
	(res_inst_tac [("p","x")] liftE 1),
	(asm_simp_tac Lift_ss 1),
	(asm_simp_tac Lift_ss 1),
	(res_inst_tac [("p","y")] liftE 1),
	(hyp_subst_tac 1),
	(rtac notE 1),
	(rtac less_lift2b 1),
	(atac 1),
	(asm_simp_tac Lift_ss 1),
	(rtac monofun_cfun_arg 1),
	(hyp_subst_tac 1),
	(etac (less_lift2c  RS iffD1) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* Some kind of surjectivity lemma                                          *)
(* ------------------------------------------------------------------------ *)


qed_goal "lift_lemma1" Lift2.thy  "z=Iup(x) ==> Iup(Ilift(LAM x.x)(z)) = z"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac Lift_ss 1)
	]);

(* ------------------------------------------------------------------------ *)
(* ('a)u is a cpo                                                           *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_lift1a" Lift2.thy 
"[|is_chain(Y);? i x.Y(i)=Iup(x)|] ==>\
\ range(Y) <<| Iup(lub(range(%i.(Ilift (LAM x.x) (Y(i))))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_lubI 1),
	(rtac conjI 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(res_inst_tac [("p","Y(i)")] liftE 1),
	(res_inst_tac [("s","UU_lift"),("t","Y(i)")] subst 1),
	(etac sym 1),
	(rtac minimal_lift 1),
	(res_inst_tac [("t","Y(i)")] (lift_lemma1 RS subst) 1),
	(atac 1),
	(rtac (less_lift2c RS iffD2) 1),
	(rtac is_ub_thelub 1),
	(etac (monofun_Ilift2 RS ch2ch_monofun) 1),
	(strip_tac 1),
	(res_inst_tac [("p","u")] liftE 1),
	(etac exE 1),
	(etac exE 1),
	(res_inst_tac [("P","Y(i)<<UU_lift")] notE 1),
	(res_inst_tac [("s","Iup(x)"),("t","Y(i)")] ssubst 1),
	(atac 1),
	(rtac less_lift2b 1),
	(hyp_subst_tac 1),
	(etac (ub_rangeE RS spec) 1),
	(res_inst_tac [("t","u")] (lift_lemma1 RS subst) 1),
	(atac 1),
	(rtac (less_lift2c RS iffD2) 1),
	(rtac is_lub_thelub 1),
	(etac (monofun_Ilift2 RS ch2ch_monofun) 1),
	(etac (monofun_Ilift2 RS ub2ub_monofun) 1)
	]);

qed_goal "lub_lift1b" Lift2.thy 
"[|is_chain(Y);!i x. Y(i)~=Iup(x)|] ==>\
\ range(Y) <<| UU_lift"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_lubI 1),
	(rtac conjI 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(res_inst_tac [("p","Y(i)")] liftE 1),
	(res_inst_tac [("s","UU_lift"),("t","Y(i)")] ssubst 1),
	(atac 1),
	(rtac refl_less 1),
	(rtac notE 1),
	(dtac spec 1),
	(dtac spec 1),
	(atac 1),
	(atac 1),
	(strip_tac 1),
	(rtac minimal_lift 1)
	]);

val thelub_lift1a = lub_lift1a RS thelubI;
(*
[| is_chain ?Y1; ? i x. ?Y1 i = Iup x |] ==>
 lub (range ?Y1) = Iup (lub (range (%i. Ilift (LAM x. x) (?Y1 i))))
*)

val thelub_lift1b = lub_lift1b RS thelubI;
(*
[| is_chain ?Y1; ! i x. ?Y1 i ~= Iup x |] ==>
 lub (range ?Y1) = UU_lift
*)

qed_goal "cpo_lift" Lift2.thy 
	"is_chain(Y::nat=>('a)u) ==> ? x.range(Y) <<|x"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac disjE 1),
	(rtac exI 2),
	(etac lub_lift1a 2),
	(atac 2),
	(rtac exI 2),
	(etac lub_lift1b 2),
	(atac 2),
	(fast_tac HOL_cs 1)
	]);

