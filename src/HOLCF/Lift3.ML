(*  Title: 	HOLCF/lift3.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for lift3.thy
*)

open Lift3;

(* -------------------------------------------------------------------------*)
(* some lemmas restated for class pcpo                                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_lift3b" Lift3.thy "~ Iup(x) << UU"
 (fn prems =>
	[
	(rtac (inst_lift_pcpo RS ssubst) 1),
	(rtac less_lift2b 1)
	]);

qed_goal "defined_Iup2" Lift3.thy "~ Iup(x) = UU"
 (fn prems =>
	[
	(rtac (inst_lift_pcpo RS ssubst) 1),
	(rtac defined_Iup 1)
	]);

(* ------------------------------------------------------------------------ *)
(* continuity for Iup                                                       *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_Iup" Lift3.thy "contlub(Iup)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_lift1a RS sym) 2),
	(fast_tac HOL_cs 3),
	(etac (monofun_Iup RS ch2ch_monofun) 2),
	(res_inst_tac [("f","Iup")] arg_cong  1),
	(rtac lub_equal 1),
	(atac 1),
	(rtac (monofun_Ilift2 RS ch2ch_monofun) 1),
	(etac (monofun_Iup RS ch2ch_monofun) 1),
	(asm_simp_tac Lift_ss 1)
	]);

qed_goal "contX_Iup" Lift3.thy "contX(Iup)"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Iup 1),
	(rtac contlub_Iup 1)
	]);


(* ------------------------------------------------------------------------ *)
(* continuity for Ilift                                                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_Ilift1" Lift3.thy "contlub(Ilift)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_fun RS sym) 2),
	(etac (monofun_Ilift1 RS ch2ch_monofun) 2),
	(rtac ext 1),
	(res_inst_tac [("p","x")] liftE 1),
	(asm_simp_tac Lift_ss 1),
	(rtac (lub_const RS thelubI RS sym) 1),
	(asm_simp_tac Lift_ss 1),
	(etac contlub_cfun_fun 1)
	]);


qed_goal "contlub_Ilift2" Lift3.thy "contlub(Ilift(f))"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac disjE 1),
	(rtac (thelub_lift1a RS ssubst) 2),
	(atac 2),
	(atac 2),
	(asm_simp_tac Lift_ss 2),
	(rtac (thelub_lift1b RS ssubst) 3),
	(atac 3),
	(atac 3),
	(fast_tac HOL_cs 1),
	(asm_simp_tac Lift_ss 2),
	(rtac (chain_UU_I_inverse RS sym) 2),
	(rtac allI 2),
	(res_inst_tac [("p","Y(i)")] liftE 2),
	(asm_simp_tac Lift_ss 2),
	(rtac notE 2),
	(dtac spec 2),
	(etac spec 2),
	(atac 2),
	(rtac (contlub_cfun_arg RS ssubst) 1),
	(etac (monofun_Ilift2 RS ch2ch_monofun) 1),
	(rtac lub_equal2 1),
	(rtac (monofun_fapp2 RS ch2ch_monofun) 2),
	(etac (monofun_Ilift2 RS ch2ch_monofun) 2),
	(etac (monofun_Ilift2 RS ch2ch_monofun) 2),
	(rtac (chain_mono2 RS exE) 1),
	(atac 2),
	(etac exE 1),
	(etac exE 1),
	(rtac exI 1),
	(res_inst_tac [("s","Iup(x)"),("t","Y(i)")] ssubst 1),
	(atac 1),
	(rtac defined_Iup2 1),
	(rtac exI 1),
	(strip_tac 1),
	(res_inst_tac [("p","Y(i)")] liftE 1),
	(asm_simp_tac Lift_ss 2),
	(res_inst_tac [("P","Y(i) = UU")] notE 1),
	(fast_tac HOL_cs 1),
	(rtac (inst_lift_pcpo RS ssubst) 1),
	(atac 1)
	]);

qed_goal "contX_Ilift1" Lift3.thy "contX(Ilift)"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Ilift1 1),
	(rtac contlub_Ilift1 1)
	]);

qed_goal "contX_Ilift2" Lift3.thy "contX(Ilift(f))"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Ilift2 1),
	(rtac contlub_Ilift2 1)
	]);


(* ------------------------------------------------------------------------ *)
(* continuous versions of lemmas for ('a)u                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Exh_Lift1" Lift3.thy [up_def] "z = UU | (? x. z = up[x])"
 (fn prems =>
	[
	(simp_tac (Lift_ss addsimps [contX_Iup]) 1),
	(rtac (inst_lift_pcpo RS ssubst) 1),
	(rtac Exh_Lift 1)
	]);

qed_goalw "inject_up" Lift3.thy [up_def] "up[x]=up[y] ==> x=y"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac inject_Iup 1),
	(etac box_equals 1),
	(simp_tac (Lift_ss addsimps [contX_Iup]) 1),
	(simp_tac (Lift_ss addsimps [contX_Iup]) 1)
	]);

qed_goalw "defined_up" Lift3.thy [up_def] "~ up[x]=UU"
 (fn prems =>
	[
	(simp_tac (Lift_ss addsimps [contX_Iup]) 1),
	(rtac defined_Iup2 1)
	]);

qed_goalw "liftE1" Lift3.thy [up_def] 
	"[| p=UU ==> Q; !!x. p=up[x]==>Q|] ==>Q"
 (fn prems =>
	[
	(rtac liftE 1),
	(resolve_tac prems 1),
	(etac (inst_lift_pcpo RS ssubst) 1),
	(resolve_tac (tl prems) 1),
	(asm_simp_tac (Lift_ss addsimps [contX_Iup]) 1)
	]);


qed_goalw "lift1" Lift3.thy [up_def,lift_def] "lift[f][UU]=UU"
 (fn prems =>
	[
	(rtac (inst_lift_pcpo RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iup,contX_Ilift1,
		contX_Ilift2,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iup,contX_Ilift1,
		contX_Ilift2,contX2contX_CF1L]) 1)),
	(simp_tac (Lift_ss addsimps [contX_Iup,contX_Ilift1,contX_Ilift2]) 1)
	]);

qed_goalw "lift2" Lift3.thy [up_def,lift_def] "lift[f][up[x]]=f[x]"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Iup 1),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iup,contX_Ilift1,
		contX_Ilift2,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Ilift2 1),
	(simp_tac (Lift_ss addsimps [contX_Iup,contX_Ilift1,contX_Ilift2]) 1)
	]);

qed_goalw "less_lift4b" Lift3.thy [up_def,lift_def] "~ up[x] << UU"
 (fn prems =>
	[
	(simp_tac (Lift_ss addsimps [contX_Iup]) 1),
	(rtac less_lift3b 1)
	]);

qed_goalw "less_lift4c" Lift3.thy [up_def,lift_def]
	 "(up[x]<<up[y]) = (x<<y)"
 (fn prems =>
	[
	(simp_tac (Lift_ss addsimps [contX_Iup]) 1),
	(rtac less_lift2c 1)
	]);

qed_goalw "thelub_lift2a" Lift3.thy [up_def,lift_def] 
"[| is_chain(Y); ? i x. Y(i) = up[x] |] ==>\
\      lub(range(Y)) = up[lub(range(%i. lift[LAM x. x][Y(i)]))]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iup,contX_Ilift1,
		contX_Ilift2,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iup,contX_Ilift1,
		contX_Ilift2,contX2contX_CF1L]) 1)),

	(rtac (beta_cfun RS ext RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iup,contX_Ilift1,
		contX_Ilift2,contX2contX_CF1L]) 1)),
	(rtac thelub_lift1a 1),
	(atac 1),
	(etac exE 1),
	(etac exE 1),
	(rtac exI 1),
	(rtac exI 1),
	(etac box_equals 1),
	(rtac refl 1),
	(simp_tac (Lift_ss addsimps [contX_Iup]) 1)
	]);



qed_goalw "thelub_lift2b" Lift3.thy [up_def,lift_def] 
"[| is_chain(Y); ! i x. ~ Y(i) = up[x] |] ==> lub(range(Y)) = UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (inst_lift_pcpo RS ssubst) 1),
	(rtac thelub_lift1b 1),
	(atac 1),
	(strip_tac 1),
	(dtac spec 1),
	(dtac spec 1),
	(rtac swap 1),
	(atac 1),
	(dtac notnotD 1),
	(etac box_equals 1),
	(rtac refl 1),
	(simp_tac (Lift_ss addsimps [contX_Iup]) 1)
	]);


qed_goal "lift_lemma2" Lift3.thy  " (? x.z = up[x]) = (~z=UU)"
 (fn prems =>
	[
	(rtac iffI 1),
	(etac exE 1),
	(hyp_subst_tac 1),
	(rtac defined_up 1),
	(res_inst_tac [("p","z")] liftE1 1),
	(etac notE 1),
	(atac 1),
	(etac exI 1)
	]);


qed_goal "thelub_lift2a_rev" Lift3.thy  
"[| is_chain(Y); lub(range(Y)) = up[x] |] ==> ? i x. Y(i) = up[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac exE 1),
	(rtac chain_UU_I_inverse2 1),
	(rtac (lift_lemma2 RS iffD1) 1),
	(etac exI 1),
	(rtac exI 1),
	(rtac (lift_lemma2 RS iffD2) 1),
	(atac 1)
	]);

qed_goal "thelub_lift2b_rev" Lift3.thy  
"[| is_chain(Y); lub(range(Y)) = UU |] ==> ! i x. ~ Y(i) = up[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac allI 1),
	(rtac (notex2all RS iffD1) 1),
	(rtac contrapos 1),
	(etac (lift_lemma2 RS iffD1) 2),
	(rtac notnotI 1),
	(rtac (chain_UU_I RS spec) 1),
	(atac 1),
	(atac 1)
	]);


qed_goal "thelub_lift3" Lift3.thy  
"is_chain(Y) ==> lub(range(Y)) = UU |\
\                lub(range(Y)) = up[lub(range(%i. lift[LAM x. x][Y(i)]))]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac disjE 1),
	(rtac disjI1 2),
	(rtac thelub_lift2b 2),
	(atac 2),
	(atac 2),
	(rtac disjI2 2),
	(rtac thelub_lift2a 2),
	(atac 2),
	(atac 2),
	(fast_tac HOL_cs 1)
	]);

qed_goal "lift3" Lift3.thy "lift[up][x]=x"
 (fn prems =>
	[
	(res_inst_tac [("p","x")] liftE1 1),
	(asm_simp_tac (Cfun_ss addsimps [lift1,lift2]) 1),
	(asm_simp_tac (Cfun_ss addsimps [lift1,lift2]) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* install simplifier for ('a)u                                             *)
(* ------------------------------------------------------------------------ *)

val lift_rews = [lift1,lift2,defined_up];
