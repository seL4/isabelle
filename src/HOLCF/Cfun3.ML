(*  Title: 	HOLCF/cfun3.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

open Cfun3;

(* ------------------------------------------------------------------------ *)
(* the contlub property for fapp its 'first' argument                       *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_fapp1" Cfun3.thy "contlub(fapp)"
(fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (expand_fun_eq RS iffD2) 1),
	(strip_tac 1),
	(rtac (thelub_cfun RS ssubst) 1),
	(atac 1),
	(rtac (Cfunapp2 RS ssubst) 1),
	(etac contX_lubcfun 1),
	(rtac (thelub_fun RS ssubst) 1),
	(etac (monofun_fapp1 RS ch2ch_monofun) 1),
	(rtac refl 1)
	]);


(* ------------------------------------------------------------------------ *)
(* the contX property for fapp in its first argument                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "contX_fapp1" Cfun3.thy "contX(fapp)"
(fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_fapp1 1),
	(rtac contlub_fapp1 1)
	]);


(* ------------------------------------------------------------------------ *)
(* contlub, contX properties of fapp in its first argument in mixfix _[_]   *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_cfun_fun" Cfun3.thy 
"is_chain(FY) ==>\
\ lub(range(FY))[x] = lub(range(%i.FY(i)[x]))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac trans 1),
	(etac (contlub_fapp1 RS contlubE RS spec RS mp RS fun_cong) 1),
	(rtac (thelub_fun RS ssubst) 1),
	(etac (monofun_fapp1 RS ch2ch_monofun) 1),
	(rtac refl 1)
	]);


qed_goal "contX_cfun_fun" Cfun3.thy 
"is_chain(FY) ==>\
\ range(%i.FY(i)[x]) <<| lub(range(FY))[x]"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac thelubE 1),
	(etac ch2ch_fappL 1),
	(etac (contlub_cfun_fun RS sym) 1)
	]);


(* ------------------------------------------------------------------------ *)
(* contlub, contX  properties of fapp in both argument in mixfix _[_]       *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_cfun" Cfun3.thy 
"[|is_chain(FY);is_chain(TY)|] ==>\
\ lub(range(FY))[lub(range(TY))] = lub(range(%i.FY(i)[TY(i)]))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac contlub_CF2 1),
	(rtac contX_fapp1 1),
	(rtac allI 1),
	(rtac contX_fapp2 1),
	(atac 1),
	(atac 1)
	]);

qed_goal "contX_cfun" Cfun3.thy 
"[|is_chain(FY);is_chain(TY)|] ==>\
\ range(%i.FY(i)[TY(i)]) <<| lub(range(FY))[lub(range(TY))]"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac thelubE 1),
	(rtac (monofun_fapp1 RS ch2ch_MF2LR) 1),
	(rtac allI 1),
	(rtac monofun_fapp2 1),
	(atac 1),
	(atac 1),
	(etac (contlub_cfun RS sym) 1),
	(atac 1)
	]);


(* ------------------------------------------------------------------------ *)
(* contX2contX lemma for fapp                                               *)
(* ------------------------------------------------------------------------ *)

qed_goal "contX2contX_fapp" Cfun3.thy 
	"[|contX(%x.ft(x));contX(%x.tt(x))|] ==> contX(%x.(ft(x))[tt(x)])"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac contX2contX_app2 1),
	(rtac contX2contX_app2 1),
	(rtac contX_const 1),
	(rtac contX_fapp1 1),
	(atac 1),
	(rtac contX_fapp2 1),
	(atac 1)
	]);



(* ------------------------------------------------------------------------ *)
(* contX2mono Lemma for %x. LAM y. c1(x,y)                                  *)
(* ------------------------------------------------------------------------ *)

qed_goal "contX2mono_LAM" Cfun3.thy 
 "[|!x.contX(c1(x)); !y.monofun(%x.c1(x,y))|] ==>\
\	 		monofun(%x. LAM y. c1(x,y))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac monofunI 1),
	(strip_tac 1),
	(rtac (less_cfun RS ssubst) 1),
	(rtac (less_fun RS ssubst) 1),
	(rtac allI 1),
	(rtac (beta_cfun RS ssubst) 1),
	(etac spec 1),
	(rtac (beta_cfun RS ssubst) 1),
	(etac spec 1),
	(etac ((hd (tl prems)) RS spec RS monofunE RS spec RS spec RS mp) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* contX2contX Lemma for %x. LAM y. c1(x,y)                                 *)
(* ------------------------------------------------------------------------ *)

qed_goal "contX2contX_LAM" Cfun3.thy 
 "[| !x.contX(c1(x)); !y.contX(%x.c1(x,y)) |] ==> contX(%x. LAM y. c1(x,y))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac monocontlub2contX 1),
	(etac contX2mono_LAM 1),
	(rtac (contX2mono RS allI) 1),
	(etac spec 1),
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (thelub_cfun RS ssubst) 1),
	(rtac (contX2mono_LAM RS ch2ch_monofun) 1),
	(atac 1),
	(rtac (contX2mono RS allI) 1),
	(etac spec 1),
	(atac 1),
	(res_inst_tac [("f","fabs")] arg_cong 1),
	(rtac ext 1),
	(rtac (beta_cfun RS ext RS ssubst) 1),
	(etac spec 1),
	(rtac (contX2contlub RS contlubE 
		RS spec RS mp ) 1),
	(etac spec 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* elimination of quantifier in premisses of contX2contX_LAM yields good    *)
(* lemma for the contX tactic                                               *)
(* ------------------------------------------------------------------------ *)

val contX2contX_LAM2 = (allI RSN (2,(allI RS contX2contX_LAM)));
(*
	[| !!x. contX(?c1.0(x)); !!y. contX(%x. ?c1.0(x,y)) |] ==>
					contX(%x. LAM y. ?c1.0(x,y))
*)

(* ------------------------------------------------------------------------ *)
(* contX2contX tactic                                                       *)
(* ------------------------------------------------------------------------ *)

val contX_lemmas = [contX_const, contX_id, contX_fapp2,
			contX2contX_fapp,contX2contX_LAM2];


val contX_tac = (fn i => (resolve_tac contX_lemmas i));

val contX_tacR = (fn i => (REPEAT (contX_tac i)));

(* ------------------------------------------------------------------------ *)
(* function application _[_]  is strict in its first arguments              *)
(* ------------------------------------------------------------------------ *)

qed_goal "strict_fapp1" Cfun3.thy "(UU::'a->'b)[x] = (UU::'b)"
 (fn prems =>
	[
	(rtac (inst_cfun_pcpo RS ssubst) 1),
	(rewrite_goals_tac [UU_cfun_def]),
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tac 1),
	(rtac refl 1)
	]);


(* ------------------------------------------------------------------------ *)
(* results about strictify                                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Istrictify1" Cfun3.thy [Istrictify_def]
	"Istrictify(f)(UU)= (UU)"
 (fn prems =>
	[
	(rtac select_equality 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);

qed_goalw "Istrictify2" Cfun3.thy [Istrictify_def]
	"~x=UU ==> Istrictify(f)(x)=f[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac select_equality 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "monofun_Istrictify1" Cfun3.thy "monofun(Istrictify)"
 (fn prems =>
	[
	(rtac monofunI 1),
	(strip_tac 1),
	(rtac (less_fun RS iffD2) 1),
	(strip_tac 1),
	(res_inst_tac [("Q","xa=UU")] (excluded_middle RS disjE) 1),
	(rtac (Istrictify2 RS ssubst) 1),
	(atac 1),
	(rtac (Istrictify2 RS ssubst) 1),
	(atac 1),
	(rtac monofun_cfun_fun 1),
	(atac 1),
	(hyp_subst_tac 1),
	(rtac (Istrictify1 RS ssubst) 1),
	(rtac (Istrictify1 RS ssubst) 1),
	(rtac refl_less 1)
	]);

qed_goal "monofun_Istrictify2" Cfun3.thy "monofun(Istrictify(f))"
 (fn prems =>
	[
	(rtac monofunI 1),
	(strip_tac 1),
	(res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
	(rtac (Istrictify2 RS ssubst) 1),
	(etac notUU_I 1),
	(atac 1),
	(rtac (Istrictify2 RS ssubst) 1),
	(atac 1),
	(rtac monofun_cfun_arg 1),
	(atac 1),
	(hyp_subst_tac 1),
	(rtac (Istrictify1 RS ssubst) 1),
	(rtac minimal 1)
	]);


qed_goal "contlub_Istrictify1" Cfun3.thy "contlub(Istrictify)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac (expand_fun_eq RS iffD2) 1),
	(strip_tac 1),
	(rtac (thelub_fun RS ssubst) 1),
	(etac (monofun_Istrictify1 RS ch2ch_monofun) 1),
	(res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
	(rtac (Istrictify2 RS ssubst) 1),
	(atac 1),
	(rtac (Istrictify2 RS ext RS ssubst) 1),
	(atac 1),
	(rtac (thelub_cfun RS ssubst) 1),
	(atac 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_lubcfun 1),
	(atac 1),
	(rtac refl 1),
	(hyp_subst_tac 1),
	(rtac (Istrictify1 RS ssubst) 1),
	(rtac (Istrictify1 RS ext RS ssubst) 1),
	(rtac (chain_UU_I_inverse RS sym) 1),
	(rtac (refl RS allI) 1)
	]);

qed_goal "contlub_Istrictify2" Cfun3.thy "contlub(Istrictify(f::'a -> 'b))"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(res_inst_tac [("Q","lub(range(Y))=(UU::'a)")] classical2 1),
	(res_inst_tac [("t","lub(range(Y))")] subst 1),
	(rtac sym 1),
	(atac 1),
	(rtac (Istrictify1 RS ssubst) 1),
	(rtac sym 1),
	(rtac chain_UU_I_inverse 1),
	(strip_tac 1),
	(res_inst_tac [("t","Y(i)"),("s","UU::'a")] subst 1),
	(rtac sym 1),
	(rtac (chain_UU_I RS spec) 1),
	(atac 1),
	(atac 1),
	(rtac Istrictify1 1),
	(rtac (Istrictify2 RS ssubst) 1),
	(atac 1),
	(res_inst_tac [("s","lub(range(%i. f[Y(i)]))")] trans 1),
	(rtac contlub_cfun_arg 1),
	(atac 1),
	(rtac lub_equal2 1),
	(rtac (chain_mono2 RS exE) 1),
	(atac 2),
	(rtac chain_UU_I_inverse2 1),
	(atac 1),
	(rtac exI 1),
	(strip_tac 1),
	(rtac (Istrictify2 RS sym) 1),
	(fast_tac HOL_cs 1),
	(rtac ch2ch_monofun 1),
	(rtac monofun_fapp2 1),
	(atac 1),
	(rtac ch2ch_monofun 1),
	(rtac monofun_Istrictify2 1),
	(atac 1)
	]);


val contX_Istrictify1 = (contlub_Istrictify1 RS 
	(monofun_Istrictify1 RS monocontlub2contX)); 

val contX_Istrictify2 = (contlub_Istrictify2 RS 
	(monofun_Istrictify2 RS monocontlub2contX)); 


qed_goalw "strictify1" Cfun3.thy [strictify_def]
	"strictify[f][UU]=UU"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tac 1),
	(rtac contX_Istrictify2 1),
	(rtac contX2contX_CF1L 1),
	(rtac contX_Istrictify1 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Istrictify2 1),
	(rtac Istrictify1 1)
	]);

qed_goalw "strictify2" Cfun3.thy [strictify_def]
	"~x=UU ==> strictify[f][x]=f[x]"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(contX_tac 1),
	(rtac contX_Istrictify2 1),
	(rtac contX2contX_CF1L 1),
	(rtac contX_Istrictify1 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Istrictify2 1),
	(rtac Istrictify2 1),
	(resolve_tac prems 1)
	]);


(* ------------------------------------------------------------------------ *)
(* Instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

val Cfun_rews  = [minimal,refl_less,beta_cfun,strict_fapp1,strictify1,
		strictify2];

(* ------------------------------------------------------------------------ *)
(* use contX_tac as autotac.                                                *)
(* ------------------------------------------------------------------------ *)

val Cfun_ss = HOL_ss 
	addsimps  Cfun_rews 
	setsolver 
	(fn thms => (resolve_tac (TrueI::refl::thms)) ORELSE' atac ORELSE'
		    (fn i => DEPTH_SOLVE_1 (contX_tac i))
	);
