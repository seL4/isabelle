(*  Title: 	HOLCF/cfun1.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for cfun1.thy 
*)

open Cfun1;

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Cfun                                          *)
(* ------------------------------------------------------------------------ *)

val CfunI = prove_goalw Cfun1.thy [Cfun_def] "(% x.x):Cfun"
 (fn prems =>
	[
	(rtac (mem_Collect_eq RS ssubst) 1),
	(rtac contX_id 1)
	]);


(* ------------------------------------------------------------------------ *)
(* less_cfun is a partial order on type 'a -> 'b                            *)
(* ------------------------------------------------------------------------ *)

val refl_less_cfun = prove_goalw Cfun1.thy [less_cfun_def] "less_cfun(f,f)"
(fn prems =>
	[
	(rtac refl_less 1)
	]);

val antisym_less_cfun = prove_goalw Cfun1.thy [less_cfun_def] 
	"[|less_cfun(f1,f2); less_cfun(f2,f1)|] ==> f1 = f2"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac injD 1),
	(rtac antisym_less 2),
	(atac 3),
	(atac 2),
	(rtac inj_inverseI 1),
	(rtac Rep_Cfun_inverse 1)
	]);

val trans_less_cfun = prove_goalw Cfun1.thy [less_cfun_def] 
	"[|less_cfun(f1,f2); less_cfun(f2,f3)|] ==> less_cfun(f1,f3)"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac trans_less 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* lemmas about application of continuous functions                         *)
(* ------------------------------------------------------------------------ *)

val cfun_cong = prove_goal Cfun1.thy 
	 "[| f=g; x=y |] ==> f[x] = g[y]"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(fast_tac HOL_cs 1)
	]);

val cfun_fun_cong = prove_goal Cfun1.thy "f=g ==> f[x] = g[x]"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac cfun_cong 1),
	(rtac refl 1)
	]);

val cfun_arg_cong = prove_goal Cfun1.thy "x=y ==> f[x] = f[y]"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac cfun_cong 1),
	(rtac refl 1),
	(atac 1)
	]);


(* ------------------------------------------------------------------------ *)
(* additional lemma about the isomorphism between -> and Cfun               *)
(* ------------------------------------------------------------------------ *)

val Abs_Cfun_inverse2 = prove_goal Cfun1.thy "contX(f) ==> fapp(fabs(f)) = f"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac Abs_Cfun_inverse 1),
	(rewrite_goals_tac [Cfun_def]),
	(etac (mem_Collect_eq RS ssubst) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* simplification of application                                            *)
(* ------------------------------------------------------------------------ *)

val Cfunapp2 = prove_goal Cfun1.thy 
	"contX(f) ==> (fabs(f))[x] = f(x)"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac (Abs_Cfun_inverse2 RS fun_cong) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* beta - equality for continuous functions                                 *)
(* ------------------------------------------------------------------------ *)

val beta_cfun = prove_goal Cfun1.thy 
	"contX(c1) ==> (LAM x .c1(x))[u] = c1(u)"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac Cfunapp2 1),
	(atac 1)
	]);

