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

qed_goalw "CfunI" Cfun1.thy [Cfun_def] "(% x.x):Cfun"
 (fn prems =>
	[
	(rtac (mem_Collect_eq RS ssubst) 1),
	(rtac cont_id 1)
	]);


(* ------------------------------------------------------------------------ *)
(* less_cfun is a partial order on type 'a -> 'b                            *)
(* ------------------------------------------------------------------------ *)

qed_goalw "refl_less_cfun" Cfun1.thy [less_cfun_def] "less_cfun f f"
(fn prems =>
	[
	(rtac refl_less 1)
	]);

qed_goalw "antisym_less_cfun" Cfun1.thy [less_cfun_def] 
	"[|less_cfun f1 f2; less_cfun f2 f1|] ==> f1 = f2"
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

qed_goalw "trans_less_cfun" Cfun1.thy [less_cfun_def] 
	"[|less_cfun f1 f2; less_cfun f2 f3|] ==> less_cfun f1 f3"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac trans_less 1),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* lemmas about application of continuous functions                         *)
(* ------------------------------------------------------------------------ *)

qed_goal "cfun_cong" Cfun1.thy 
	 "[| f=g; x=y |] ==> f`x = g`y"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "cfun_fun_cong" Cfun1.thy "f=g ==> f`x = g`x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac cfun_cong 1),
	(rtac refl 1)
	]);

qed_goal "cfun_arg_cong" Cfun1.thy "x=y ==> f`x = f`y"
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

qed_goal "Abs_Cfun_inverse2" Cfun1.thy "cont(f) ==> fapp(fabs(f)) = f"
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

qed_goal "Cfunapp2" Cfun1.thy 
	"cont(f) ==> (fabs f)`x = f x"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac (Abs_Cfun_inverse2 RS fun_cong) 1)
	]);

(* ------------------------------------------------------------------------ *)
(* beta - equality for continuous functions                                 *)
(* ------------------------------------------------------------------------ *)

qed_goal "beta_cfun" Cfun1.thy 
	"cont(c1) ==> (LAM x .c1 x)`u = c1 u"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac Cfunapp2 1),
	(atac 1)
	]);




