(*  Title:      HOLCF/Cfun1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for Cfun1.thy 
*)

open Cfun1;

(* ------------------------------------------------------------------------ *)
(* derive old type definition rules for Abs_CFun & Rep_CFun                         *)
(* Rep_CFun and Abs_CFun should be replaced by Rep_Cfun anf Abs_Cfun in future      *)
(* ------------------------------------------------------------------------ *)
qed_goal "Rep_Cfun" thy "Rep_CFun fo : CFun"
(fn prems =>
        [
        (rtac Rep_CFun 1)
        ]);

qed_goal "Rep_Cfun_inverse" thy "Abs_CFun (Rep_CFun fo) = fo"
(fn prems =>
        [
        (rtac Rep_CFun_inverse 1)
        ]);

qed_goal "Abs_Cfun_inverse" thy "f:CFun==>Rep_CFun(Abs_CFun f)=f"
(fn prems =>
        [
	(cut_facts_tac prems 1),
        (etac Abs_CFun_inverse 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* less_cfun is a partial order on type 'a -> 'b                            *)
(* ------------------------------------------------------------------------ *)

qed_goalw "refl_less_cfun" thy [less_cfun_def] "(f::'a->'b) << f"
(fn prems =>
        [
        (rtac refl_less 1)
        ]);

qed_goalw "antisym_less_cfun" thy [less_cfun_def] 
        "[|(f1::'a->'b) << f2; f2 << f1|] ==> f1 = f2"
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

qed_goalw "trans_less_cfun" thy [less_cfun_def] 
        "[|(f1::'a->'b) << f2; f2 << f3|] ==> f1 << f3"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac trans_less 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* lemmas about application of continuous functions                         *)
(* ------------------------------------------------------------------------ *)

qed_goal "cfun_cong" thy 
         "[| f=g; x=y |] ==> f`x = g`y"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (fast_tac HOL_cs 1)
        ]);

qed_goal "cfun_fun_cong" thy "f=g ==> f`x = g`x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac cfun_cong 1),
        (rtac refl 1)
        ]);

qed_goal "cfun_arg_cong" thy "x=y ==> f`x = f`y"
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

qed_goal "Abs_Cfun_inverse2" thy "cont f ==> Rep_CFun (Abs_CFun f) = f"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac Abs_Cfun_inverse 1),
        (rewtac CFun_def),
        (etac (mem_Collect_eq RS ssubst) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* simplification of application                                            *)
(* ------------------------------------------------------------------------ *)

qed_goal "Cfunapp2" thy "cont f ==> (Abs_CFun f)`x = f x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac (Abs_Cfun_inverse2 RS fun_cong) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* beta - equality for continuous functions                                 *)
(* ------------------------------------------------------------------------ *)

qed_goal "beta_cfun" thy 
        "cont(c1) ==> (LAM x .c1 x)`u = c1 u"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac Cfunapp2 1),
        (atac 1)
        ]);
