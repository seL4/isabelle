(*  Title:      HOLCF/Cfun1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

The type ->  of continuous functions.
*)

(* ------------------------------------------------------------------------ *)
(* derive old type definition rules for Abs_CFun & Rep_CFun                         *)
(* Rep_CFun and Abs_CFun should be replaced by Rep_Cfun anf Abs_Cfun in future      *)
(* ------------------------------------------------------------------------ *)
val prems = goal thy "Rep_CFun fo : CFun";
by (rtac Rep_CFun 1);
qed "Rep_Cfun";

val prems = goal thy "Abs_CFun (Rep_CFun fo) = fo";
by (rtac Rep_CFun_inverse 1);
qed "Rep_Cfun_inverse";

val prems = goal thy "f:CFun==>Rep_CFun(Abs_CFun f)=f";
by (cut_facts_tac prems 1);
by (etac Abs_CFun_inverse 1);
qed "Abs_Cfun_inverse";

(* ------------------------------------------------------------------------ *)
(* less_cfun is a partial order on type 'a -> 'b                            *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [less_cfun_def] "(f::'a->'b) << f";
by (rtac refl_less 1);
qed "refl_less_cfun";

val prems = goalw thy [less_cfun_def] 
        "[|(f1::'a->'b) << f2; f2 << f1|] ==> f1 = f2";
by (cut_facts_tac prems 1);
by (rtac injD 1);
by (rtac antisym_less 2);
by (atac 3);
by (atac 2);
by (rtac inj_inverseI 1);
by (rtac Rep_Cfun_inverse 1);
qed "antisym_less_cfun";

val prems = goalw thy [less_cfun_def] 
        "[|(f1::'a->'b) << f2; f2 << f3|] ==> f1 << f3";
by (cut_facts_tac prems 1);
by (etac trans_less 1);
by (atac 1);
qed "trans_less_cfun";

(* ------------------------------------------------------------------------ *)
(* lemmas about application of continuous functions                         *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy 
         "[| f=g; x=y |] ==> f`x = g`y";
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
qed "cfun_cong";

val prems = goal thy "f=g ==> f`x = g`x";
by (cut_facts_tac prems 1);
by (etac cfun_cong 1);
by (rtac refl 1);
qed "cfun_fun_cong";

val prems = goal thy "x=y ==> f`x = f`y";
by (cut_facts_tac prems 1);
by (rtac cfun_cong 1);
by (rtac refl 1);
by (atac 1);
qed "cfun_arg_cong";


(* ------------------------------------------------------------------------ *)
(* additional lemma about the isomorphism between -> and Cfun               *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy "cont f ==> Rep_CFun (Abs_CFun f) = f";
by (cut_facts_tac prems 1);
by (rtac Abs_Cfun_inverse 1);
by (rewtac CFun_def);
by (etac (mem_Collect_eq RS ssubst) 1);
qed "Abs_Cfun_inverse2";

(* ------------------------------------------------------------------------ *)
(* simplification of application                                            *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy "cont f ==> (Abs_CFun f)`x = f x";
by (cut_facts_tac prems 1);
by (etac (Abs_Cfun_inverse2 RS fun_cong) 1);
qed "Cfunapp2";

(* ------------------------------------------------------------------------ *)
(* beta - equality for continuous functions                                 *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy 
        "cont(c1) ==> (LAM x .c1 x)`u = c1 u";
by (cut_facts_tac prems 1);
by (rtac Cfunapp2 1);
by (atac 1);
qed "beta_cfun";
