(*  Title:      HOLCF/Ssum0.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Strict sum with typedef
*)

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Sssum                                         *)
(* ------------------------------------------------------------------------ *)

Goalw [Ssum_def] "Sinl_Rep(a):Ssum";
by (Blast_tac 1);
qed "SsumIl";

Goalw [Ssum_def] "Sinr_Rep(a):Ssum";
by (Blast_tac 1);
qed "SsumIr";

Goal "inj_on Abs_Ssum Ssum";
by (rtac inj_on_inverseI 1);
by (etac Abs_Ssum_inverse 1);
qed "inj_on_Abs_Ssum";

(* ------------------------------------------------------------------------ *)
(* Strictness of Sinr_Rep, Sinl_Rep and Isinl, Isinr                        *)
(* ------------------------------------------------------------------------ *)

Goalw [Sinr_Rep_def,Sinl_Rep_def]
 "Sinl_Rep(UU) = Sinr_Rep(UU)";
by (rtac ext 1);
by (rtac ext 1);
by (rtac ext 1);
by (fast_tac HOL_cs 1);
qed "strict_SinlSinr_Rep";

Goalw [Isinl_def,Isinr_def]
 "Isinl(UU) = Isinr(UU)";
by (rtac (strict_SinlSinr_Rep RS arg_cong) 1);
qed "strict_IsinlIsinr";


(* ------------------------------------------------------------------------ *)
(* distinctness of  Sinl_Rep, Sinr_Rep and Isinl, Isinr                     *)
(* ------------------------------------------------------------------------ *)

Goalw [Sinl_Rep_def,Sinr_Rep_def]
        "(Sinl_Rep(a) = Sinr_Rep(b)) ==> a=UU & b=UU";
by (blast_tac (claset() addSDs [fun_cong]) 1);
qed "noteq_SinlSinr_Rep";


Goalw [Isinl_def,Isinr_def]
        "Isinl(a)=Isinr(b) ==> a=UU & b=UU";
by (rtac noteq_SinlSinr_Rep 1);
by (etac (inj_on_Abs_Ssum  RS inj_onD) 1);
by (rtac SsumIl 1);
by (rtac SsumIr 1);
qed "noteq_IsinlIsinr";



(* ------------------------------------------------------------------------ *)
(* injectivity of Sinl_Rep, Sinr_Rep and Isinl, Isinr                       *)
(* ------------------------------------------------------------------------ *)

Goalw [Sinl_Rep_def] "(Sinl_Rep(a) = Sinl_Rep(UU)) ==> a=UU";
by (blast_tac (claset() addSDs [fun_cong]) 1);
qed "inject_Sinl_Rep1";

Goalw [Sinr_Rep_def] "(Sinr_Rep(b) = Sinr_Rep(UU)) ==> b=UU";
by (blast_tac (claset() addSDs [fun_cong]) 1);
qed "inject_Sinr_Rep1";

Goalw [Sinl_Rep_def]
"[| a1~=UU ; a2~=UU ; Sinl_Rep(a1)=Sinl_Rep(a2) |] ==> a1=a2";
by (blast_tac (claset() addSDs [fun_cong]) 1);
qed "inject_Sinl_Rep2";

Goalw [Sinr_Rep_def]
"[|b1~=UU ; b2~=UU ; Sinr_Rep(b1)=Sinr_Rep(b2) |] ==> b1=b2";
by (blast_tac (claset() addSDs [fun_cong]) 1);
qed "inject_Sinr_Rep2";

Goal "Sinl_Rep(a1)=Sinl_Rep(a2) ==> a1=a2";
by (case_tac "a1=UU" 1);
by (hyp_subst_tac 1);
by (rtac (inject_Sinl_Rep1 RS sym) 1);
by (etac sym 1);
by (case_tac "a2=UU" 1);
by (hyp_subst_tac 1);
by (etac inject_Sinl_Rep1 1);
by (etac inject_Sinl_Rep2 1);
by (atac 1);
by (atac 1);
qed "inject_Sinl_Rep";

Goal "Sinr_Rep(b1)=Sinr_Rep(b2) ==> b1=b2";
by (case_tac "b1=UU" 1);
by (hyp_subst_tac 1);
by (rtac (inject_Sinr_Rep1 RS sym) 1);
by (etac sym 1);
by (case_tac "b2=UU" 1);
by (hyp_subst_tac 1);
by (etac inject_Sinr_Rep1 1);
by (etac inject_Sinr_Rep2 1);
by (atac 1);
by (atac 1);
qed "inject_Sinr_Rep";

Goalw [Isinl_def] "Isinl(a1)=Isinl(a2)==> a1=a2";
by (rtac inject_Sinl_Rep 1);
by (etac (inj_on_Abs_Ssum  RS inj_onD) 1);
by (rtac SsumIl 1);
by (rtac SsumIl 1);
qed "inject_Isinl";

Goalw [Isinr_def] "Isinr(b1)=Isinr(b2) ==> b1=b2";
by (rtac inject_Sinr_Rep 1);
by (etac (inj_on_Abs_Ssum  RS inj_onD) 1);
by (rtac SsumIr 1);
by (rtac SsumIr 1);
qed "inject_Isinr";

AddSDs [inject_Isinl, inject_Isinr];

Goal "a1~=a2 ==> Isinl(a1) ~= Isinl(a2)";
by (Blast_tac 1);
qed "inject_Isinl_rev";

Goal "b1~=b2 ==> Isinr(b1) ~= Isinr(b2)";
by (Blast_tac 1);
qed "inject_Isinr_rev";

(* ------------------------------------------------------------------------ *)
(* Exhaustion of the strict sum ++                                          *)
(* choice of the bottom representation is arbitrary                         *)
(* ------------------------------------------------------------------------ *)

Goalw [Isinl_def,Isinr_def]
        "z=Isinl(UU) | (? a. z=Isinl(a) & a~=UU) | (? b. z=Isinr(b) & b~=UU)";
by (rtac (rewrite_rule [Ssum_def] Rep_Ssum RS CollectE) 1);
by (etac disjE 1);
by (etac exE 1);
by (case_tac "z= Abs_Ssum(Sinl_Rep(UU))" 1);
by (etac disjI1 1);
by (rtac disjI2 1);
by (rtac disjI1 1);
by (rtac exI 1);
by (rtac conjI 1);
by (rtac (Rep_Ssum_inverse RS sym RS trans) 1);
by (etac arg_cong 1);
by (res_inst_tac [("Q","Sinl_Rep(a)=Sinl_Rep(UU)")] contrapos_nn 1);
by (etac arg_cong 2);
by (etac contrapos_nn 1);
by (rtac (Rep_Ssum_inverse RS sym RS trans) 1);
by (rtac trans 1);
by (etac arg_cong 1);
by (etac arg_cong 1);
by (etac exE 1);
by (case_tac "z= Abs_Ssum(Sinl_Rep(UU))" 1);
by (etac disjI1 1);
by (rtac disjI2 1);
by (rtac disjI2 1);
by (rtac exI 1);
by (rtac conjI 1);
by (rtac (Rep_Ssum_inverse RS sym RS trans) 1);
by (etac arg_cong 1);
by (res_inst_tac [("Q","Sinr_Rep(b)=Sinl_Rep(UU)")] contrapos_nn 1);
by (hyp_subst_tac 2);
by (rtac (strict_SinlSinr_Rep RS sym) 2);
by (etac contrapos_nn 1);
by (rtac (Rep_Ssum_inverse RS sym RS trans) 1);
by (rtac trans 1);
by (etac arg_cong 1);
by (etac arg_cong 1);
qed "Exh_Ssum";

(* ------------------------------------------------------------------------ *)
(* elimination rules for the strict sum ++                                  *)
(* ------------------------------------------------------------------------ *)

val prems = Goal
        "[|p=Isinl(UU) ==> Q ;\
\       !!x.[|p=Isinl(x); x~=UU |] ==> Q;\
\       !!y.[|p=Isinr(y); y~=UU |] ==> Q|] ==> Q";
by (rtac (Exh_Ssum RS disjE) 1);
by (etac disjE 2);
by (eresolve_tac prems 1);
by (etac exE 1);
by (etac conjE 1);
by (eresolve_tac prems 1);
by (atac 1);
by (etac exE 1);
by (etac conjE 1);
by (eresolve_tac prems 1);
by (atac 1);
qed "IssumE";

val prems = Goal
"[| !!x. [| p = Isinl(x) |] ==> Q;   !!y. [| p = Isinr(y) |] ==> Q |] ==>Q";
by (rtac IssumE 1);
by (eresolve_tac prems 1);
by (eresolve_tac prems 1);
by (eresolve_tac prems 1);
qed "IssumE2";




(* ------------------------------------------------------------------------ *)
(* rewrites for Iwhen                                                       *)
(* ------------------------------------------------------------------------ *)

Goalw [Iwhen_def]
        "Iwhen f g (Isinl UU) = UU";
by (rtac some_equality 1);
by (rtac conjI 1);
by (fast_tac HOL_cs  1);
by (rtac conjI 1);
by (strip_tac 1);
by (res_inst_tac [("P","a=UU")] notE 1);
by (fast_tac HOL_cs  1);
by (rtac inject_Isinl 1);
by (rtac sym 1);
by (fast_tac HOL_cs  1);
by (strip_tac 1);
by (res_inst_tac [("P","b=UU")] notE 1);
by (fast_tac HOL_cs  1);
by (rtac inject_Isinr 1);
by (rtac sym 1);
by (rtac (strict_IsinlIsinr RS subst) 1);
by (fast_tac HOL_cs  1);
by (fast_tac HOL_cs  1);
qed "Iwhen1";


Goalw [Iwhen_def]
        "x~=UU ==> Iwhen f g (Isinl x) = f`x";
by (rtac some_equality 1);
by (fast_tac HOL_cs  2);
by (rtac conjI 1);
by (strip_tac 1);
by (res_inst_tac [("P","x=UU")] notE 1);
by (atac 1);
by (rtac inject_Isinl 1);
by (atac 1);
by (rtac conjI 1);
by (strip_tac 1);
by (rtac cfun_arg_cong 1);
by (rtac inject_Isinl 1);
by (fast_tac HOL_cs  1);
by (strip_tac 1);
by (res_inst_tac [("P","Isinl(x) = Isinr(b)")] notE 1);
by (fast_tac HOL_cs  2);
by (rtac contrapos_nn 1);
by (etac noteq_IsinlIsinr 2);
by (fast_tac HOL_cs  1);
qed "Iwhen2";

Goalw [Iwhen_def]
        "y~=UU ==> Iwhen f g (Isinr y) = g`y";
by (rtac some_equality 1);
by (fast_tac HOL_cs  2);
by (rtac conjI 1);
by (strip_tac 1);
by (res_inst_tac [("P","y=UU")] notE 1);
by (atac 1);
by (rtac inject_Isinr 1);
by (rtac (strict_IsinlIsinr RS subst) 1);
by (atac 1);
by (rtac conjI 1);
by (strip_tac 1);
by (res_inst_tac [("P","Isinr(y) = Isinl(a)")] notE 1);
by (fast_tac HOL_cs  2);
by (rtac contrapos_nn 1);
by (etac (sym RS noteq_IsinlIsinr) 2);
by (fast_tac HOL_cs  1);
by (strip_tac 1);
by (rtac cfun_arg_cong 1);
by (rtac inject_Isinr 1);
by (fast_tac HOL_cs  1);
qed "Iwhen3";

(* ------------------------------------------------------------------------ *)
(* instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

val Ssum0_ss = (simpset_of Cfun3.thy) delsimps [range_composition] addsimps 
                [(strict_IsinlIsinr RS sym),Iwhen1,Iwhen2,Iwhen3];

Addsimps [strict_IsinlIsinr RS sym, Iwhen1, Iwhen2, Iwhen3];
