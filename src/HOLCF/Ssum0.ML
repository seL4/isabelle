(*  Title: 	HOLCF/ssum0.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for theory ssum0.thy 
*)

open Ssum0;

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Sssum                                         *)
(* ------------------------------------------------------------------------ *)

qed_goalw "SsumIl" Ssum0.thy [Ssum_def] "Sinl_Rep(a):Ssum"
 (fn prems =>
	[
	(rtac CollectI 1),
	(rtac disjI1 1),
	(rtac exI 1),
	(rtac refl 1)
	]);

qed_goalw "SsumIr" Ssum0.thy [Ssum_def] "Sinr_Rep(a):Ssum"
 (fn prems =>
	[
	(rtac CollectI 1),
	(rtac disjI2 1),
	(rtac exI 1),
	(rtac refl 1)
	]);

qed_goal "inj_onto_Abs_Ssum" Ssum0.thy "inj_onto Abs_Ssum Ssum"
(fn prems =>
	[
	(rtac inj_onto_inverseI 1),
	(etac Abs_Ssum_inverse 1)
	]);

(* ------------------------------------------------------------------------ *)
(* Strictness of Sinr_Rep, Sinl_Rep and Isinl, Isinr                        *)
(* ------------------------------------------------------------------------ *)

qed_goalw "strict_SinlSinr_Rep" Ssum0.thy [Sinr_Rep_def,Sinl_Rep_def]
 "Sinl_Rep(UU) = Sinr_Rep(UU)"
 (fn prems =>
	[
	(rtac ext 1),
	(rtac ext 1),
	(rtac ext 1),
	(fast_tac HOL_cs 1)
	]);

qed_goalw "strict_IsinlIsinr" Ssum0.thy [Isinl_def,Isinr_def]
 "Isinl(UU) = Isinr(UU)"
 (fn prems =>
	[
	(rtac (strict_SinlSinr_Rep RS arg_cong) 1)
	]);


(* ------------------------------------------------------------------------ *)
(* distinctness of  Sinl_Rep, Sinr_Rep and Isinl, Isinr                     *)
(* ------------------------------------------------------------------------ *)

qed_goalw "noteq_SinlSinr_Rep" Ssum0.thy [Sinl_Rep_def,Sinr_Rep_def]
	"(Sinl_Rep(a) = Sinr_Rep(b)) ==> a=UU & b=UU"
 (fn prems =>
	[
	(rtac conjI 1),
	(res_inst_tac [("Q","a=UU")] classical2 1),
	(atac 1),
	(rtac ((hd prems) RS fun_cong RS fun_cong RS fun_cong RS iffD2 
	RS mp RS conjunct1 RS sym) 1),
	(fast_tac HOL_cs 1),
	(atac 1),
	(res_inst_tac [("Q","b=UU")] classical2 1),
	(atac 1),
	(rtac ((hd prems) RS fun_cong RS fun_cong RS fun_cong RS iffD1 
	RS mp RS conjunct1 RS sym) 1),
	(fast_tac HOL_cs 1),
	(atac 1)
	]);


qed_goalw "noteq_IsinlIsinr" Ssum0.thy [Isinl_def,Isinr_def]
	"Isinl(a)=Isinr(b) ==> a=UU & b=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac noteq_SinlSinr_Rep 1),
	(etac (inj_onto_Abs_Ssum  RS inj_ontoD) 1),
	(rtac SsumIl 1),
	(rtac SsumIr 1)
	]);



(* ------------------------------------------------------------------------ *)
(* injectivity of Sinl_Rep, Sinr_Rep and Isinl, Isinr                       *)
(* ------------------------------------------------------------------------ *)

qed_goalw "inject_Sinl_Rep1" Ssum0.thy [Sinl_Rep_def]
 "(Sinl_Rep(a) = Sinl_Rep(UU)) ==> a=UU"
 (fn prems =>
	[
	(res_inst_tac [("Q","a=UU")] classical2 1),
	(atac 1),
	(rtac ((hd prems) RS fun_cong RS fun_cong RS fun_cong 
	RS iffD2 RS mp RS conjunct1 RS sym) 1),
	(fast_tac HOL_cs 1),
	(atac 1)
	]);

qed_goalw "inject_Sinr_Rep1" Ssum0.thy [Sinr_Rep_def]
 "(Sinr_Rep(b) = Sinr_Rep(UU)) ==> b=UU"
 (fn prems =>
	[
	(res_inst_tac [("Q","b=UU")] classical2 1),
	(atac 1),
	(rtac ((hd prems) RS fun_cong RS fun_cong RS fun_cong 
	RS iffD2 RS mp RS conjunct1 RS sym) 1),
	(fast_tac HOL_cs 1),
	(atac 1)
	]);

qed_goalw "inject_Sinl_Rep2" Ssum0.thy [Sinl_Rep_def]
"[| a1~=UU ; a2~=UU ; Sinl_Rep(a1)=Sinl_Rep(a2) |] ==> a1=a2"
 (fn prems =>
	[
	(rtac ((nth_elem (2,prems)) RS fun_cong  RS fun_cong RS fun_cong 
	RS iffD1 RS mp RS conjunct1) 1),
	(fast_tac HOL_cs 1),
	(resolve_tac prems 1)
	]);

qed_goalw "inject_Sinr_Rep2" Ssum0.thy [Sinr_Rep_def]
"[|b1~=UU ; b2~=UU ; Sinr_Rep(b1)=Sinr_Rep(b2) |] ==> b1=b2"
 (fn prems =>
	[
	(rtac ((nth_elem (2,prems)) RS fun_cong  RS fun_cong RS fun_cong 
	RS iffD1 RS mp RS conjunct1) 1),
	(fast_tac HOL_cs 1),
	(resolve_tac prems 1)
	]);

qed_goal "inject_Sinl_Rep" Ssum0.thy 
	"Sinl_Rep(a1)=Sinl_Rep(a2) ==> a1=a2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("Q","a1=UU")] classical2 1),
	(hyp_subst_tac 1),
	(rtac (inject_Sinl_Rep1 RS sym) 1),
	(etac sym 1),
	(res_inst_tac [("Q","a2=UU")] classical2 1),
	(hyp_subst_tac 1),
	(etac inject_Sinl_Rep1 1),
	(etac inject_Sinl_Rep2 1),
	(atac 1),
	(atac 1)
	]);

qed_goal "inject_Sinr_Rep" Ssum0.thy 
	"Sinr_Rep(b1)=Sinr_Rep(b2) ==> b1=b2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("Q","b1=UU")] classical2 1),
	(hyp_subst_tac 1),
	(rtac (inject_Sinr_Rep1 RS sym) 1),
	(etac sym 1),
	(res_inst_tac [("Q","b2=UU")] classical2 1),
	(hyp_subst_tac 1),
	(etac inject_Sinr_Rep1 1),
	(etac inject_Sinr_Rep2 1),
	(atac 1),
	(atac 1)
	]);

qed_goalw "inject_Isinl" Ssum0.thy [Isinl_def]
"Isinl(a1)=Isinl(a2)==> a1=a2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac inject_Sinl_Rep 1),
	(etac (inj_onto_Abs_Ssum  RS inj_ontoD) 1),
	(rtac SsumIl 1),
	(rtac SsumIl 1)
	]);

qed_goalw "inject_Isinr" Ssum0.thy [Isinr_def]
"Isinr(b1)=Isinr(b2) ==> b1=b2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac inject_Sinr_Rep 1),
	(etac (inj_onto_Abs_Ssum  RS inj_ontoD) 1),
	(rtac SsumIr 1),
	(rtac SsumIr 1)
	]);

qed_goal "inject_Isinl_rev" Ssum0.thy  
"a1~=a2 ==> Isinl(a1) ~= Isinl(a2)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac contrapos 1),
	(etac inject_Isinl 2),
	(atac 1)
	]);

qed_goal "inject_Isinr_rev" Ssum0.thy  
"b1~=b2 ==> Isinr(b1) ~= Isinr(b2)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac contrapos 1),
	(etac inject_Isinr 2),
	(atac 1)
	]);

(* ------------------------------------------------------------------------ *)
(* Exhaustion of the strict sum ++                                          *)
(* choice of the bottom representation is arbitrary                         *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Exh_Ssum" Ssum0.thy [Isinl_def,Isinr_def]
	"z=Isinl(UU) | (? a. z=Isinl(a) & a~=UU) | (? b. z=Isinr(b) & b~=UU)"
 (fn prems =>
	[
	(rtac (rewrite_rule [Ssum_def] Rep_Ssum RS CollectE) 1),
	(etac disjE 1),
	(etac exE 1),
	(res_inst_tac [("Q","z= Abs_Ssum(Sinl_Rep(UU))")] classical2 1),
	(etac disjI1 1),
	(rtac disjI2 1),
	(rtac disjI1 1),
	(rtac exI 1),
	(rtac conjI 1),
	(rtac (Rep_Ssum_inverse RS sym RS trans) 1),
	(etac arg_cong 1),
	(res_inst_tac [("Q","Sinl_Rep(a)=Sinl_Rep(UU)")] contrapos 1),
	(etac arg_cong 2),
	(etac contrapos 1),
	(rtac (Rep_Ssum_inverse RS sym RS trans) 1),
	(rtac trans 1),
	(etac arg_cong 1),
	(etac arg_cong 1),
	(etac exE 1),
	(res_inst_tac [("Q","z= Abs_Ssum(Sinl_Rep(UU))")] classical2 1),
	(etac disjI1 1),
	(rtac disjI2 1),
	(rtac disjI2 1),
	(rtac exI 1),
	(rtac conjI 1),
	(rtac (Rep_Ssum_inverse RS sym RS trans) 1),
	(etac arg_cong 1),
	(res_inst_tac [("Q","Sinr_Rep(b)=Sinl_Rep(UU)")] contrapos 1),
	(hyp_subst_tac 2),
	(rtac (strict_SinlSinr_Rep RS sym) 2),
	(etac contrapos 1),
	(rtac (Rep_Ssum_inverse RS sym RS trans) 1),
	(rtac trans 1),
	(etac arg_cong 1),
	(etac arg_cong 1)
	]);

(* ------------------------------------------------------------------------ *)
(* elimination rules for the strict sum ++                                  *)
(* ------------------------------------------------------------------------ *)

qed_goal "IssumE" Ssum0.thy
	"[|p=Isinl(UU) ==> Q ;\
\	!!x.[|p=Isinl(x); x~=UU |] ==> Q;\
\	!!y.[|p=Isinr(y); y~=UU |] ==> Q|] ==> Q"
 (fn prems =>
	[
	(rtac (Exh_Ssum RS disjE) 1),
	(etac disjE 2),
	(eresolve_tac prems 1),
	(etac exE 1),
	(etac conjE 1),
	(eresolve_tac prems 1),
	(atac 1),
	(etac exE 1),
	(etac conjE 1),
	(eresolve_tac prems 1),
	(atac 1)
	]);

qed_goal "IssumE2" Ssum0.thy 
"[| !!x. [| p = Isinl(x) |] ==> Q;   !!y. [| p = Isinr(y) |] ==> Q |] ==>Q"
 (fn prems =>
	[
	(rtac IssumE 1),
	(eresolve_tac prems 1), 
	(eresolve_tac prems 1), 
	(eresolve_tac prems 1)
	]);




(* ------------------------------------------------------------------------ *)
(* rewrites for Iwhen                                                       *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Iwhen1" Ssum0.thy [Iwhen_def]
	"Iwhen f g (Isinl UU) = UU"
 (fn prems =>
	[
	(rtac  select_equality 1),
	(rtac conjI 1),
	(fast_tac HOL_cs  1),
	(rtac conjI 1),
	(strip_tac 1),
	(res_inst_tac [("P","a=UU")] notE 1),
	(fast_tac HOL_cs  1),
	(rtac inject_Isinl 1),
	(rtac sym 1),
	(fast_tac HOL_cs  1),
	(strip_tac 1),
	(res_inst_tac [("P","b=UU")] notE 1),
	(fast_tac HOL_cs  1),
	(rtac inject_Isinr 1),
	(rtac sym 1),
	(rtac (strict_IsinlIsinr RS subst) 1),
	(fast_tac HOL_cs  1),
	(fast_tac HOL_cs  1)
	]);


qed_goalw "Iwhen2" Ssum0.thy [Iwhen_def]
	"x~=UU ==> Iwhen f g (Isinl x) = f`x"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac  select_equality 1),
	(fast_tac HOL_cs  2),
	(rtac conjI 1),
	(strip_tac 1),
	(res_inst_tac [("P","x=UU")] notE 1),
	(atac 1),
	(rtac inject_Isinl 1),
	(atac 1),
	(rtac conjI 1),
	(strip_tac 1),
	(rtac cfun_arg_cong 1),
	(rtac inject_Isinl 1),
	(fast_tac HOL_cs  1),
	(strip_tac 1),
	(res_inst_tac [("P","Isinl(x) = Isinr(b)")] notE 1),
	(fast_tac HOL_cs  2),
	(rtac contrapos 1),
	(etac noteq_IsinlIsinr 2),
	(fast_tac HOL_cs  1)
	]);

qed_goalw "Iwhen3" Ssum0.thy [Iwhen_def]
	"y~=UU ==> Iwhen f g (Isinr y) = g`y"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac  select_equality 1),
	(fast_tac HOL_cs  2),
	(rtac conjI 1),
	(strip_tac 1),
	(res_inst_tac [("P","y=UU")] notE 1),
	(atac 1),
	(rtac inject_Isinr 1),
	(rtac (strict_IsinlIsinr RS subst) 1),
	(atac 1),
	(rtac conjI 1),
	(strip_tac 1),
	(res_inst_tac [("P","Isinr(y) = Isinl(a)")] notE 1),
	(fast_tac HOL_cs  2),
	(rtac contrapos 1),
	(etac (sym RS noteq_IsinlIsinr) 2),
	(fast_tac HOL_cs  1),
	(strip_tac 1),
	(rtac cfun_arg_cong 1),
	(rtac inject_Isinr 1),
	(fast_tac HOL_cs  1)
	]);

(* ------------------------------------------------------------------------ *)
(* instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

Addsimps [(strict_IsinlIsinr RS sym),Iwhen1,Iwhen2,Iwhen3];


