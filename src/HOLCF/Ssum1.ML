(*  Title: 	HOLCF/ssum1.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for theory ssum1.thy
*)

open Ssum1;

local 

fun eq_left s1 s2 = 
	(
	(res_inst_tac [("s",s1),("t",s2)] (inject_Isinl RS subst) 1)
	THEN 	(rtac trans 1)
	THEN 	(atac 2)
	THEN 	(etac sym 1));

fun eq_right s1 s2 = 
	(
	(res_inst_tac [("s",s1),("t",s2)] (inject_Isinr RS subst) 1)
	THEN 	(rtac trans 1)
	THEN 	(atac 2)
	THEN 	(etac sym 1));

fun UU_left s1 = 
	(
	(res_inst_tac [("t",s1)](noteq_IsinlIsinr RS conjunct1 RS ssubst)1)
	THEN (rtac trans 1)
	THEN (atac 2)
	THEN (etac sym 1));

fun UU_right s1 = 
	(
	(res_inst_tac [("t",s1)](noteq_IsinlIsinr RS conjunct2 RS ssubst)1)
	THEN (rtac trans 1)
	THEN (atac 2)
	THEN (etac sym 1))

in

val less_ssum1a = prove_goalw Ssum1.thy [less_ssum_def]
"[|s1=Isinl(x); s2=Isinl(y)|] ==> less_ssum(s1,s2) = (x << y)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac  select_equality 1),
	(dtac conjunct1 2),
	(dtac spec 2),
	(dtac spec 2),
	(etac mp 2),
	(fast_tac HOL_cs 2),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(eq_left "x" "u"),
	(eq_left "y" "xa"),
	(rtac refl 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_left "x"),
	(UU_right "v"),
	(simp_tac Cfun_ss 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(eq_left "x" "u"),
	(UU_left "y"),
	(rtac iffI 1),
	(etac UU_I 1),
	(res_inst_tac [("s","x"),("t","UU")] subst 1),
	(atac 1),
	(rtac refl_less 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_left "x"),
	(UU_right "v"),
	(simp_tac Cfun_ss 1)
	]);


val less_ssum1b = prove_goalw Ssum1.thy [less_ssum_def]
"[|s1=Isinr(x); s2=Isinr(y)|] ==> less_ssum(s1,s2) = (x << y)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac  select_equality 1),
	(dtac conjunct2 2),
	(dtac conjunct1 2),
	(dtac spec 2),
	(dtac spec 2),
	(etac mp 2),
	(fast_tac HOL_cs 2),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_right "x"),
	(UU_left "u"),
	(simp_tac Cfun_ss 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(eq_right "x" "v"),
	(eq_right "y" "ya"),
	(rtac refl 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_right "x"),
	(UU_left "u"),
	(simp_tac Cfun_ss 1),
	(strip_tac 1),
	(etac conjE 1),
	(eq_right "x" "v"),
	(UU_right "y"),
	(rtac iffI 1),
	(etac UU_I 1),
	(res_inst_tac [("s","UU"),("t","x")] subst 1),
	(etac sym 1),
	(rtac refl_less 1)
	]);


val less_ssum1c = prove_goalw Ssum1.thy [less_ssum_def]
"[|s1=Isinl(x); s2=Isinr(y)|] ==> less_ssum(s1,s2) = (x = UU)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac  select_equality 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(eq_left  "x" "u"),
	(UU_left "xa"),
	(rtac iffI 1),
	(res_inst_tac [("s","x"),("t","UU")] subst 1),
	(atac 1),
	(rtac refl_less 1),
	(etac UU_I 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_left "x"),
	(UU_right "v"),
	(simp_tac Cfun_ss 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(eq_left  "x" "u"),
	(rtac refl 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_left "x"),
	(UU_right "v"),
	(simp_tac Cfun_ss 1),
	(dtac conjunct2 1),
	(dtac conjunct2 1),
	(dtac conjunct1 1),
	(dtac spec 1),
	(dtac spec 1),
	(etac mp 1),
	(fast_tac HOL_cs 1)
	]);


val less_ssum1d = prove_goalw Ssum1.thy [less_ssum_def]
"[|s1=Isinr(x); s2=Isinl(y)|] ==> less_ssum(s1,s2) = (x = UU)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac  select_equality 1),
	(dtac conjunct2 2),
	(dtac conjunct2 2),
	(dtac conjunct2 2),
	(dtac spec 2),
	(dtac spec 2),
	(etac mp 2),
	(fast_tac HOL_cs 2),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_right "x"),
	(UU_left "u"),
	(simp_tac Cfun_ss 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_right "ya"),
	(eq_right "x" "v"),
	(rtac iffI 1),
	(etac UU_I 2),
	(res_inst_tac [("s","UU"),("t","x")] subst 1),
	(etac sym 1),
	(rtac refl_less 1),
	(rtac conjI 1),
	(strip_tac 1),
	(etac conjE 1),
	(UU_right "x"),
	(UU_left "u"),
	(simp_tac HOL_ss 1),
	(strip_tac 1),
	(etac conjE 1),
	(eq_right "x" "v"),
	(rtac refl 1)
	])
end;


(* ------------------------------------------------------------------------ *)
(* optimize lemmas about less_ssum                                          *)
(* ------------------------------------------------------------------------ *)

val less_ssum2a = prove_goal Ssum1.thy 
	"less_ssum(Isinl(x),Isinl(y)) = (x << y)"
 (fn prems =>
	[
	(rtac less_ssum1a 1),
	(rtac refl 1),
	(rtac refl 1)
	]);

val less_ssum2b = prove_goal Ssum1.thy 
	"less_ssum(Isinr(x),Isinr(y)) = (x << y)"
 (fn prems =>
	[
	(rtac less_ssum1b 1),
	(rtac refl 1),
	(rtac refl 1)
	]);

val less_ssum2c = prove_goal Ssum1.thy 
	"less_ssum(Isinl(x),Isinr(y)) = (x = UU)"
 (fn prems =>
	[
	(rtac less_ssum1c 1),
	(rtac refl 1),
	(rtac refl 1)
	]);

val less_ssum2d = prove_goal Ssum1.thy 
	"less_ssum(Isinr(x),Isinl(y)) = (x = UU)"
 (fn prems =>
	[
	(rtac less_ssum1d 1),
	(rtac refl 1),
	(rtac refl 1)
	]);


(* ------------------------------------------------------------------------ *)
(* less_ssum is a partial order on ++                                     *)
(* ------------------------------------------------------------------------ *)

val refl_less_ssum = prove_goal Ssum1.thy "less_ssum(p,p)"
 (fn prems =>
	[
	(res_inst_tac [("p","p")] IssumE2 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum2a RS iffD2) 1),
	(rtac refl_less 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum2b RS iffD2) 1),
	(rtac refl_less 1)
	]);

val antisym_less_ssum = prove_goal Ssum1.thy 
 "[|less_ssum(p1,p2);less_ssum(p2,p1)|] ==> p1=p2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","p1")] IssumE2 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p2")] IssumE2 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("f","Isinl")] arg_cong 1),
	(rtac antisym_less 1),
	(etac (less_ssum2a RS iffD1) 1),
	(etac (less_ssum2a RS iffD1) 1),
	(hyp_subst_tac 1),
	(etac (less_ssum2d RS iffD1 RS ssubst) 1),
	(etac (less_ssum2c RS iffD1 RS ssubst) 1),
	(rtac strict_IsinlIsinr 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p2")] IssumE2 1),
	(hyp_subst_tac 1),
	(etac (less_ssum2c RS iffD1 RS ssubst) 1),
	(etac (less_ssum2d RS iffD1 RS ssubst) 1),
	(rtac (strict_IsinlIsinr RS sym) 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("f","Isinr")] arg_cong 1),
	(rtac antisym_less 1),
	(etac (less_ssum2b RS iffD1) 1),
	(etac (less_ssum2b RS iffD1) 1)
	]);

val trans_less_ssum = prove_goal Ssum1.thy 
 "[|less_ssum(p1,p2);less_ssum(p2,p3)|] ==> less_ssum(p1,p3)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","p1")] IssumE2 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p3")] IssumE2 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum2a RS iffD2) 1),
	(res_inst_tac [("p","p2")] IssumE2 1),
	(hyp_subst_tac 1),
	(rtac trans_less 1),
	(etac (less_ssum2a RS iffD1) 1),
	(etac (less_ssum2a RS iffD1) 1),
	(hyp_subst_tac 1),
	(etac (less_ssum2c RS iffD1 RS ssubst) 1),
	(rtac minimal 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum2c RS iffD2) 1),
	(res_inst_tac [("p","p2")] IssumE2 1),
	(hyp_subst_tac 1),
	(rtac UU_I 1),
	(rtac trans_less 1),
	(etac (less_ssum2a RS iffD1) 1),
	(rtac (antisym_less_inverse RS conjunct1) 1),
	(etac (less_ssum2c RS iffD1) 1),
	(hyp_subst_tac 1),
	(etac (less_ssum2c RS iffD1) 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","p3")] IssumE2 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum2d RS iffD2) 1),
	(res_inst_tac [("p","p2")] IssumE2 1),
	(hyp_subst_tac 1),
	(etac (less_ssum2d RS iffD1) 1),
	(hyp_subst_tac 1),
	(rtac UU_I 1),
	(rtac trans_less 1),
	(etac (less_ssum2b RS iffD1) 1),
	(rtac (antisym_less_inverse RS conjunct1) 1),
	(etac (less_ssum2d RS iffD1) 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum2b RS iffD2) 1),
	(res_inst_tac [("p","p2")] IssumE2 1),
	(hyp_subst_tac 1),
	(etac (less_ssum2d RS iffD1 RS ssubst) 1),
	(rtac minimal 1),
	(hyp_subst_tac 1),
	(rtac trans_less 1),
	(etac (less_ssum2b RS iffD1) 1),
	(etac (less_ssum2b RS iffD1) 1)
	]);



