(*  Title: 	HOLCF/ssum2.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for ssum2.thy
*)

open Ssum2;

(* ------------------------------------------------------------------------ *)
(* access to less_ssum in class po                                          *)
(* ------------------------------------------------------------------------ *)

val less_ssum3a = prove_goal Ssum2.thy 
	"(Isinl(x) << Isinl(y)) = (x << y)"
 (fn prems =>
	[
	(rtac (inst_ssum_po RS ssubst) 1),
	(rtac less_ssum2a 1)
	]);

val less_ssum3b = prove_goal Ssum2.thy 
	"(Isinr(x) << Isinr(y)) = (x << y)"
 (fn prems =>
	[
	(rtac (inst_ssum_po RS ssubst) 1),
	(rtac less_ssum2b 1)
	]);

val less_ssum3c = prove_goal Ssum2.thy 
	"(Isinl(x) << Isinr(y)) = (x = UU)"
 (fn prems =>
	[
	(rtac (inst_ssum_po RS ssubst) 1),
	(rtac less_ssum2c 1)
	]);

val less_ssum3d = prove_goal Ssum2.thy 
	"(Isinr(x) << Isinl(y)) = (x = UU)"
 (fn prems =>
	[
	(rtac (inst_ssum_po RS ssubst) 1),
	(rtac less_ssum2d 1)
	]);


(* ------------------------------------------------------------------------ *)
(* type ssum ++ is pointed                                                  *)
(* ------------------------------------------------------------------------ *)

val minimal_ssum = prove_goal Ssum2.thy "Isinl(UU) << s"
 (fn prems =>
	[
	(res_inst_tac [("p","s")] IssumE2 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum3a RS iffD2) 1),
	(rtac minimal 1),
	(hyp_subst_tac 1),
	(rtac (strict_IsinlIsinr RS ssubst) 1),
	(rtac (less_ssum3b RS iffD2) 1),
	(rtac minimal 1)
	]);


(* ------------------------------------------------------------------------ *)
(* Isinl, Isinr are monotone                                                *)
(* ------------------------------------------------------------------------ *)

val monofun_Isinl = prove_goalw Ssum2.thy [monofun] "monofun(Isinl)"
 (fn prems =>
	[
	(strip_tac 1),
	(etac (less_ssum3a RS iffD2) 1)
	]);

val monofun_Isinr = prove_goalw Ssum2.thy [monofun] "monofun(Isinr)"
 (fn prems =>
	[
	(strip_tac 1),
	(etac (less_ssum3b RS iffD2) 1)
	]);


(* ------------------------------------------------------------------------ *)
(* Iwhen is monotone in all arguments                                       *)
(* ------------------------------------------------------------------------ *)


val monofun_Iwhen1 = prove_goalw Ssum2.thy [monofun] "monofun(Iwhen)"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac (less_fun RS iffD2) 1),
	(strip_tac 1),
	(rtac (less_fun RS iffD2) 1),
	(strip_tac 1),
	(res_inst_tac [("p","xb")] IssumE 1),
	(hyp_subst_tac 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 1),
	(etac monofun_cfun_fun 1),
	(asm_simp_tac Ssum_ss 1)
	]);

val monofun_Iwhen2 = prove_goalw Ssum2.thy [monofun] "monofun(Iwhen(f))"
 (fn prems =>
	[
	(strip_tac 1),
	(rtac (less_fun RS iffD2) 1),
	(strip_tac 1),
	(res_inst_tac [("p","xa")] IssumE 1),
	(hyp_subst_tac 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 1),
	(etac monofun_cfun_fun 1)
	]);

val monofun_Iwhen3 = prove_goalw Ssum2.thy [monofun] "monofun(Iwhen(f)(g))"
 (fn prems =>
	[
	(strip_tac 1),
	(res_inst_tac [("p","x")] IssumE 1),
	(hyp_subst_tac 1),
	(asm_simp_tac Ssum_ss 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","y")] IssumE 1),
	(hyp_subst_tac 1),
	(asm_simp_tac Ssum_ss 1),
	(res_inst_tac  [("P","xa=UU")] notE 1),
	(atac 1),
	(rtac UU_I 1),
	(rtac (less_ssum3a  RS iffD1) 1),
	(atac 1),
	(hyp_subst_tac 1),
	(asm_simp_tac Ssum_ss 1),
	(rtac monofun_cfun_arg 1),
	(etac (less_ssum3a  RS iffD1) 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("s","UU"),("t","xa")] subst 1),
	(etac (less_ssum3c  RS iffD1 RS sym) 1),
	(asm_simp_tac Ssum_ss 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("p","y")] IssumE 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("s","UU"),("t","ya")] subst 1),
	(etac (less_ssum3d  RS iffD1 RS sym) 1),
	(asm_simp_tac Ssum_ss 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("s","UU"),("t","ya")] subst 1),
	(etac (less_ssum3d  RS iffD1 RS sym) 1),
	(asm_simp_tac Ssum_ss 1),
	(hyp_subst_tac 1),
	(asm_simp_tac Ssum_ss 1),
	(rtac monofun_cfun_arg 1),
	(etac (less_ssum3b  RS iffD1) 1)
	]);




(* ------------------------------------------------------------------------ *)
(* some kind of exhaustion rules for chains in 'a ++ 'b                     *)
(* ------------------------------------------------------------------------ *)


val ssum_lemma1 = prove_goal Ssum2.thy 
"[|~(!i.? x.Y(i::nat)=Isinl(x))|] ==> (? i.! x.~Y(i)=Isinl(x))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(fast_tac HOL_cs 1)
	]);

val ssum_lemma2 = prove_goal Ssum2.thy 
"[|(? i.!x.~(Y::nat => 'a++'b)(i::nat)=Isinl(x::'a))|] ==>\
\   (? i y. (Y::nat => 'a++'b)(i::nat)=Isinr(y::'b) & ~y=UU)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(res_inst_tac [("p","Y(i)")] IssumE 1),
	(dtac spec 1),
	(contr_tac 1),
	(dtac spec 1),
	(contr_tac 1),
	(fast_tac HOL_cs 1)
	]);


val ssum_lemma3 = prove_goal Ssum2.thy 
"[|is_chain(Y);(? i x. Y(i)=Isinr(x) & ~x=UU)|] ==> (!i.? y.Y(i)=Isinr(y))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(etac exE 1),
	(rtac allI 1),
	(res_inst_tac [("p","Y(ia)")] IssumE 1),
	(rtac exI 1),
	(rtac trans 1),
	(rtac strict_IsinlIsinr 2),
	(atac 1),
	(etac exI 2),
	(etac conjE 1),
	(res_inst_tac [("m","i"),("n","ia")] nat_less_cases 1),
	(hyp_subst_tac 2),
	(etac exI 2),
	(res_inst_tac [("P","x=UU")] notE 1),
	(atac 1),
	(rtac (less_ssum3d RS iffD1) 1),
	(res_inst_tac [("s","Y(i)"),("t","Isinr(x)")] subst 1),
	(atac 1),
	(res_inst_tac [("s","Y(ia)"),("t","Isinl(xa)")] subst 1),
	(atac 1),
	(etac (chain_mono RS mp) 1),
	(atac 1),
	(res_inst_tac [("P","xa=UU")] notE 1),
	(atac 1),
	(rtac (less_ssum3c RS iffD1) 1),
	(res_inst_tac [("s","Y(i)"),("t","Isinr(x)")] subst 1),
	(atac 1),
	(res_inst_tac [("s","Y(ia)"),("t","Isinl(xa)")] subst 1),
	(atac 1),
	(etac (chain_mono RS mp) 1),
	(atac 1)
	]);

val ssum_lemma4 = prove_goal Ssum2.thy 
"is_chain(Y) ==> (!i.? x.Y(i)=Isinl(x))|(!i.? y.Y(i)=Isinr(y))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac classical2 1),
	(etac disjI1 1),
	(rtac disjI2 1),
	(etac ssum_lemma3 1),
	(rtac ssum_lemma2 1),
	(etac ssum_lemma1 1)
	]);


(* ------------------------------------------------------------------------ *)
(* restricted surjectivity of Isinl                                         *)
(* ------------------------------------------------------------------------ *)

val ssum_lemma5 = prove_goal Ssum2.thy 
"z=Isinl(x)==> Isinl((Iwhen (LAM x.x) (LAM y.UU))(z)) = z"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("Q","x=UU")] classical2 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 1)
	]);

(* ------------------------------------------------------------------------ *)
(* restricted surjectivity of Isinr                                         *)
(* ------------------------------------------------------------------------ *)

val ssum_lemma6 = prove_goal Ssum2.thy 
"z=Isinr(x)==> Isinr((Iwhen (LAM y.UU) (LAM x.x))(z)) = z"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(hyp_subst_tac 1),
	(res_inst_tac [("Q","x=UU")] classical2 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 1)
	]);

(* ------------------------------------------------------------------------ *)
(* technical lemmas                                                         *)
(* ------------------------------------------------------------------------ *)

val ssum_lemma7 = prove_goal Ssum2.thy 
"[|Isinl(x) << z; ~x=UU|] ==> ? y.z=Isinl(y) & ~y=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","z")] IssumE 1),
	(hyp_subst_tac 1),
	(etac notE 1),
	(rtac antisym_less 1),
	(etac (less_ssum3a RS iffD1) 1),
	(rtac minimal 1),
	(fast_tac HOL_cs 1),
	(hyp_subst_tac 1),
	(rtac notE 1),
	(etac (less_ssum3c RS iffD1) 2),
	(atac 1)
	]);

val ssum_lemma8 = prove_goal Ssum2.thy 
"[|Isinr(x) << z; ~x=UU|] ==> ? y.z=Isinr(y) & ~y=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(res_inst_tac [("p","z")] IssumE 1),
	(hyp_subst_tac 1),
	(etac notE 1),
	(etac (less_ssum3d RS iffD1) 1),
	(hyp_subst_tac 1),
	(rtac notE 1),
	(etac (less_ssum3d RS iffD1) 2),
	(atac 1),
	(fast_tac HOL_cs 1)
	]);

(* ------------------------------------------------------------------------ *)
(* the type 'a ++ 'b is a cpo in three steps                                *)
(* ------------------------------------------------------------------------ *)

val lub_ssum1a = prove_goal Ssum2.thy 
"[|is_chain(Y);(!i.? x.Y(i)=Isinl(x))|] ==>\
\ range(Y) <<|\
\ Isinl(lub(range(%i.(Iwhen (LAM x.x) (LAM y.UU))(Y(i)))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_lubI 1),
	(rtac conjI 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(etac allE 1),
	(etac exE 1),
	(res_inst_tac [("t","Y(i)")] (ssum_lemma5 RS subst) 1),
	(atac 1),
	(rtac (monofun_Isinl RS monofunE RS spec RS spec RS mp) 1),
	(rtac is_ub_thelub 1),
	(etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(strip_tac 1),
	(res_inst_tac [("p","u")] IssumE2 1),
	(res_inst_tac [("t","u")] (ssum_lemma5 RS subst) 1),
	(atac 1),
	(rtac (monofun_Isinl RS monofunE RS spec RS spec RS mp) 1),
	(rtac is_lub_thelub 1),
	(etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(etac (monofun_Iwhen3 RS ub2ub_monofun) 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum3c RS iffD2) 1),
	(rtac chain_UU_I_inverse 1),
	(rtac allI 1),
	(res_inst_tac [("p","Y(i)")] IssumE 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 2),
	(etac notE 1),
	(rtac (less_ssum3c RS iffD1) 1),
	(res_inst_tac [("t","Isinl(x)")] subst 1),
	(atac 1),
	(etac (ub_rangeE RS spec) 1)
	]);


val lub_ssum1b = prove_goal Ssum2.thy 
"[|is_chain(Y);(!i.? x.Y(i)=Isinr(x))|] ==>\
\ range(Y) <<|\
\ Isinr(lub(range(%i.(Iwhen (LAM y.UU) (LAM x.x))(Y(i)))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac is_lubI 1),
	(rtac conjI 1),
	(rtac ub_rangeI 1),
	(rtac allI 1),
	(etac allE 1),
	(etac exE 1),
	(res_inst_tac [("t","Y(i)")] (ssum_lemma6 RS subst) 1),
	(atac 1),
	(rtac (monofun_Isinr RS monofunE RS spec RS spec RS mp) 1),
	(rtac is_ub_thelub 1),
	(etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(strip_tac 1),
	(res_inst_tac [("p","u")] IssumE2 1),
	(hyp_subst_tac 1),
	(rtac (less_ssum3d RS iffD2) 1),
	(rtac chain_UU_I_inverse 1),
	(rtac allI 1),
	(res_inst_tac [("p","Y(i)")] IssumE 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 1),
	(etac notE 1),
	(rtac (less_ssum3d RS iffD1) 1),
	(res_inst_tac [("t","Isinr(y)")] subst 1),
	(atac 1),
	(etac (ub_rangeE RS spec) 1),
	(res_inst_tac [("t","u")] (ssum_lemma6 RS subst) 1),
	(atac 1),
	(rtac (monofun_Isinr RS monofunE RS spec RS spec RS mp) 1),
	(rtac is_lub_thelub 1),
	(etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(etac (monofun_Iwhen3 RS ub2ub_monofun) 1)
	]);


val thelub_ssum1a = lub_ssum1a RS thelubI;
(* [| is_chain(?Y1); ! i. ? x. ?Y1(i) = Isinl(x) |] ==>                     *)
(* lub(range(?Y1)) = Isinl(lub(range(%i. Iwhen(LAM x. x,LAM y. UU,?Y1(i)))))*)

val thelub_ssum1b = lub_ssum1b RS thelubI;
(* [| is_chain(?Y1); ! i. ? x. ?Y1(i) = Isinr(x) |] ==>                     *)
(* lub(range(?Y1)) = Isinr(lub(range(%i. Iwhen(LAM y. UU,LAM x. x,?Y1(i)))))*)

val cpo_ssum = prove_goal Ssum2.thy 
	"is_chain(Y::nat=>'a ++'b) ==> ? x.range(Y) <<|x"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (ssum_lemma4 RS disjE) 1),
	(atac 1),
	(rtac exI 1),
	(etac lub_ssum1a 1),
	(atac 1),
	(rtac exI 1),
	(etac lub_ssum1b 1),
	(atac 1)
	]);
