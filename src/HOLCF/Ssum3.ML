(*  Title: 	HOLCF/ssum3.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for ssum3.thy
*)

open Ssum3;

(* ------------------------------------------------------------------------ *)
(* continuity for Isinl and Isinr                                           *)
(* ------------------------------------------------------------------------ *)


val contlub_Isinl = prove_goal Ssum3.thy "contlub(Isinl)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_ssum1a RS sym) 2),
	(rtac allI 3),
	(rtac exI 3),
	(rtac refl 3),
	(etac (monofun_Isinl RS ch2ch_monofun) 2),
	(res_inst_tac [("Q","lub(range(Y))=UU")] classical2 1),
	(res_inst_tac [("s","UU"),("t","lub(range(Y))")] ssubst 1),
	(atac 1),
	(res_inst_tac [("f","Isinl")] arg_cong  1),
	(rtac (chain_UU_I_inverse RS sym) 1),
	(rtac allI 1),
	(res_inst_tac [("s","UU"),("t","Y(i)")] ssubst 1),
	(etac (chain_UU_I RS spec ) 1),
	(atac 1),
	(rtac Iwhen1 1),
	(res_inst_tac [("f","Isinl")] arg_cong  1),
	(rtac lub_equal 1),
	(atac 1),
	(rtac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(etac (monofun_Isinl RS ch2ch_monofun) 1),
	(rtac allI 1),
	(res_inst_tac [("Q","Y(k)=UU")] classical2 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 1)
	]);

val contlub_Isinr = prove_goal Ssum3.thy "contlub(Isinr)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_ssum1b RS sym) 2),
	(rtac allI 3),
	(rtac exI 3),
	(rtac refl 3),
	(etac (monofun_Isinr RS ch2ch_monofun) 2),
	(res_inst_tac [("Q","lub(range(Y))=UU")] classical2 1),
	(res_inst_tac [("s","UU"),("t","lub(range(Y))")] ssubst 1),
	(atac 1),
	((rtac arg_cong 1) THEN (rtac (chain_UU_I_inverse RS sym) 1)),
	(rtac allI 1),
	(res_inst_tac [("s","UU"),("t","Y(i)")] ssubst 1),
	(etac (chain_UU_I RS spec ) 1),
	(atac 1),
	(rtac (strict_IsinlIsinr RS subst) 1),
	(rtac Iwhen1 1),
	((rtac arg_cong 1) THEN (rtac lub_equal 1)),
	(atac 1),
	(rtac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(etac (monofun_Isinr RS ch2ch_monofun) 1),
	(rtac allI 1),
	(res_inst_tac [("Q","Y(k)=UU")] classical2 1),
	(asm_simp_tac Ssum_ss 1),
	(asm_simp_tac Ssum_ss 1)
	]);

val contX_Isinl = prove_goal Ssum3.thy "contX(Isinl)"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Isinl 1),
	(rtac contlub_Isinl 1)
	]);

val contX_Isinr = prove_goal Ssum3.thy "contX(Isinr)"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Isinr 1),
	(rtac contlub_Isinr 1)
	]);


(* ------------------------------------------------------------------------ *)
(* continuity for Iwhen in the firts two arguments                          *)
(* ------------------------------------------------------------------------ *)

val contlub_Iwhen1 = prove_goal Ssum3.thy "contlub(Iwhen)"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_fun RS sym) 2),
	(etac (monofun_Iwhen1 RS ch2ch_monofun) 2),
	(rtac (expand_fun_eq RS iffD2) 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_fun RS sym) 2),
	(rtac ch2ch_fun 2),
	(etac (monofun_Iwhen1 RS ch2ch_monofun) 2),
	(rtac (expand_fun_eq RS iffD2) 1),
	(strip_tac 1),
	(res_inst_tac [("p","xa")] IssumE 1),
	(asm_simp_tac Ssum_ss 1),
	(rtac (lub_const RS thelubI RS sym) 1),
	(asm_simp_tac Ssum_ss 1),
	(etac contlub_cfun_fun 1),
	(asm_simp_tac Ssum_ss 1),
	(rtac (lub_const RS thelubI RS sym) 1)
	]);

val contlub_Iwhen2 = prove_goal Ssum3.thy "contlub(Iwhen(f))"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(rtac trans 1),
	(rtac (thelub_fun RS sym) 2),
	(etac (monofun_Iwhen2 RS ch2ch_monofun) 2),
	(rtac (expand_fun_eq RS iffD2) 1),
	(strip_tac 1),
	(res_inst_tac [("p","x")] IssumE 1),
	(asm_simp_tac Ssum_ss 1),
	(rtac (lub_const RS thelubI RS sym) 1),
	(asm_simp_tac Ssum_ss 1),
	(rtac (lub_const RS thelubI RS sym) 1),
	(asm_simp_tac Ssum_ss 1),
	(etac contlub_cfun_fun 1)
	]);

(* ------------------------------------------------------------------------ *)
(* continuity for Iwhen in its third argument                               *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* first 5 ugly lemmas                                                      *)
(* ------------------------------------------------------------------------ *)

val ssum_lemma9 = prove_goal Ssum3.thy 
"[| is_chain(Y); lub(range(Y)) = Isinl(x)|] ==> !i.? x.Y(i)=Isinl(x)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(res_inst_tac [("p","Y(i)")] IssumE 1),
	(etac exI 1),
	(etac exI 1),
	(res_inst_tac [("P","y=UU")] notE 1),
	(atac 1),
	(rtac (less_ssum3d RS iffD1) 1),
	(etac subst 1),
	(etac subst 1),
	(etac is_ub_thelub 1)
	]);


val ssum_lemma10 = prove_goal Ssum3.thy 
"[| is_chain(Y); lub(range(Y)) = Isinr(x)|] ==> !i.? x.Y(i)=Isinr(x)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(res_inst_tac [("p","Y(i)")] IssumE 1),
	(rtac exI 1),
	(etac trans 1),
	(rtac strict_IsinlIsinr 1),
	(etac exI 2),
	(res_inst_tac [("P","xa=UU")] notE 1),
	(atac 1),
	(rtac (less_ssum3c RS iffD1) 1),
	(etac subst 1),
	(etac subst 1),
	(etac is_ub_thelub 1)
	]);

val ssum_lemma11 = prove_goal Ssum3.thy 
"[| is_chain(Y); lub(range(Y)) = Isinl(UU) |] ==>\
\   Iwhen(f,g,lub(range(Y))) = lub(range(%i. Iwhen(f,g,Y(i))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac Ssum_ss 1),
	(rtac (chain_UU_I_inverse RS sym) 1),
	(rtac allI 1),
	(res_inst_tac [("s","Isinl(UU)"),("t","Y(i)")] subst 1),
	(rtac (inst_ssum_pcpo RS subst) 1),
	(rtac (chain_UU_I RS spec RS sym) 1),
	(atac 1),
	(etac (inst_ssum_pcpo RS ssubst) 1),
	(asm_simp_tac Ssum_ss 1)
	]);

val ssum_lemma12 = prove_goal Ssum3.thy 
"[| is_chain(Y); lub(range(Y)) = Isinl(x); ~ x = UU |] ==>\
\   Iwhen(f,g,lub(range(Y))) = lub(range(%i. Iwhen(f,g,Y(i))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac Ssum_ss 1),
	(res_inst_tac [("t","x")] subst 1),
	(rtac inject_Isinl 1),
	(rtac trans 1),
	(atac 2),
	(rtac (thelub_ssum1a RS sym) 1),
	(atac 1),
	(etac ssum_lemma9 1),
	(atac 1),
	(rtac trans 1),
	(rtac contlub_cfun_arg 1),
	(rtac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(atac 1),
	(rtac lub_equal2 1),
	(rtac (chain_mono2 RS exE) 1),
	(atac 2),
	(rtac chain_UU_I_inverse2 1),
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(etac swap 1),
	(rtac inject_Isinl 1),
	(rtac trans 1),
	(etac sym 1),
	(etac notnotD 1),
	(rtac exI 1),
	(strip_tac 1),
	(rtac (ssum_lemma9 RS spec RS exE) 1),
	(atac 1),
	(atac 1),
	(res_inst_tac [("t","Y(i)")] ssubst 1),
	(atac 1),
	(rtac trans 1),
	(rtac cfun_arg_cong 1),
	(rtac Iwhen2 1),
	(res_inst_tac [("Pa","Y(i)=UU")] swap 1),
	(fast_tac HOL_cs 1),
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(res_inst_tac [("t","Y(i)")] ssubst 1),
	(atac 1),
	(fast_tac HOL_cs 1),
	(rtac (Iwhen2 RS ssubst) 1),
	(res_inst_tac [("Pa","Y(i)=UU")] swap 1),
	(fast_tac HOL_cs 1),
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(res_inst_tac [("t","Y(i)")] ssubst 1),
	(atac 1),
	(fast_tac HOL_cs 1),
	(simp_tac Cfun_ss 1),
	(rtac (monofun_fapp2 RS ch2ch_monofun) 1),
	(etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(etac (monofun_Iwhen3 RS ch2ch_monofun) 1)
	]);


val ssum_lemma13 = prove_goal Ssum3.thy 
"[| is_chain(Y); lub(range(Y)) = Isinr(x); ~ x = UU |] ==>\
\   Iwhen(f,g,lub(range(Y))) = lub(range(%i. Iwhen(f,g,Y(i))))"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac Ssum_ss 1),
	(res_inst_tac [("t","x")] subst 1),
	(rtac inject_Isinr 1),
	(rtac trans 1),
	(atac 2),
	(rtac (thelub_ssum1b RS sym) 1),
	(atac 1),
	(etac ssum_lemma10 1),
	(atac 1),
	(rtac trans 1),
	(rtac contlub_cfun_arg 1),
	(rtac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(atac 1),
	(rtac lub_equal2 1),
	(rtac (chain_mono2 RS exE) 1),
	(atac 2),
	(rtac chain_UU_I_inverse2 1),
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(etac swap 1),
	(rtac inject_Isinr 1),
	(rtac trans 1),
	(etac sym 1),
	(rtac (strict_IsinlIsinr RS subst) 1),
	(etac notnotD 1),
	(rtac exI 1),
	(strip_tac 1),
	(rtac (ssum_lemma10 RS spec RS exE) 1),
	(atac 1),
	(atac 1),
	(res_inst_tac [("t","Y(i)")] ssubst 1),
	(atac 1),
	(rtac trans 1),
	(rtac cfun_arg_cong 1),
	(rtac Iwhen3 1),
	(res_inst_tac [("Pa","Y(i)=UU")] swap 1),
	(fast_tac HOL_cs 1),
	(dtac notnotD 1),
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(rtac (strict_IsinlIsinr RS ssubst) 1),
	(res_inst_tac [("t","Y(i)")] ssubst 1),
	(atac 1),
	(fast_tac HOL_cs 1),
	(rtac (Iwhen3 RS ssubst) 1),
	(res_inst_tac [("Pa","Y(i)=UU")] swap 1),
	(fast_tac HOL_cs 1),
	(dtac notnotD 1),
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(rtac (strict_IsinlIsinr RS ssubst) 1),
	(res_inst_tac [("t","Y(i)")] ssubst 1),
	(atac 1),
	(fast_tac HOL_cs 1),
	(simp_tac Cfun_ss 1),
	(rtac (monofun_fapp2 RS ch2ch_monofun) 1),
	(etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
	(etac (monofun_Iwhen3 RS ch2ch_monofun) 1)
	]);


val contlub_Iwhen3 = prove_goal Ssum3.thy "contlub(Iwhen(f)(g))"
 (fn prems =>
	[
	(rtac contlubI 1),
	(strip_tac 1),
	(res_inst_tac [("p","lub(range(Y))")] IssumE 1),
	(etac ssum_lemma11 1),
	(atac 1),
	(etac ssum_lemma12 1),
	(atac 1),
	(atac 1),
	(etac ssum_lemma13 1),
	(atac 1),
	(atac 1)
	]);

val contX_Iwhen1 = prove_goal Ssum3.thy "contX(Iwhen)"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Iwhen1 1),
	(rtac contlub_Iwhen1 1)
	]);

val contX_Iwhen2 = prove_goal Ssum3.thy "contX(Iwhen(f))"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Iwhen2 1),
	(rtac contlub_Iwhen2 1)
	]);

val contX_Iwhen3 = prove_goal Ssum3.thy "contX(Iwhen(f)(g))"
 (fn prems =>
	[
	(rtac monocontlub2contX 1),
	(rtac monofun_Iwhen3 1),
	(rtac contlub_Iwhen3 1)
	]);

(* ------------------------------------------------------------------------ *)
(* continuous versions of lemmas for 'a ++ 'b                               *)
(* ------------------------------------------------------------------------ *)

val strict_sinl = prove_goalw Ssum3.thy [sinl_def] "sinl[UU]=UU"
 (fn prems =>
	[
	(simp_tac (Ssum_ss addsimps [contX_Isinl]) 1),
	(rtac (inst_ssum_pcpo RS sym) 1)
	]);

val strict_sinr = prove_goalw Ssum3.thy [sinr_def] "sinr[UU]=UU"
 (fn prems =>
	[
	(simp_tac (Ssum_ss addsimps [contX_Isinr]) 1),
	(rtac (inst_ssum_pcpo RS sym) 1)
	]);

val noteq_sinlsinr = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"sinl[a]=sinr[b] ==> a=UU & b=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac noteq_IsinlIsinr 1),
	(etac box_equals 1),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1)
	]);

val inject_sinl = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"sinl[a1]=sinl[a2]==> a1=a2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac inject_Isinl 1),
	(etac box_equals 1),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1)
	]);

val inject_sinr = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"sinr[a1]=sinr[a2]==> a1=a2"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac inject_Isinr 1),
	(etac box_equals 1),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1)
	]);


val defined_sinl = prove_goal Ssum3.thy  
	"~x=UU ==> ~sinl[x]=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac swap 1),
	(rtac inject_sinl 1),
	(rtac (strict_sinl RS ssubst) 1),
	(etac notnotD 1)
	]);

val defined_sinr = prove_goal Ssum3.thy  
	"~x=UU ==> ~sinr[x]=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac swap 1),
	(rtac inject_sinr 1),
	(rtac (strict_sinr RS ssubst) 1),
	(etac notnotD 1)
	]);

val Exh_Ssum1 = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"z=UU | (? a. z=sinl[a] & ~a=UU) | (? b. z=sinr[b] & ~b=UU)"
 (fn prems =>
	[
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1),
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(rtac Exh_Ssum 1)
	]);


val ssumE = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"[|p=UU ==> Q ;\
\	!!x.[|p=sinl[x]; ~x=UU |] ==> Q;\
\	!!y.[|p=sinr[y]; ~y=UU |] ==> Q|] ==> Q"
 (fn prems =>
	[
	(rtac IssumE 1),
	(resolve_tac prems 1),
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(atac 1),
	(resolve_tac prems 1),
	(atac 2),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1),
	(resolve_tac prems 1),
	(atac 2),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1)
	]);


val ssumE2 = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
      "[|!!x.[|p=sinl[x]|] ==> Q;\
\	!!y.[|p=sinr[y]|] ==> Q|] ==> Q"
 (fn prems =>
	[
	(rtac IssumE2 1),
	(resolve_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isinl 1),
	(atac 1),
	(resolve_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(rtac contX_Isinr 1),
	(atac 1)
	]);

val when1 = prove_goalw Ssum3.thy [when_def,sinl_def,sinr_def] 
	"when[f][g][UU] = UU"
 (fn prems =>
	[
	(rtac (inst_ssum_pcpo RS ssubst) 1),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX2contX_CF1L]) 1)),
	(simp_tac Ssum_ss  1)
	]);

val when2 = prove_goalw Ssum3.thy [when_def,sinl_def,sinr_def] 
	"~x=UU==>when[f][g][sinl[x]] = f[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(asm_simp_tac Ssum_ss  1)
	]);



val when3 = prove_goalw Ssum3.thy [when_def,sinl_def,sinr_def] 
	"~x=UU==>when[f][g][sinr[x]] = g[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(asm_simp_tac Ssum_ss  1)
	]);


val less_ssum4a = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"(sinl[x] << sinl[y]) = (x << y)"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac less_ssum3a 1)
	]);

val less_ssum4b = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"(sinr[x] << sinr[y]) = (x << y)"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac less_ssum3b 1)
	]);

val less_ssum4c = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"(sinl[x] << sinr[y]) = (x = UU)"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac less_ssum3c 1)
	]);

val less_ssum4d = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"(sinr[x] << sinl[y]) = (x = UU)"
 (fn prems =>
	[
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac less_ssum3d 1)
	]);

val ssum_chainE = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"is_chain(Y) ==> (!i.? x.Y(i)=sinl[x])|(!i.? y.Y(i)=sinr[y])"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinr,contX_Isinl]) 1),
	(etac ssum_lemma4 1)
	]);


val thelub_ssum2a = prove_goalw Ssum3.thy [sinl_def,sinr_def,when_def] 
"[| is_chain(Y); !i.? x. Y(i) = sinl[x] |] ==>\ 
\   lub(range(Y)) = sinl[lub(range(%i. when[LAM x. x][LAM y. UU][Y(i)]))]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ext RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac thelub_ssum1a 1),
	(atac 1),
	(rtac allI 1),
	(etac allE 1),
	(etac exE 1),
	(rtac exI 1),
	(etac box_equals 1),
	(rtac refl 1),
	(asm_simp_tac (Ssum_ss addsimps [contX_Isinl]) 1)
	]);

val thelub_ssum2b = prove_goalw Ssum3.thy [sinl_def,sinr_def,when_def] 
"[| is_chain(Y); !i.? x. Y(i) = sinr[x] |] ==>\ 
\   lub(range(Y)) = sinr[lub(range(%i. when[LAM y. UU][LAM x. x][Y(i)]))]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac (beta_cfun RS ext RS ssubst) 1),
	(REPEAT (resolve_tac (contX_lemmas @ [contX_Iwhen1,contX_Iwhen2,
		contX_Iwhen3,contX_Isinl,contX_Isinr,contX2contX_CF1L]) 1)),
	(rtac thelub_ssum1b 1),
	(atac 1),
	(rtac allI 1),
	(etac allE 1),
	(etac exE 1),
	(rtac exI 1),
	(etac box_equals 1),
	(rtac refl 1),
	(asm_simp_tac (Ssum_ss addsimps 
	[contX_Isinr,contX_Isinl,contX_Iwhen1,contX_Iwhen2,
	contX_Iwhen3]) 1)
	]);

val thelub_ssum2a_rev = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"[| is_chain(Y); lub(range(Y)) = sinl[x]|] ==> !i.? x.Y(i)=sinl[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (Ssum_ss addsimps 
	[contX_Isinr,contX_Isinl,contX_Iwhen1,contX_Iwhen2,
	contX_Iwhen3]) 1),
	(etac ssum_lemma9 1),
	(asm_simp_tac (Ssum_ss addsimps 
	[contX_Isinr,contX_Isinl,contX_Iwhen1,contX_Iwhen2,
	contX_Iwhen3]) 1)
	]);

val thelub_ssum2b_rev = prove_goalw Ssum3.thy [sinl_def,sinr_def] 
	"[| is_chain(Y); lub(range(Y)) = sinr[x]|] ==> !i.? x.Y(i)=sinr[x]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (Ssum_ss addsimps 
	[contX_Isinr,contX_Isinl,contX_Iwhen1,contX_Iwhen2,
	contX_Iwhen3]) 1),
	(etac ssum_lemma10 1),
	(asm_simp_tac (Ssum_ss addsimps 
	[contX_Isinr,contX_Isinl,contX_Iwhen1,contX_Iwhen2,
	contX_Iwhen3]) 1)
	]);

val thelub_ssum3 = prove_goal Ssum3.thy  
"is_chain(Y) ==>\ 
\   lub(range(Y)) = sinl[lub(range(%i. when[LAM x. x][LAM y. UU][Y(i)]))]\
\ | lub(range(Y)) = sinr[lub(range(%i. when[LAM y. UU][LAM x. x][Y(i)]))]"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (ssum_chainE RS disjE) 1),
	(atac 1),
	(rtac disjI1 1),
	(etac thelub_ssum2a 1),
	(atac 1),
	(rtac disjI2 1),
	(etac thelub_ssum2b 1),
	(atac 1)
	]);


val when4 = prove_goal Ssum3.thy  
	"when[sinl][sinr][z]=z"
 (fn prems =>
	[
	(res_inst_tac [("p","z")] ssumE 1),
	(asm_simp_tac (Cfun_ss addsimps [when1,when2,when3]) 1),
	(asm_simp_tac (Cfun_ss addsimps [when1,when2,when3]) 1),
	(asm_simp_tac (Cfun_ss addsimps [when1,when2,when3]) 1)
	]);


(* ------------------------------------------------------------------------ *)
(* install simplifier for Ssum                                              *)
(* ------------------------------------------------------------------------ *)

val Ssum_rews = [strict_sinl,strict_sinr,when1,when2,when3];
val Ssum_ss = Cfun_ss addsimps Ssum_rews;
