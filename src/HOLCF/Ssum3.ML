(*  Title:      HOLCF/ssum3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for ssum3.thy
*)

open Ssum3;

(* for compatibility with old HOLCF-Version *)
qed_goal "inst_ssum_pcpo" thy "UU = Isinl UU"
 (fn prems => 
        [
        (simp_tac (HOL_ss addsimps [UU_def,UU_ssum_def]) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* continuity for Isinl and Isinr                                           *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_Isinl" Ssum3.thy "contlub(Isinl)"
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
        (case_tac "lub(range(Y))=UU" 1),
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
        (case_tac "Y(k)=UU" 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 1)
        ]);

qed_goal "contlub_Isinr" Ssum3.thy "contlub(Isinr)"
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
        (case_tac "lub(range(Y))=UU" 1),
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
        (case_tac "Y(k)=UU" 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 1)
        ]);

qed_goal "cont_Isinl" Ssum3.thy "cont(Isinl)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Isinl 1),
        (rtac contlub_Isinl 1)
        ]);

qed_goal "cont_Isinr" Ssum3.thy "cont(Isinr)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Isinr 1),
        (rtac contlub_Isinr 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* continuity for Iwhen in the firts two arguments                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_Iwhen1" Ssum3.thy "contlub(Iwhen)"
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
        (asm_simp_tac Ssum0_ss 1),
        (rtac (lub_const RS thelubI RS sym) 1),
        (asm_simp_tac Ssum0_ss 1),
        (etac contlub_cfun_fun 1),
        (asm_simp_tac Ssum0_ss 1),
        (rtac (lub_const RS thelubI RS sym) 1)
        ]);

qed_goal "contlub_Iwhen2" Ssum3.thy "contlub(Iwhen(f))"
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
        (asm_simp_tac Ssum0_ss 1),
        (rtac (lub_const RS thelubI RS sym) 1),
        (asm_simp_tac Ssum0_ss 1),
        (rtac (lub_const RS thelubI RS sym) 1),
        (asm_simp_tac Ssum0_ss 1),
        (etac contlub_cfun_fun 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* continuity for Iwhen in its third argument                               *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* first 5 ugly lemmas                                                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "ssum_lemma9" Ssum3.thy 
"[| chain(Y); lub(range(Y)) = Isinl(x)|] ==> !i.? x. Y(i)=Isinl(x)"
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


qed_goal "ssum_lemma10" Ssum3.thy 
"[| chain(Y); lub(range(Y)) = Isinr(x)|] ==> !i.? x. Y(i)=Isinr(x)"
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

qed_goal "ssum_lemma11" Ssum3.thy 
"[| chain(Y); lub(range(Y)) = Isinl(UU) |] ==>\
\   Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac Ssum0_ss 1),
        (rtac (chain_UU_I_inverse RS sym) 1),
        (rtac allI 1),
        (res_inst_tac [("s","Isinl(UU)"),("t","Y(i)")] subst 1),
        (rtac (inst_ssum_pcpo RS subst) 1),
        (rtac (chain_UU_I RS spec RS sym) 1),
        (atac 1),
        (etac (inst_ssum_pcpo RS ssubst) 1),
        (asm_simp_tac Ssum0_ss 1)
        ]);

qed_goal "ssum_lemma12" Ssum3.thy 
"[| chain(Y); lub(range(Y)) = Isinl(x); x ~= UU |] ==>\
\   Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac Ssum0_ss 1),
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
        (stac inst_ssum_pcpo 1),
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
        (stac inst_ssum_pcpo 1),
        (res_inst_tac [("t","Y(i)")] ssubst 1),
        (atac 1),
        (fast_tac HOL_cs 1),
        (stac Iwhen2 1),
        (res_inst_tac [("Pa","Y(i)=UU")] swap 1),
        (fast_tac HOL_cs 1),
        (stac inst_ssum_pcpo 1),
        (res_inst_tac [("t","Y(i)")] ssubst 1),
        (atac 1),
        (fast_tac HOL_cs 1),
        (simp_tac (simpset_of Cfun3.thy) 1),
        (rtac (monofun_fapp2 RS ch2ch_monofun) 1),
        (etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
        (etac (monofun_Iwhen3 RS ch2ch_monofun) 1)
        ]);


qed_goal "ssum_lemma13" Ssum3.thy 
"[| chain(Y); lub(range(Y)) = Isinr(x); x ~= UU |] ==>\
\   Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac Ssum0_ss 1),
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
        (stac inst_ssum_pcpo 1),
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
        (stac inst_ssum_pcpo 1),
        (stac strict_IsinlIsinr 1),
        (res_inst_tac [("t","Y(i)")] ssubst 1),
        (atac 1),
        (fast_tac HOL_cs 1),
        (stac Iwhen3 1),
        (res_inst_tac [("Pa","Y(i)=UU")] swap 1),
        (fast_tac HOL_cs 1),
        (dtac notnotD 1),
        (stac inst_ssum_pcpo 1),
        (stac strict_IsinlIsinr 1),
        (res_inst_tac [("t","Y(i)")] ssubst 1),
        (atac 1),
        (fast_tac HOL_cs 1),
        (simp_tac (simpset_of Cfun3.thy) 1),
        (rtac (monofun_fapp2 RS ch2ch_monofun) 1),
        (etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
        (etac (monofun_Iwhen3 RS ch2ch_monofun) 1)
        ]);


qed_goal "contlub_Iwhen3" Ssum3.thy "contlub(Iwhen(f)(g))"
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

qed_goal "cont_Iwhen1" Ssum3.thy "cont(Iwhen)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Iwhen1 1),
        (rtac contlub_Iwhen1 1)
        ]);

qed_goal "cont_Iwhen2" Ssum3.thy "cont(Iwhen(f))"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Iwhen2 1),
        (rtac contlub_Iwhen2 1)
        ]);

qed_goal "cont_Iwhen3" Ssum3.thy "cont(Iwhen(f)(g))"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Iwhen3 1),
        (rtac contlub_Iwhen3 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* continuous versions of lemmas for 'a ++ 'b                               *)
(* ------------------------------------------------------------------------ *)

qed_goalw "strict_sinl" Ssum3.thy [sinl_def] "sinl`UU =UU"
 (fn prems =>
        [
        (simp_tac (Ssum0_ss addsimps [cont_Isinl]) 1),
        (rtac (inst_ssum_pcpo RS sym) 1)
        ]);

qed_goalw "strict_sinr" Ssum3.thy [sinr_def] "sinr`UU=UU"
 (fn prems =>
        [
        (simp_tac (Ssum0_ss addsimps [cont_Isinr]) 1),
        (rtac (inst_ssum_pcpo RS sym) 1)
        ]);

qed_goalw "noteq_sinlsinr" Ssum3.thy [sinl_def,sinr_def] 
        "sinl`a=sinr`b ==> a=UU & b=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac noteq_IsinlIsinr 1),
        (etac box_equals 1),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1)
        ]);

qed_goalw "inject_sinl" Ssum3.thy [sinl_def,sinr_def] 
        "sinl`a1=sinl`a2==> a1=a2"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac inject_Isinl 1),
        (etac box_equals 1),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1)
        ]);

qed_goalw "inject_sinr" Ssum3.thy [sinl_def,sinr_def] 
        "sinr`a1=sinr`a2==> a1=a2"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac inject_Isinr 1),
        (etac box_equals 1),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1)
        ]);


qed_goal "defined_sinl" Ssum3.thy  
        "x~=UU ==> sinl`x ~= UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac swap 1),
        (rtac inject_sinl 1),
        (stac strict_sinl 1),
        (etac notnotD 1)
        ]);

qed_goal "defined_sinr" Ssum3.thy  
        "x~=UU ==> sinr`x ~= UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac swap 1),
        (rtac inject_sinr 1),
        (stac strict_sinr 1),
        (etac notnotD 1)
        ]);

qed_goalw "Exh_Ssum1" Ssum3.thy [sinl_def,sinr_def] 
        "z=UU | (? a. z=sinl`a & a~=UU) | (? b. z=sinr`b & b~=UU)"
 (fn prems =>
        [
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1),
        (stac inst_ssum_pcpo 1),
        (rtac Exh_Ssum 1)
        ]);


qed_goalw "ssumE" Ssum3.thy [sinl_def,sinr_def] 
        "[|p=UU ==> Q ;\
\       !!x.[|p=sinl`x; x~=UU |] ==> Q;\
\       !!y.[|p=sinr`y; y~=UU |] ==> Q|] ==> Q"
 (fn prems =>
        [
        (rtac IssumE 1),
        (resolve_tac prems 1),
        (stac inst_ssum_pcpo 1),
        (atac 1),
        (resolve_tac prems 1),
        (atac 2),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1),
        (resolve_tac prems 1),
        (atac 2),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1)
        ]);


qed_goalw "ssumE2" Ssum3.thy [sinl_def,sinr_def] 
      "[|!!x.[|p=sinl`x|] ==> Q;\
\        !!y.[|p=sinr`y|] ==> Q|] ==> Q"
 (fn prems =>
        [
        (rtac IssumE2 1),
        (resolve_tac prems 1),
        (stac beta_cfun 1),
        (rtac cont_Isinl 1),
        (atac 1),
        (resolve_tac prems 1),
        (stac beta_cfun 1),
        (rtac cont_Isinr 1),
        (atac 1)
        ]);

qed_goalw "sswhen1" Ssum3.thy [sswhen_def,sinl_def,sinr_def] 
        "sswhen`f`g`UU = UU" (fn _ => let
val tac = (REPEAT (resolve_tac (cont_lemmas1 @ [cont_Iwhen1,cont_Iwhen2,
                cont_Iwhen3,cont2cont_CF1L]) 1)) in
	[
        (stac inst_ssum_pcpo 1),
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
	tac,
        (simp_tac Ssum0_ss  1)
        ] end);


val tac = (REPEAT (resolve_tac (cont_lemmas1 @ [cont_Iwhen1,cont_Iwhen2,
                cont_Iwhen3,cont_Isinl,cont_Isinr,cont2cont_CF1L]) 1));

qed_goalw "sswhen2" Ssum3.thy [sswhen_def,sinl_def,sinr_def] 
        "x~=UU==> sswhen`f`g`(sinl`x) = f`x" (fn prems => [
        (cut_facts_tac prems 1),
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
        tac,
        (asm_simp_tac Ssum0_ss  1)
        ]);

qed_goalw "sswhen3" Ssum3.thy [sswhen_def,sinl_def,sinr_def] 
        "x~=UU==> sswhen`f`g`(sinr`x) = g`x" (fn prems => [
        (cut_facts_tac prems 1),
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
        tac,
        (asm_simp_tac Ssum0_ss  1)
        ]);


qed_goalw "less_ssum4a" Ssum3.thy [sinl_def,sinr_def] 
        "(sinl`x << sinl`y) = (x << y)" (fn prems => [
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
	tac,
        (rtac less_ssum3a 1)
        ]);

qed_goalw "less_ssum4b" Ssum3.thy [sinl_def,sinr_def] 
        "(sinr`x << sinr`y) = (x << y)" (fn prems => [
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
        tac,
        (rtac less_ssum3b 1)
        ]);

qed_goalw "less_ssum4c" Ssum3.thy [sinl_def,sinr_def] 
        "(sinl`x << sinr`y) = (x = UU)" (fn prems =>
        [
        (stac beta_cfun 1),
        tac,
        (stac beta_cfun 1),
        tac,
        (rtac less_ssum3c 1)
        ]);

qed_goalw "less_ssum4d" Ssum3.thy [sinl_def,sinr_def] 
        "(sinr`x << sinl`y) = (x = UU)"
 (fn prems =>
        [
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
        tac,
        (rtac less_ssum3d 1)
        ]);

qed_goalw "ssum_chainE" Ssum3.thy [sinl_def,sinr_def] 
        "chain(Y) ==> (!i.? x.(Y i)=sinl`x)|(!i.? y.(Y i)=sinr`y)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1),
        (etac ssum_lemma4 1)
        ]);


qed_goalw "thelub_ssum2a" Ssum3.thy [sinl_def,sinr_def,sswhen_def] 
"[| chain(Y); !i.? x. Y(i) = sinl`x |] ==>\ 
\   lub(range(Y)) = sinl`(lub(range(%i. sswhen`(LAM x. x)`(LAM y. UU)`(Y i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
	tac,
        (stac (beta_cfun RS ext) 1),
	tac,
        (rtac thelub_ssum1a 1),
        (atac 1),
        (rtac allI 1),
        (etac allE 1),
        (etac exE 1),
        (rtac exI 1),
        (etac box_equals 1),
        (rtac refl 1),
        (asm_simp_tac (Ssum0_ss addsimps [cont_Isinl]) 1)
        ]);

qed_goalw "thelub_ssum2b" Ssum3.thy [sinl_def,sinr_def,sswhen_def] 
"[| chain(Y); !i.? x. Y(i) = sinr`x |] ==>\ 
\   lub(range(Y)) = sinr`(lub(range(%i. sswhen`(LAM y. UU)`(LAM x. x)`(Y i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
	tac,
        (stac (beta_cfun RS ext) 1),
	tac,
        (rtac thelub_ssum1b 1),
        (atac 1),
        (rtac allI 1),
        (etac allE 1),
        (etac exE 1),
        (rtac exI 1),
        (etac box_equals 1),
        (rtac refl 1),
        (asm_simp_tac (Ssum0_ss addsimps 
        [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2,
        cont_Iwhen3]) 1)
        ]);

qed_goalw "thelub_ssum2a_rev" Ssum3.thy [sinl_def,sinr_def] 
        "[| chain(Y); lub(range(Y)) = sinl`x|] ==> !i.? x. Y(i)=sinl`x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac (Ssum0_ss addsimps 
        [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2,
        cont_Iwhen3]) 1),
        (etac ssum_lemma9 1),
        (asm_simp_tac (Ssum0_ss addsimps 
        [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2,
        cont_Iwhen3]) 1)
        ]);

qed_goalw "thelub_ssum2b_rev" Ssum3.thy [sinl_def,sinr_def] 
        "[| chain(Y); lub(range(Y)) = sinr`x|] ==> !i.? x. Y(i)=sinr`x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac (Ssum0_ss addsimps 
        [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2,
        cont_Iwhen3]) 1),
        (etac ssum_lemma10 1),
        (asm_simp_tac (Ssum0_ss addsimps 
        [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2,
        cont_Iwhen3]) 1)
        ]);

qed_goal "thelub_ssum3" Ssum3.thy  
"chain(Y) ==>\ 
\   lub(range(Y)) = sinl`(lub(range(%i. sswhen`(LAM x. x)`(LAM y. UU)`(Y i))))\
\ | lub(range(Y)) = sinr`(lub(range(%i. sswhen`(LAM y. UU)`(LAM x. x)`(Y i))))"
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


qed_goal "sswhen4" Ssum3.thy  
        "sswhen`sinl`sinr`z=z"
 (fn prems =>
        [
        (res_inst_tac [("p","z")] ssumE 1),
        (asm_simp_tac ((simpset_of Cfun3.thy) addsimps [sswhen1,sswhen2,sswhen3]) 1),
        (asm_simp_tac ((simpset_of Cfun3.thy) addsimps [sswhen1,sswhen2,sswhen3]) 1),
        (asm_simp_tac ((simpset_of Cfun3.thy) addsimps [sswhen1,sswhen2,sswhen3]) 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* install simplifier for Ssum                                              *)
(* ------------------------------------------------------------------------ *)

val Ssum_rews = [strict_sinl,strict_sinr,defined_sinl,defined_sinr,
                sswhen1,sswhen2,sswhen3];

Addsimps [strict_sinl,strict_sinr,defined_sinl,defined_sinr,
                sswhen1,sswhen2,sswhen3];
