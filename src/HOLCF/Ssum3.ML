(*  Title:      HOLCF/Ssum3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  ++ for class pcpo
*)

(* for compatibility with old HOLCF-Version *)
Goal "UU = Isinl UU";
by (simp_tac (HOL_ss addsimps [UU_def,UU_ssum_def]) 1);
qed "inst_ssum_pcpo";

Addsimps [inst_ssum_pcpo RS sym];

(* ------------------------------------------------------------------------ *)
(* continuity for Isinl and Isinr                                           *)
(* ------------------------------------------------------------------------ *)

Goal "contlub(Isinl)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_ssum1a RS sym) 2);
by (rtac allI 3);
by (rtac exI 3);
by (rtac refl 3);
by (etac (monofun_Isinl RS ch2ch_monofun) 2);
by (case_tac "lub(range(Y))=UU" 1);
by (res_inst_tac [("s","UU"),("t","lub(range(Y))")] ssubst 1);
by (atac 1);
by (res_inst_tac [("f","Isinl")] arg_cong  1);
by (rtac (chain_UU_I_inverse RS sym) 1);
by (rtac allI 1);
by (res_inst_tac [("s","UU"),("t","Y(i)")] ssubst 1);
by (etac (chain_UU_I RS spec ) 1);
by (atac 1);
by (rtac Iwhen1 1);
by (res_inst_tac [("f","Isinl")] arg_cong  1);
by (rtac lub_equal 1);
by (atac 1);
by (rtac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (etac (monofun_Isinl RS ch2ch_monofun) 1);
by (rtac allI 1);
by (case_tac "Y(k)=UU" 1);
by (asm_simp_tac Ssum0_ss 1);
by (asm_simp_tac Ssum0_ss 1);
qed "contlub_Isinl";

Goal "contlub(Isinr)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_ssum1b RS sym) 2);
by (rtac allI 3);
by (rtac exI 3);
by (rtac refl 3);
by (etac (monofun_Isinr RS ch2ch_monofun) 2);
by (case_tac "lub(range(Y))=UU" 1);
by (res_inst_tac [("s","UU"),("t","lub(range(Y))")] ssubst 1);
by (atac 1);
by ((rtac arg_cong 1) THEN (rtac (chain_UU_I_inverse RS sym) 1));
by (rtac allI 1);
by (res_inst_tac [("s","UU"),("t","Y(i)")] ssubst 1);
by (etac (chain_UU_I RS spec ) 1);
by (atac 1);
by (rtac (strict_IsinlIsinr RS subst) 1);
by (rtac Iwhen1 1);
by ((rtac arg_cong 1) THEN (rtac lub_equal 1));
by (atac 1);
by (rtac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (etac (monofun_Isinr RS ch2ch_monofun) 1);
by (rtac allI 1);
by (case_tac "Y(k)=UU" 1);
by (asm_simp_tac Ssum0_ss 1);
by (asm_simp_tac Ssum0_ss 1);
qed "contlub_Isinr";

Goal "cont(Isinl)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Isinl 1);
by (rtac contlub_Isinl 1);
qed "cont_Isinl";

Goal "cont(Isinr)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Isinr 1);
by (rtac contlub_Isinr 1);
qed "cont_Isinr";

AddIffs [cont_Isinl, cont_Isinr];


(* ------------------------------------------------------------------------ *)
(* continuity for Iwhen in the firts two arguments                          *)
(* ------------------------------------------------------------------------ *)

Goal "contlub(Iwhen)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_fun RS sym) 2);
by (etac (monofun_Iwhen1 RS ch2ch_monofun) 2);
by (rtac (expand_fun_eq RS iffD2) 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_fun RS sym) 2);
by (rtac ch2ch_fun 2);
by (etac (monofun_Iwhen1 RS ch2ch_monofun) 2);
by (rtac (expand_fun_eq RS iffD2) 1);
by (strip_tac 1);
by (res_inst_tac [("p","xa")] IssumE 1);
by (asm_simp_tac Ssum0_ss 1);
by (rtac (lub_const RS thelubI RS sym) 1);
by (asm_simp_tac Ssum0_ss 1);
by (etac contlub_cfun_fun 1);
by (asm_simp_tac Ssum0_ss 1);
by (rtac (lub_const RS thelubI RS sym) 1);
qed "contlub_Iwhen1";

Goal "contlub(Iwhen(f))";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_fun RS sym) 2);
by (etac (monofun_Iwhen2 RS ch2ch_monofun) 2);
by (rtac (expand_fun_eq RS iffD2) 1);
by (strip_tac 1);
by (res_inst_tac [("p","x")] IssumE 1);
by (asm_simp_tac Ssum0_ss 1);
by (rtac (lub_const RS thelubI RS sym) 1);
by (asm_simp_tac Ssum0_ss 1);
by (rtac (lub_const RS thelubI RS sym) 1);
by (asm_simp_tac Ssum0_ss 1);
by (etac contlub_cfun_fun 1);
qed "contlub_Iwhen2";

(* ------------------------------------------------------------------------ *)
(* continuity for Iwhen in its third argument                               *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* first 5 ugly lemmas                                                      *)
(* ------------------------------------------------------------------------ *)

Goal "[| chain(Y); lub(range(Y)) = Isinl(x)|] ==> !i.? x. Y(i)=Isinl(x)";
by (strip_tac 1);
by (res_inst_tac [("p","Y(i)")] IssumE 1);
by (etac exI 1);
by (etac exI 1);
by (res_inst_tac [("P","y=UU")] notE 1);
by (atac 1);
by (rtac (less_ssum3d RS iffD1) 1);
by (etac subst 1);
by (etac subst 1);
by (etac is_ub_thelub 1);
qed "ssum_lemma9";


Goal "[| chain(Y); lub(range(Y)) = Isinr(x)|] ==> !i.? x. Y(i)=Isinr(x)";
by (strip_tac 1);
by (res_inst_tac [("p","Y(i)")] IssumE 1);
by (rtac exI 1);
by (etac trans 1);
by (rtac strict_IsinlIsinr 1);
by (etac exI 2);
by (res_inst_tac [("P","xa=UU")] notE 1);
by (atac 1);
by (rtac (less_ssum3c RS iffD1) 1);
by (etac subst 1);
by (etac subst 1);
by (etac is_ub_thelub 1);
qed "ssum_lemma10";

Goal "[| chain(Y); lub(range(Y)) = Isinl(UU) |] ==>\
\   Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))";
by (asm_simp_tac Ssum0_ss 1);
by (rtac (chain_UU_I_inverse RS sym) 1);
by (rtac allI 1);
by (res_inst_tac [("s","Isinl(UU)"),("t","Y(i)")] subst 1);
by (rtac (inst_ssum_pcpo RS subst) 1);
by (rtac (chain_UU_I RS spec RS sym) 1);
by (atac 1);
by (etac (inst_ssum_pcpo RS ssubst) 1);
by (asm_simp_tac Ssum0_ss 1);
qed "ssum_lemma11";

Goal "[| chain(Y); lub(range(Y)) = Isinl(x); x ~= UU |] ==>\
\   Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))";
by (asm_simp_tac Ssum0_ss 1);
by (res_inst_tac [("t","x")] subst 1);
by (rtac inject_Isinl 1);
by (rtac trans 1);
by (atac 2);
by (rtac (thelub_ssum1a RS sym) 1);
by (atac 1);
by (etac ssum_lemma9 1);
by (atac 1);
by (rtac trans 1);
by (rtac contlub_cfun_arg 1);
by (rtac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (atac 1);
by (rtac lub_equal2 1);
by (rtac (chain_mono2 RS exE) 1);
by (atac 2);
by (rtac chain_UU_I_inverse2 1);
by (stac inst_ssum_pcpo 1);
by (etac contrapos_np 1);
by (rtac inject_Isinl 1);
by (rtac trans 1);
by (etac sym 1);
by (etac notnotD 1);
by (rtac exI 1);
by (strip_tac 1);
by (rtac (ssum_lemma9 RS spec RS exE) 1);
by (atac 1);
by (atac 1);
by (res_inst_tac [("t","Y(i)")] ssubst 1);
by (atac 1);
by (rtac trans 1);
by (rtac cfun_arg_cong 1);
by (rtac Iwhen2 1);
by (Force_tac 1); 
by (res_inst_tac [("t","Y(i)")] ssubst 1);
by (atac 1);
by Auto_tac;  
by (stac Iwhen2 1);
by (Force_tac 1); 
by (simp_tac (simpset_of Cfun3.thy) 1);
by (rtac (monofun_Rep_CFun2 RS ch2ch_monofun) 1);
by (etac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (etac (monofun_Iwhen3 RS ch2ch_monofun) 1);
qed "ssum_lemma12";


Goal "[| chain(Y); lub(range(Y)) = Isinr(x); x ~= UU |] ==>\
\   Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))";
by (asm_simp_tac Ssum0_ss 1);
by (res_inst_tac [("t","x")] subst 1);
by (rtac inject_Isinr 1);
by (rtac trans 1);
by (atac 2);
by (rtac (thelub_ssum1b RS sym) 1);
by (atac 1);
by (etac ssum_lemma10 1);
by (atac 1);
by (rtac trans 1);
by (rtac contlub_cfun_arg 1);
by (rtac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (atac 1);
by (rtac lub_equal2 1);
by (rtac (chain_mono2 RS exE) 1);
by (atac 2);
by (rtac chain_UU_I_inverse2 1);
by (stac inst_ssum_pcpo 1);
by (etac contrapos_np 1);
by (rtac inject_Isinr 1);
by (rtac trans 1);
by (etac sym 1);
by (rtac (strict_IsinlIsinr RS subst) 1);
by (etac notnotD 1);
by (rtac exI 1);
by (strip_tac 1);
by (rtac (ssum_lemma10 RS spec RS exE) 1);
by (atac 1);
by (atac 1);
by (res_inst_tac [("t","Y(i)")] ssubst 1);
by (atac 1);
by (rtac trans 1);
by (rtac cfun_arg_cong 1);
by (rtac Iwhen3 1);
by (Force_tac 1); 
by (res_inst_tac [("t","Y(i)")] ssubst 1);
by (atac 1);
by (stac Iwhen3 1);
by (Force_tac 1); 
by (res_inst_tac [("t","Y(i)")] ssubst 1);
by (atac 1);
by (simp_tac (simpset_of Cfun3.thy) 1);
by (rtac (monofun_Rep_CFun2 RS ch2ch_monofun) 1);
by (etac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (etac (monofun_Iwhen3 RS ch2ch_monofun) 1);
qed "ssum_lemma13";


Goal "contlub(Iwhen(f)(g))";
by (rtac contlubI 1);
by (strip_tac 1);
by (res_inst_tac [("p","lub(range(Y))")] IssumE 1);
by (etac ssum_lemma11 1);
by (atac 1);
by (etac ssum_lemma12 1);
by (atac 1);
by (atac 1);
by (etac ssum_lemma13 1);
by (atac 1);
by (atac 1);
qed "contlub_Iwhen3";

Goal "cont(Iwhen)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Iwhen1 1);
by (rtac contlub_Iwhen1 1);
qed "cont_Iwhen1";

Goal "cont(Iwhen(f))";
by (rtac monocontlub2cont 1);
by (rtac monofun_Iwhen2 1);
by (rtac contlub_Iwhen2 1);
qed "cont_Iwhen2";

Goal "cont(Iwhen(f)(g))";
by (rtac monocontlub2cont 1);
by (rtac monofun_Iwhen3 1);
by (rtac contlub_Iwhen3 1);
qed "cont_Iwhen3";

(* ------------------------------------------------------------------------ *)
(* continuous versions of lemmas for 'a ++ 'b                               *)
(* ------------------------------------------------------------------------ *)

Goalw [sinl_def] "sinl$UU =UU";
by (simp_tac (Ssum0_ss addsimps [cont_Isinl]) 1);
by (rtac (inst_ssum_pcpo RS sym) 1);
qed "strict_sinl";
Addsimps [strict_sinl];

Goalw [sinr_def] "sinr$UU=UU";
by (simp_tac (Ssum0_ss addsimps [cont_Isinr]) 1);
by (rtac (inst_ssum_pcpo RS sym) 1);
qed "strict_sinr";
Addsimps [strict_sinr];

Goalw [sinl_def,sinr_def] 
        "sinl$a=sinr$b ==> a=UU & b=UU";
by (auto_tac (claset() addSDs [noteq_IsinlIsinr], simpset()));
qed "noteq_sinlsinr";

Goalw [sinl_def,sinr_def] 
        "sinl$a1=sinl$a2==> a1=a2";
by Auto_tac;
qed "inject_sinl";

Goalw [sinl_def,sinr_def] 
        "sinr$a1=sinr$a2==> a1=a2";
by Auto_tac;
qed "inject_sinr";

AddSDs [inject_sinl, inject_sinr];

Goal "x~=UU ==> sinl$x ~= UU";
by (etac contrapos_nn 1);
by (rtac inject_sinl 1);
by Auto_tac;
qed "defined_sinl";
Addsimps [defined_sinl];

Goal "x~=UU ==> sinr$x ~= UU";
by (etac contrapos_nn 1);
by (rtac inject_sinr 1);
by Auto_tac;
qed "defined_sinr";
Addsimps [defined_sinr];

Goalw [sinl_def,sinr_def] 
        "z=UU | (? a. z=sinl$a & a~=UU) | (? b. z=sinr$b & b~=UU)";
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1);
by (stac inst_ssum_pcpo 1);
by (rtac Exh_Ssum 1);
qed "Exh_Ssum1";


val [major,prem2,prem3] = Goalw [sinl_def,sinr_def] 
        "[|p=UU ==> Q ;\
\       !!x.[|p=sinl$x; x~=UU |] ==> Q;\
\       !!y.[|p=sinr$y; y~=UU |] ==> Q|] ==> Q";
by (rtac (major RS IssumE) 1);
by (stac inst_ssum_pcpo 1);
by (atac 1);
by (rtac prem2 1);
by (atac 2);
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1);
by (rtac prem3 1);
by (atac 2);
by (Asm_simp_tac 1);
qed "ssumE";


val [preml,premr] = Goalw [sinl_def,sinr_def] 
      "[|!!x.[|p=sinl$x|] ==> Q;\
\        !!y.[|p=sinr$y|] ==> Q|] ==> Q";
by (rtac IssumE2 1);
by (rtac preml 1);
by (rtac premr 2);
by Auto_tac;  
qed "ssumE2";

val tac = (REPEAT (resolve_tac (cont_lemmas1 @ [cont_Iwhen1,cont_Iwhen2,
                cont_Iwhen3,cont2cont_CF1L]) 1)); 

Goalw [sscase_def,sinl_def,sinr_def] 
        "sscase$f$g$UU = UU";
by (stac inst_ssum_pcpo 1);
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (simp_tac Ssum0_ss  1);
qed "sscase1";
Addsimps [sscase1];


val tac = (REPEAT (resolve_tac (cont_lemmas1 @ [cont_Iwhen1,cont_Iwhen2,
                cont_Iwhen3,cont_Isinl,cont_Isinr,cont2cont_CF1L]) 1));

Goalw [sscase_def,sinl_def,sinr_def] 
        "x~=UU==> sscase$f$g$(sinl$x) = f$x";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (asm_simp_tac Ssum0_ss  1);
qed "sscase2";
Addsimps [sscase2];

Goalw [sscase_def,sinl_def,sinr_def] 
        "x~=UU==> sscase$f$g$(sinr$x) = g$x";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (asm_simp_tac Ssum0_ss  1);
qed "sscase3";
Addsimps [sscase3];


Goalw [sinl_def,sinr_def] 
        "(sinl$x << sinl$y) = (x << y)";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (rtac less_ssum3a 1);
qed "less_ssum4a";

Goalw [sinl_def,sinr_def] 
        "(sinr$x << sinr$y) = (x << y)";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (rtac less_ssum3b 1);
qed "less_ssum4b";

Goalw [sinl_def,sinr_def] 
        "(sinl$x << sinr$y) = (x = UU)";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (rtac less_ssum3c 1);
qed "less_ssum4c";

Goalw [sinl_def,sinr_def] 
        "(sinr$x << sinl$y) = (x = UU)";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (rtac less_ssum3d 1);
qed "less_ssum4d";

Goalw [sinl_def,sinr_def] 
        "chain(Y) ==> (!i.? x.(Y i)=sinl$x)|(!i.? y.(Y i)=sinr$y)";
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl]) 1);
by (etac ssum_lemma4 1);
qed "ssum_chainE";


Goalw [sinl_def,sinr_def,sscase_def] 
"[| chain(Y); !i.? x. Y(i) = sinl$x |] ==>\ 
\   lub(range(Y)) = sinl$(lub(range(%i. sscase$(LAM x. x)$(LAM y. UU)$(Y i))))";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac (beta_cfun RS ext) 1);
by tac;
by (rtac thelub_ssum1a 1);
by (atac 1);
by (rtac allI 1);
by (etac allE 1);
by (etac exE 1);
by (rtac exI 1);
by (etac box_equals 1);
by (rtac refl 1);
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinl]) 1);
qed "thelub_ssum2a";

Goalw [sinl_def,sinr_def,sscase_def] 
"[| chain(Y); !i.? x. Y(i) = sinr$x |] ==>\ 
\   lub(range(Y)) = sinr$(lub(range(%i. sscase$(LAM y. UU)$(LAM x. x)$(Y i))))";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac (beta_cfun RS ext) 1);
by tac;
by (rtac thelub_ssum1b 1);
by (atac 1);
by (rtac allI 1);
by (etac allE 1);
by (etac exE 1);
by (rtac exI 1);
by (etac box_equals 1);
by (rtac refl 1);
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2, cont_Iwhen3]) 1);
qed "thelub_ssum2b";

Goalw [sinl_def,sinr_def] 
        "[| chain(Y); lub(range(Y)) = sinl$x|] ==> !i.? x. Y(i)=sinl$x";
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2, cont_Iwhen3]) 1);
by (etac ssum_lemma9 1);
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2, cont_Iwhen3]) 1);
qed "thelub_ssum2a_rev";

Goalw [sinl_def,sinr_def] 
     "[| chain(Y); lub(range(Y)) = sinr$x|] ==> !i.? x. Y(i)=sinr$x";
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2, cont_Iwhen3]) 1);
by (etac ssum_lemma10 1);
by (asm_simp_tac (Ssum0_ss addsimps [cont_Isinr,cont_Isinl,cont_Iwhen1,cont_Iwhen2, cont_Iwhen3]) 1);
qed "thelub_ssum2b_rev";

Goal "chain(Y) ==>\ 
\   lub(range(Y)) = sinl$(lub(range(%i. sscase$(LAM x. x)$(LAM y. UU)$(Y i))))\
\ | lub(range(Y)) = sinr$(lub(range(%i. sscase$(LAM y. UU)$(LAM x. x)$(Y i))))";
by (rtac (ssum_chainE RS disjE) 1);
by (atac 1);
by (rtac disjI1 1);
by (etac thelub_ssum2a 1);
by (atac 1);
by (rtac disjI2 1);
by (etac thelub_ssum2b 1);
by (atac 1);
qed "thelub_ssum3";

Goal "sscase$sinl$sinr$z=z";
by (res_inst_tac [("p","z")] ssumE 1);
by Auto_tac;
qed "sscase4";


(* ------------------------------------------------------------------------ *)
(* install simplifier for Ssum                                              *)
(* ------------------------------------------------------------------------ *)

val Ssum_rews = [strict_sinl,strict_sinr,defined_sinl,defined_sinr,
                sscase1,sscase2,sscase3];
