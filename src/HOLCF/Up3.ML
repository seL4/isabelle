(*  Title:      HOLCF/Up3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  ('a)u for class pcpo
*)

(* for compatibility with old HOLCF-Version *)
Goal "UU = Abs_Up(Inl ())";
by (simp_tac (HOL_ss addsimps [UU_def,UU_up_def]) 1);
qed "inst_up_pcpo";

(* -------------------------------------------------------------------------*)
(* some lemmas restated for class pcpo                                      *)
(* ------------------------------------------------------------------------ *)

Goal "~ Iup(x) << UU";
by (stac inst_up_pcpo 1);
by (rtac less_up2b 1);
qed "less_up3b";

Goal "Iup(x) ~= UU";
by (stac inst_up_pcpo 1);
by (rtac defined_Iup 1);
qed "defined_Iup2";
AddIffs [defined_Iup2];

(* ------------------------------------------------------------------------ *)
(* continuity for Iup                                                       *)
(* ------------------------------------------------------------------------ *)

Goal "contlub(Iup)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_up1a RS sym) 2);
by (fast_tac HOL_cs 3);
by (etac (monofun_Iup RS ch2ch_monofun) 2);
by (res_inst_tac [("f","Iup")] arg_cong  1);
by (rtac lub_equal 1);
by (atac 1);
by (rtac (monofun_Ifup2 RS ch2ch_monofun) 1);
by (etac (monofun_Iup RS ch2ch_monofun) 1);
by (asm_simp_tac Up0_ss 1);
qed "contlub_Iup";

Goal "cont(Iup)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Iup 1);
by (rtac contlub_Iup 1);
qed "cont_Iup";
AddIffs [cont_Iup];

(* ------------------------------------------------------------------------ *)
(* continuity for Ifup                                                     *)
(* ------------------------------------------------------------------------ *)

Goal "contlub(Ifup)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_fun RS sym) 2);
by (etac (monofun_Ifup1 RS ch2ch_monofun) 2);
by (rtac ext 1);
by (res_inst_tac [("p","x")] upE 1);
by (asm_simp_tac Up0_ss 1);
by (rtac (lub_const RS thelubI RS sym) 1);
by (asm_simp_tac Up0_ss 1);
by (etac contlub_cfun_fun 1);
qed "contlub_Ifup1";


Goal "contlub(Ifup(f))";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac disjE 1);
by   (stac thelub_up1a 2);
by     (atac 2);
by    (atac 2);
by   (asm_simp_tac Up0_ss 2);
by   (stac thelub_up1b 3);
by     (atac 3);
by    (atac 3);
by   (fast_tac HOL_cs 1);
by  (asm_simp_tac Up0_ss 2);
by  (rtac (chain_UU_I_inverse RS sym) 2);
by  (rtac allI 2);
by  (res_inst_tac [("p","Y(i)")] upE 2);
by   (asm_simp_tac Up0_ss 2);
by  (rtac notE 2);
by   (dtac spec 2);
by   (etac spec 2);
by  (atac 2);
by (stac contlub_cfun_arg 1);
by  (etac (monofun_Ifup2 RS ch2ch_monofun) 1);
by (rtac lub_equal2 1);
by   (rtac (monofun_Rep_CFun2 RS ch2ch_monofun) 2);
by   (etac (monofun_Ifup2 RS ch2ch_monofun) 2);
by  (etac (monofun_Ifup2 RS ch2ch_monofun) 2);
by (rtac (chain_mono2 RS exE) 1);
by   (atac 2);
by  (etac exE 1);
by  (etac exE 1);
by  (rtac exI 1);
by  (res_inst_tac [("s","Iup(x)"),("t","Y(i)")] ssubst 1);
by   (atac 1);
by  (rtac defined_Iup2 1);
by (rtac exI 1);
by (strip_tac 1);
by (res_inst_tac [("p","Y(i)")] upE 1);
by  (asm_simp_tac Up0_ss 2);
by (res_inst_tac [("P","Y(i) = UU")] notE 1);
by  (fast_tac HOL_cs 1);
by (stac inst_up_pcpo 1);
by (atac 1);
qed "contlub_Ifup2";

Goal "cont(Ifup)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Ifup1 1);
by (rtac contlub_Ifup1 1);
qed "cont_Ifup1";

Goal "cont(Ifup(f))";
by (rtac monocontlub2cont 1);
by (rtac monofun_Ifup2 1);
by (rtac contlub_Ifup2 1);
qed "cont_Ifup2";


(* ------------------------------------------------------------------------ *)
(* continuous versions of lemmas for ('a)u                                  *)
(* ------------------------------------------------------------------------ *)

Goalw [up_def] "z = UU | (EX x. z = up$x)";
by (simp_tac (Up0_ss addsimps [cont_Iup]) 1);
by (stac inst_up_pcpo 1);
by (rtac Exh_Up 1);
qed "Exh_Up1";

Goalw [up_def] "up$x=up$y ==> x=y";
by (rtac inject_Iup 1);
by Auto_tac;
qed "inject_up";

Goalw [up_def] " up$x ~= UU";
by Auto_tac;
qed "defined_up";

val prems = Goalw [up_def] 
        "[| p=UU ==> Q; !!x. p=up$x==>Q|] ==>Q";
by (rtac upE 1);
by (resolve_tac prems 1);
by (etac (inst_up_pcpo RS ssubst) 1);
by (resolve_tac (tl prems) 1);
by (asm_simp_tac (Up0_ss addsimps [cont_Iup]) 1);
qed "upE1";

val tac = (simp_tac (simpset() addsimps [cont_Iup,cont_Ifup1,
                cont_Ifup2,cont2cont_CF1L]) 1);

Goalw [up_def,fup_def] "fup$f$UU=UU";
by (stac inst_up_pcpo 1);
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (simp_tac (Up0_ss addsimps [cont_Iup,cont_Ifup1,cont_Ifup2]) 1);
qed "fup1";

Goalw [up_def,fup_def] "fup$f$(up$x)=f$x";
by (stac beta_cfun 1);
by (rtac cont_Iup 1);
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by (rtac cont_Ifup2 1);
by (simp_tac (Up0_ss addsimps [cont_Iup,cont_Ifup1,cont_Ifup2]) 1);
qed "fup2";

Goalw [up_def,fup_def] "~ up$x << UU";
by (simp_tac (Up0_ss addsimps [cont_Iup]) 1);
by (rtac less_up3b 1);
qed "less_up4b";

Goalw [up_def,fup_def]
         "(up$x << up$y) = (x<<y)";
by (simp_tac (Up0_ss addsimps [cont_Iup]) 1);
by (rtac less_up2c 1);
qed "less_up4c";

Goalw [up_def,fup_def] 
"[| chain(Y); EX i x. Y(i) = up$x |] ==>\
\      lub(range(Y)) = up$(lub(range(%i. fup$(LAM x. x)$(Y i))))";
by (stac beta_cfun 1);
by tac;
by (stac beta_cfun 1);
by tac;
by (stac (beta_cfun RS ext) 1);
by tac;
by (rtac thelub_up1a 1);
by (atac 1);
by (etac exE 1);
by (etac exE 1);
by (rtac exI 1);
by (rtac exI 1);
by (etac box_equals 1);
by (rtac refl 1);
by (simp_tac (Up0_ss addsimps [cont_Iup]) 1);
qed "thelub_up2a";



Goalw [up_def,fup_def] 
"[| chain(Y); ! i x. Y(i) ~= up$x |] ==> lub(range(Y)) = UU";
by (stac inst_up_pcpo 1);
by (rtac thelub_up1b 1);
by (atac 1);
by (strip_tac 1);
by (dtac spec 1);
by (dtac spec 1);
by (asm_full_simp_tac (Up0_ss addsimps [cont_Iup]) 1);
qed "thelub_up2b";


Goal "(EX x. z = up$x) = (z~=UU)";
by (rtac iffI 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (rtac defined_up 1);
by (res_inst_tac [("p","z")] upE1 1);
by (etac notE 1);
by (atac 1);
by (etac exI 1);
qed "up_lemma2";


Goal "[| chain(Y); lub(range(Y)) = up$x |] ==> EX i x. Y(i) = up$x";
by (rtac exE 1);
by (rtac chain_UU_I_inverse2 1);
by (rtac (up_lemma2 RS iffD1) 1);
by (etac exI 1);
by (rtac exI 1);
by (rtac (up_lemma2 RS iffD2) 1);
by (atac 1);
qed "thelub_up2a_rev";

Goal "[| chain(Y); lub(range(Y)) = UU |] ==> ! i x.  Y(i) ~= up$x";
by (blast_tac (claset() addSDs [chain_UU_I RS spec, 
                                exI RS (up_lemma2 RS iffD1)]) 1);
qed "thelub_up2b_rev";


Goal "chain(Y) ==> lub(range(Y)) = UU | \
\                  lub(range(Y)) = up$(lub(range(%i. fup$(LAM x. x)$(Y i))))";
by (rtac disjE 1);
by (rtac disjI1 2);
by (rtac thelub_up2b 2);
by (atac 2);
by (atac 2);
by (rtac disjI2 2);
by (rtac thelub_up2a 2);
by (atac 2);
by (atac 2);
by (fast_tac HOL_cs 1);
qed "thelub_up3";

Goal "fup$up$x=x";
by (res_inst_tac [("p","x")] upE1 1);
by (asm_simp_tac ((simpset_of Cfun3.thy) addsimps [fup1,fup2]) 1);
by (asm_simp_tac ((simpset_of Cfun3.thy) addsimps [fup1,fup2]) 1);
qed "fup3";

(* ------------------------------------------------------------------------ *)
(* install simplifier for ('a)u                                             *)
(* ------------------------------------------------------------------------ *)

Addsimps [fup1,fup2,defined_up];
