(*  Title:      HOLCF/Up3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for Up3.thy
*)

open Up3;

(* -------------------------------------------------------------------------*)
(* some lemmas restated for class pcpo                                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_up3b" Up3.thy "~ Iup(x) << UU"
 (fn prems =>
        [
        (stac inst_up_pcpo 1),
        (rtac less_up2b 1)
        ]);

qed_goal "defined_Iup2" Up3.thy "Iup(x) ~= UU"
 (fn prems =>
        [
        (stac inst_up_pcpo 1),
        (rtac defined_Iup 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* continuity for Iup                                                       *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_Iup" Up3.thy "contlub(Iup)"
 (fn prems =>
        [
        (rtac contlubI 1),
        (strip_tac 1),
        (rtac trans 1),
        (rtac (thelub_up1a RS sym) 2),
        (fast_tac HOL_cs 3),
        (etac (monofun_Iup RS ch2ch_monofun) 2),
        (res_inst_tac [("f","Iup")] arg_cong  1),
        (rtac lub_equal 1),
        (atac 1),
        (rtac (monofun_Ifup2 RS ch2ch_monofun) 1),
        (etac (monofun_Iup RS ch2ch_monofun) 1),
        (asm_simp_tac Up0_ss 1)
        ]);

qed_goal "cont_Iup" Up3.thy "cont(Iup)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Iup 1),
        (rtac contlub_Iup 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* continuity for Ifup                                                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_Ifup1" Up3.thy "contlub(Ifup)"
 (fn prems =>
        [
        (rtac contlubI 1),
        (strip_tac 1),
        (rtac trans 1),
        (rtac (thelub_fun RS sym) 2),
        (etac (monofun_Ifup1 RS ch2ch_monofun) 2),
        (rtac ext 1),
        (res_inst_tac [("p","x")] upE 1),
        (asm_simp_tac Up0_ss 1),
        (rtac (lub_const RS thelubI RS sym) 1),
        (asm_simp_tac Up0_ss 1),
        (etac contlub_cfun_fun 1)
        ]);


qed_goal "contlub_Ifup2" Up3.thy "contlub(Ifup(f))"
 (fn prems =>
        [
        (rtac contlubI 1),
        (strip_tac 1),
        (rtac disjE 1),
        (stac thelub_up1a 2),
        (atac 2),
        (atac 2),
        (asm_simp_tac Up0_ss 2),
        (stac thelub_up1b 3),
        (atac 3),
        (atac 3),
        (fast_tac HOL_cs 1),
        (asm_simp_tac Up0_ss 2),
        (rtac (chain_UU_I_inverse RS sym) 2),
        (rtac allI 2),
        (res_inst_tac [("p","Y(i)")] upE 2),
        (asm_simp_tac Up0_ss 2),
        (rtac notE 2),
        (dtac spec 2),
        (etac spec 2),
        (atac 2),
        (stac contlub_cfun_arg 1),
        (etac (monofun_Ifup2 RS ch2ch_monofun) 1),
        (rtac lub_equal2 1),
        (rtac (monofun_fapp2 RS ch2ch_monofun) 2),
        (etac (monofun_Ifup2 RS ch2ch_monofun) 2),
        (etac (monofun_Ifup2 RS ch2ch_monofun) 2),
        (rtac (chain_mono2 RS exE) 1),
        (atac 2),
        (etac exE 1),
        (etac exE 1),
        (rtac exI 1),
        (res_inst_tac [("s","Iup(x)"),("t","Y(i)")] ssubst 1),
        (atac 1),
        (rtac defined_Iup2 1),
        (rtac exI 1),
        (strip_tac 1),
        (res_inst_tac [("p","Y(i)")] upE 1),
        (asm_simp_tac Up0_ss 2),
        (res_inst_tac [("P","Y(i) = UU")] notE 1),
        (fast_tac HOL_cs 1),
        (stac inst_up_pcpo 1),
        (atac 1)
        ]);

qed_goal "cont_Ifup1" Up3.thy "cont(Ifup)"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Ifup1 1),
        (rtac contlub_Ifup1 1)
        ]);

qed_goal "cont_Ifup2" Up3.thy "cont(Ifup(f))"
 (fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_Ifup2 1),
        (rtac contlub_Ifup2 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* continuous versions of lemmas for ('a)u                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Exh_Up1" Up3.thy [up_def] "z = UU | (? x. z = up`x)"
 (fn prems =>
        [
        (simp_tac (Up0_ss addsimps [cont_Iup]) 1),
        (stac inst_up_pcpo 1),
        (rtac Exh_Up 1)
        ]);

qed_goalw "inject_up" Up3.thy [up_def] "up`x=up`y ==> x=y"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac inject_Iup 1),
        (etac box_equals 1),
        (simp_tac (Up0_ss addsimps [cont_Iup]) 1),
        (simp_tac (Up0_ss addsimps [cont_Iup]) 1)
        ]);

qed_goalw "defined_up" Up3.thy [up_def] " up`x ~= UU"
 (fn prems =>
        [
        (simp_tac (Up0_ss addsimps [cont_Iup]) 1),
        (rtac defined_Iup2 1)
        ]);

qed_goalw "upE1" Up3.thy [up_def] 
        "[| p=UU ==> Q; !!x. p=up`x==>Q|] ==>Q"
 (fn prems =>
        [
        (rtac upE 1),
        (resolve_tac prems 1),
        (etac (inst_up_pcpo RS ssubst) 1),
        (resolve_tac (tl prems) 1),
        (asm_simp_tac (Up0_ss addsimps [cont_Iup]) 1)
        ]);

val tac = (simp_tac (!simpset addsimps [cont_Iup,cont_Ifup1,
                cont_Ifup2,cont2cont_CF1L]) 1);

qed_goalw "fup1" Up3.thy [up_def,fup_def] "fup`f`UU=UU"
 (fn prems =>
        [
        (stac inst_up_pcpo 1),
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
	tac,
        (simp_tac (Up0_ss addsimps [cont_Iup,cont_Ifup1,cont_Ifup2]) 1)
        ]);

qed_goalw "fup2" Up3.thy [up_def,fup_def] "fup`f`(up`x)=f`x"
 (fn prems =>
        [
        (stac beta_cfun 1),
        (rtac cont_Iup 1),
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
        (rtac cont_Ifup2 1),
        (simp_tac (Up0_ss addsimps [cont_Iup,cont_Ifup1,cont_Ifup2]) 1)
        ]);

qed_goalw "less_up4b" Up3.thy [up_def,fup_def] "~ up`x << UU"
 (fn prems =>
        [
        (simp_tac (Up0_ss addsimps [cont_Iup]) 1),
        (rtac less_up3b 1)
        ]);

qed_goalw "less_up4c" Up3.thy [up_def,fup_def]
         "(up`x << up`y) = (x<<y)"
 (fn prems =>
        [
        (simp_tac (Up0_ss addsimps [cont_Iup]) 1),
        (rtac less_up2c 1)
        ]);

qed_goalw "thelub_up2a" Up3.thy [up_def,fup_def] 
"[| is_chain(Y); ? i x. Y(i) = up`x |] ==>\
\      lub(range(Y)) = up`(lub(range(%i. fup`(LAM x. x)`(Y i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac beta_cfun 1),
	tac,
        (stac beta_cfun 1),
	tac,
        (stac (beta_cfun RS ext) 1),
	tac,
        (rtac thelub_up1a 1),
        (atac 1),
        (etac exE 1),
        (etac exE 1),
        (rtac exI 1),
        (rtac exI 1),
        (etac box_equals 1),
        (rtac refl 1),
        (simp_tac (Up0_ss addsimps [cont_Iup]) 1)
        ]);



qed_goalw "thelub_up2b" Up3.thy [up_def,fup_def] 
"[| is_chain(Y); ! i x. Y(i) ~= up`x |] ==> lub(range(Y)) = UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac inst_up_pcpo 1),
        (rtac thelub_up1b 1),
        (atac 1),
        (strip_tac 1),
        (dtac spec 1),
        (dtac spec 1),
        (rtac swap 1),
        (atac 1),
        (dtac notnotD 1),
        (etac box_equals 1),
        (rtac refl 1),
        (simp_tac (Up0_ss addsimps [cont_Iup]) 1)
        ]);


qed_goal "up_lemma2" Up3.thy  " (? x.z = up`x) = (z~=UU)"
 (fn prems =>
        [
        (rtac iffI 1),
        (etac exE 1),
        (hyp_subst_tac 1),
        (rtac defined_up 1),
        (res_inst_tac [("p","z")] upE1 1),
        (etac notE 1),
        (atac 1),
        (etac exI 1)
        ]);


qed_goal "thelub_up2a_rev" Up3.thy  
"[| is_chain(Y); lub(range(Y)) = up`x |] ==> ? i x. Y(i) = up`x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac exE 1),
        (rtac chain_UU_I_inverse2 1),
        (rtac (up_lemma2 RS iffD1) 1),
        (etac exI 1),
        (rtac exI 1),
        (rtac (up_lemma2 RS iffD2) 1),
        (atac 1)
        ]);

qed_goal "thelub_up2b_rev" Up3.thy  
"[| is_chain(Y); lub(range(Y)) = UU |] ==> ! i x.  Y(i) ~= up`x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac allI 1),
        (rtac (not_ex RS iffD1) 1),
        (rtac contrapos 1),
        (etac (up_lemma2 RS iffD1) 2),
        (fast_tac (HOL_cs addSDs [chain_UU_I RS spec]) 1)
        ]);


qed_goal "thelub_up3" Up3.thy  
"is_chain(Y) ==> lub(range(Y)) = UU |\
\                lub(range(Y)) = up`(lub(range(%i. fup`(LAM x.x)`(Y i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac disjE 1),
        (rtac disjI1 2),
        (rtac thelub_up2b 2),
        (atac 2),
        (atac 2),
        (rtac disjI2 2),
        (rtac thelub_up2a 2),
        (atac 2),
        (atac 2),
        (fast_tac HOL_cs 1)
        ]);

qed_goal "fup3" Up3.thy "fup`up`x=x"
 (fn prems =>
        [
        (res_inst_tac [("p","x")] upE1 1),
        (asm_simp_tac ((simpset_of "Cfun3") addsimps [fup1,fup2]) 1),
        (asm_simp_tac ((simpset_of "Cfun3") addsimps [fup1,fup2]) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* install simplifier for ('a)u                                             *)
(* ------------------------------------------------------------------------ *)

val up_rews = [fup1,fup2,defined_up];

