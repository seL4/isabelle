(*  Title:      HOLCF/Up2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for up2.thy 
*)

open Up2;

(* -------------------------------------------------------------------------*)
(* type ('a)u is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_up" Up2.thy "UU_up << z"
 (fn prems =>
        [
        (stac inst_up_po 1),
        (rtac less_up1a 1)
        ]);

(* -------------------------------------------------------------------------*)
(* access to less_up in class po                                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_up2b" Up2.thy "~ Iup(x) << UU_up"
 (fn prems =>
        [
        (stac inst_up_po 1),
        (rtac less_up1b 1)
        ]);

qed_goal "less_up2c" Up2.thy "(Iup(x)<<Iup(y)) = (x<<y)"
 (fn prems =>
        [
        (stac inst_up_po 1),
        (rtac less_up1c 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Iup and Ifup are monotone                                               *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_Iup" Up2.thy [monofun] "monofun(Iup)"
 (fn prems =>
        [
        (strip_tac 1),
        (etac (less_up2c RS iffD2) 1)
        ]);

qed_goalw "monofun_Ifup1" Up2.thy [monofun] "monofun(Ifup)"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac (less_fun RS iffD2) 1),
        (strip_tac 1),
        (res_inst_tac [("p","xa")] upE 1),
        (asm_simp_tac Up0_ss 1),
        (asm_simp_tac Up0_ss 1),
        (etac monofun_cfun_fun 1)
        ]);

qed_goalw "monofun_Ifup2" Up2.thy [monofun] "monofun(Ifup(f))"
 (fn prems =>
        [
        (strip_tac 1),
        (res_inst_tac [("p","x")] upE 1),
        (asm_simp_tac Up0_ss 1),
        (asm_simp_tac Up0_ss 1),
        (res_inst_tac [("p","y")] upE 1),
        (hyp_subst_tac 1),
        (rtac notE 1),
        (rtac less_up2b 1),
        (atac 1),
        (asm_simp_tac Up0_ss 1),
        (rtac monofun_cfun_arg 1),
        (hyp_subst_tac 1),
        (etac (less_up2c  RS iffD1) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Some kind of surjectivity lemma                                          *)
(* ------------------------------------------------------------------------ *)


qed_goal "up_lemma1" Up2.thy  "z=Iup(x) ==> Iup(Ifup(LAM x.x)(z)) = z"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (asm_simp_tac Up0_ss 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* ('a)u is a cpo                                                           *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_up1a" Up2.thy 
"[|is_chain(Y);? i x.Y(i)=Iup(x)|] ==>\
\ range(Y) <<| Iup(lub(range(%i.(Ifup (LAM x.x) (Y(i))))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (res_inst_tac [("p","Y(i)")] upE 1),
        (res_inst_tac [("s","UU_up"),("t","Y(i)")] subst 1),
        (etac sym 1),
        (rtac minimal_up 1),
        (res_inst_tac [("t","Y(i)")] (up_lemma1 RS subst) 1),
        (atac 1),
        (rtac (less_up2c RS iffD2) 1),
        (rtac is_ub_thelub 1),
        (etac (monofun_Ifup2 RS ch2ch_monofun) 1),
        (strip_tac 1),
        (res_inst_tac [("p","u")] upE 1),
        (etac exE 1),
        (etac exE 1),
        (res_inst_tac [("P","Y(i)<<UU_up")] notE 1),
        (res_inst_tac [("s","Iup(x)"),("t","Y(i)")] ssubst 1),
        (atac 1),
        (rtac less_up2b 1),
        (hyp_subst_tac 1),
        (etac (ub_rangeE RS spec) 1),
        (res_inst_tac [("t","u")] (up_lemma1 RS subst) 1),
        (atac 1),
        (rtac (less_up2c RS iffD2) 1),
        (rtac is_lub_thelub 1),
        (etac (monofun_Ifup2 RS ch2ch_monofun) 1),
        (etac (monofun_Ifup2 RS ub2ub_monofun) 1)
        ]);

qed_goal "lub_up1b" Up2.thy 
"[|is_chain(Y);!i x. Y(i)~=Iup(x)|] ==>\
\ range(Y) <<| UU_up"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (res_inst_tac [("p","Y(i)")] upE 1),
        (res_inst_tac [("s","UU_up"),("t","Y(i)")] ssubst 1),
        (atac 1),
        (rtac refl_less 1),
        (rtac notE 1),
        (dtac spec 1),
        (dtac spec 1),
        (atac 1),
        (atac 1),
        (strip_tac 1),
        (rtac minimal_up 1)
        ]);

bind_thm ("thelub_up1a", lub_up1a RS thelubI);
(*
[| is_chain ?Y1; ? i x. ?Y1 i = Iup x |] ==>
 lub (range ?Y1) = Iup (lub (range (%i. Iup (LAM x. x) (?Y1 i))))
*)

bind_thm ("thelub_up1b", lub_up1b RS thelubI);
(*
[| is_chain ?Y1; ! i x. ?Y1 i ~= Iup x |] ==>
 lub (range ?Y1) = UU_up
*)

qed_goal "cpo_up" Up2.thy 
        "is_chain(Y::nat=>('a)u) ==> ? x.range(Y) <<|x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac disjE 1),
        (rtac exI 2),
        (etac lub_up1a 2),
        (atac 2),
        (rtac exI 2),
        (etac lub_up1b 2),
        (atac 2),
        (fast_tac HOL_cs 1)
        ]);

