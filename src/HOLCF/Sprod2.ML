(*  Title:      HOLCF/sprod2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for sprod2.thy
*)


open Sprod2;

(* ------------------------------------------------------------------------ *)
(* access to less_sprod in class po                                         *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_sprod3a" Sprod2.thy 
        "p1=Ispair UU UU ==> p1 << p2"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac inst_sprod_po 1),
        (etac less_sprod1a 1)
        ]);


qed_goal "less_sprod3b" Sprod2.thy
 "p1~=Ispair UU UU ==>\
\       (p1<<p2) = (Isfst(p1)<<Isfst(p2) & Issnd(p1)<<Issnd(p2))" 
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac inst_sprod_po 1),
        (etac less_sprod1b 1)
        ]);

qed_goal "less_sprod4b" Sprod2.thy 
        "p << Ispair UU UU ==> p = Ispair UU UU"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac less_sprod2b 1),
        (etac (inst_sprod_po RS subst) 1)
        ]);

bind_thm ("less_sprod4a", less_sprod4b RS defined_Ispair_rev);
(* Ispair ?a ?b << Ispair UU UU ==> ?a = UU | ?b = UU *)

qed_goal "less_sprod4c" Sprod2.thy
 "[|Ispair xa ya << Ispair x y; xa~=UU; ya~=UU; x~=UU; y~=UU|] ==>\
\               xa<<x & ya << y"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac less_sprod2c 1),
        (etac (inst_sprod_po RS subst) 1),
        (REPEAT (atac 1))
        ]);

(* ------------------------------------------------------------------------ *)
(* type sprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_sprod" Sprod2.thy  "Ispair UU UU << p"
(fn prems =>
        [
        (rtac less_sprod3a 1),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Ispair is monotone in both arguments                                     *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_Ispair1" Sprod2.thy [monofun] "monofun(Ispair)"
(fn prems =>
        [
        (strip_tac 1),
        (rtac (less_fun RS iffD2) 1),
        (strip_tac 1),
        (res_inst_tac [("Q",
        " Ispair y xa = Ispair UU UU")] (excluded_middle RS disjE) 1),
        (res_inst_tac [("Q",
        " Ispair x xa = Ispair UU UU")] (excluded_middle RS disjE) 1),
        (rtac (less_sprod3b RS iffD2) 1),
        (atac 1),
        (rtac conjI 1),
        (stac Isfst 1),
        (etac (strict_Ispair_rev RS conjunct1) 1),
        (etac (strict_Ispair_rev RS conjunct2) 1),
        (stac Isfst 1),
        (etac (strict_Ispair_rev RS conjunct1) 1),
        (etac (strict_Ispair_rev RS conjunct2) 1),
        (atac 1),
        (stac Issnd 1),
        (etac (strict_Ispair_rev RS conjunct1) 1),
        (etac (strict_Ispair_rev RS conjunct2) 1),
        (stac Issnd 1),
        (etac (strict_Ispair_rev RS conjunct1) 1),
        (etac (strict_Ispair_rev RS conjunct2) 1),
        (rtac refl_less 1),
        (etac less_sprod3a 1),
        (res_inst_tac [("Q",
        " Ispair x xa  = Ispair UU UU")] (excluded_middle RS disjE) 1),
        (etac less_sprod3a 2),
        (res_inst_tac [("P","Ispair y xa = Ispair UU UU")] notE 1),
        (atac 2),
        (rtac defined_Ispair 1),
        (etac notUU_I 1),
        (etac (strict_Ispair_rev RS  conjunct1) 1),
        (etac (strict_Ispair_rev RS  conjunct2) 1)
        ]);


qed_goalw "monofun_Ispair2" Sprod2.thy [monofun] "monofun(Ispair(x))"
(fn prems =>
        [
        (strip_tac 1),
        (res_inst_tac [("Q",
        " Ispair x y = Ispair UU UU")] (excluded_middle RS disjE) 1),
        (res_inst_tac [("Q",
        " Ispair x xa = Ispair UU UU")] (excluded_middle RS disjE) 1),
        (rtac (less_sprod3b RS iffD2) 1),
        (atac 1),
        (rtac conjI 1),
        (stac Isfst 1),
        (etac (strict_Ispair_rev RS conjunct1) 1),
        (etac (strict_Ispair_rev RS conjunct2) 1),
        (stac Isfst 1),
        (etac (strict_Ispair_rev RS conjunct1) 1),
        (etac (strict_Ispair_rev RS conjunct2) 1),
        (rtac refl_less 1),
        (stac Issnd 1),
        (etac (strict_Ispair_rev RS conjunct1) 1),
        (etac (strict_Ispair_rev RS conjunct2) 1),
        (stac Issnd 1),
        (etac (strict_Ispair_rev RS conjunct1) 1),
        (etac (strict_Ispair_rev RS conjunct2) 1),
        (atac 1),
        (etac less_sprod3a 1),
        (res_inst_tac [("Q",
        " Ispair x xa = Ispair UU UU")] (excluded_middle RS disjE) 1),
        (etac less_sprod3a 2),
        (res_inst_tac [("P","Ispair x y = Ispair UU UU")] notE 1),
        (atac 2),
        (rtac defined_Ispair 1),
        (etac (strict_Ispair_rev RS  conjunct1) 1),
        (etac notUU_I 1),
        (etac (strict_Ispair_rev RS  conjunct2) 1)
        ]);

qed_goal " monofun_Ispair" Sprod2.thy 
 "[|x1<<x2; y1<<y2|] ==> Ispair x1 y1 << Ispair x2 y2"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans_less 1),
        (rtac (monofun_Ispair1 RS monofunE RS spec RS spec RS mp RS 
        (less_fun RS iffD1 RS spec)) 1),
        (rtac (monofun_Ispair2 RS monofunE RS spec RS spec RS mp) 2),
        (atac 1),
        (atac 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Isfst and Issnd are monotone                                             *)
(* ------------------------------------------------------------------------ *)

qed_goalw " monofun_Isfst" Sprod2.thy [monofun] "monofun(Isfst)"
(fn prems =>
        [
        (strip_tac 1),
        (res_inst_tac [("p","x")] IsprodE 1),
        (hyp_subst_tac 1),
        (rtac trans_less 1),
        (rtac minimal 2),
        (stac strict_Isfst1 1),
        (rtac refl_less 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","y")] IsprodE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("t","Isfst(Ispair xa ya)")] subst 1),
        (rtac refl_less 2),
        (etac (less_sprod4b RS sym RS arg_cong) 1),
        (hyp_subst_tac 1),
        (stac Isfst 1),
        (atac 1),
        (atac 1),
        (stac Isfst 1),
        (atac 1),
        (atac 1),
        (etac (less_sprod4c RS  conjunct1) 1),
        (REPEAT (atac 1))
        ]);

qed_goalw "monofun_Issnd" Sprod2.thy [monofun] "monofun(Issnd)"
(fn prems =>
        [
        (strip_tac 1),
        (res_inst_tac [("p","x")] IsprodE 1),
        (hyp_subst_tac 1),
        (rtac trans_less 1),
        (rtac minimal 2),
        (stac strict_Issnd1 1),
        (rtac refl_less 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","y")] IsprodE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("t","Issnd(Ispair xa ya)")] subst 1),
        (rtac refl_less 2),
        (etac (less_sprod4b RS sym RS arg_cong) 1),
        (hyp_subst_tac 1),
        (stac Issnd 1),
        (atac 1),
        (atac 1),
        (stac Issnd 1),
        (atac 1),
        (atac 1),
        (etac (less_sprod4c RS  conjunct2) 1),
        (REPEAT (atac 1))
        ]);


(* ------------------------------------------------------------------------ *)
(* the type 'a ** 'b is a cpo                                               *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_sprod" Sprod2.thy 
"[|is_chain(S)|] ==> range(S) <<| \
\ Ispair (lub(range(%i.Isfst(S i)))) (lub(range(%i.Issnd(S i))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (res_inst_tac [("t","S(i)")] (surjective_pairing_Sprod RS ssubst) 1),
        (rtac monofun_Ispair 1),
        (rtac is_ub_thelub 1),
        (etac (monofun_Isfst RS ch2ch_monofun) 1),
        (rtac is_ub_thelub 1),
        (etac (monofun_Issnd RS ch2ch_monofun) 1),
        (strip_tac 1),
        (res_inst_tac [("t","u")] (surjective_pairing_Sprod RS ssubst) 1),
        (rtac monofun_Ispair 1),
        (rtac is_lub_thelub 1),
        (etac (monofun_Isfst RS ch2ch_monofun) 1),
        (etac (monofun_Isfst RS ub2ub_monofun) 1),
        (rtac is_lub_thelub 1),
        (etac (monofun_Issnd RS ch2ch_monofun) 1),
        (etac (monofun_Issnd RS ub2ub_monofun) 1)
        ]);

bind_thm ("thelub_sprod", lub_sprod RS thelubI);


qed_goal "cpo_sprod" Sprod2.thy 
        "is_chain(S::nat=>'a**'b)==>? x.range(S)<<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac exI 1),
        (etac lub_sprod 1)
        ]);








