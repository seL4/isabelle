(*  Title:      HOLCF/Sprod2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for Sprod2.thy
*)

open Sprod2;

(* for compatibility with old HOLCF-Version *)
qed_goal "inst_sprod_po" thy "(op <<)=(%x y. Isfst x<<Isfst y&Issnd x<<Issnd y)"
 (fn prems => 
        [
	(fold_goals_tac [less_sprod_def]),
	(rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* type sprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_sprod" thy "Ispair UU UU << p"
(fn prems =>
        [
        (simp_tac(Sprod0_ss addsimps[inst_sprod_po,minimal])1)
        ]);

bind_thm ("UU_sprod_def",minimal_sprod RS minimal2UU RS sym);

qed_goal "least_sprod" thy "? x::'a**'b.!y. x<<y"
(fn prems =>
        [
        (res_inst_tac [("x","Ispair UU UU")] exI 1),
        (rtac (minimal_sprod RS allI) 1)
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
        (res_inst_tac [("Q","xa=UU")] (excluded_middle RS disjE) 1),
        (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
        (forward_tac [notUU_I] 1),
        (atac 1),
        (REPEAT(asm_simp_tac(Sprod0_ss 
                addsimps[inst_sprod_po,refl_less,minimal]) 1))
        ]);

qed_goalw "monofun_Ispair2" Sprod2.thy [monofun] "monofun(Ispair(x))"
(fn prems =>
        [
        (strip_tac 1),
        (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
        (res_inst_tac [("Q","xa=UU")] (excluded_middle RS disjE) 1),
        (forward_tac [notUU_I] 1),
        (atac 1),
        (REPEAT(asm_simp_tac(Sprod0_ss 
                addsimps[inst_sprod_po,refl_less,minimal]) 1))
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

qed_goalw "monofun_Isfst" Sprod2.thy [monofun] "monofun(Isfst)"
(fn prems => [(simp_tac (HOL_ss addsimps [inst_sprod_po]) 1)]);

qed_goalw "monofun_Issnd" Sprod2.thy [monofun] "monofun(Issnd)"
(fn prems => [(simp_tac (HOL_ss addsimps [inst_sprod_po]) 1)]);

(* ------------------------------------------------------------------------ *)
(* the type 'a ** 'b is a cpo                                               *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_sprod" Sprod2.thy 
"[|is_chain(S)|] ==> range(S) <<| \
\ Ispair (lub(range(%i. Isfst(S i)))) (lub(range(%i. Issnd(S i))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (conjI RS is_lubI) 1),
        (rtac (allI RS ub_rangeI) 1),
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
        "is_chain(S::nat=>'a**'b)==>? x. range(S)<<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac exI 1),
        (etac lub_sprod 1)
        ]);








