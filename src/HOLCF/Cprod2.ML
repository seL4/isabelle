(*  Title:      HOLCF/cprod2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for cprod2.thy 
*)

open Cprod2;

(* for compatibility with old HOLCF-Version *)
qed_goal "inst_cprod_po" thy "(op <<)=(%x y. fst x<<fst y & snd x<<snd y)"
 (fn prems => 
        [
        (fold_goals_tac [less_cprod_def]),
        (rtac refl 1)
        ]);

qed_goalw "less_cprod4c" thy [inst_cprod_po RS eq_reflection]
 "(x1,y1) << (x2,y2) ==> x1 << x2 & y1 << y2"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac conjE 1),
        (dtac (fst_conv RS subst) 1),
        (dtac (fst_conv RS subst) 1),
        (dtac (fst_conv RS subst) 1),
        (dtac (snd_conv RS subst) 1),
        (dtac (snd_conv RS subst) 1),
        (dtac (snd_conv RS subst) 1),
        (rtac conjI 1),
        (atac 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* type cprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_cprod" thy  "(UU,UU)<<p"
(fn prems =>
        [
        (simp_tac(!simpset addsimps[inst_cprod_po])1)
        ]);

bind_thm ("UU_cprod_def",minimal_cprod RS minimal2UU RS sym);

qed_goal "least_cprod" thy "? x::'a*'b.!y. x<<y"
(fn prems =>
        [
        (res_inst_tac [("x","(UU,UU)")] exI 1),
        (rtac (minimal_cprod RS allI) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Pair <_,_>  is monotone in both arguments                                *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_pair1" thy [monofun] "monofun Pair"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac (less_fun RS iffD2) 1),
        (strip_tac 1),
        (asm_simp_tac (!simpset addsimps [inst_cprod_po]) 1)
        ]);

qed_goalw "monofun_pair2" thy [monofun] "monofun(Pair x)"
 (fn prems =>
        [
        (asm_simp_tac (!simpset addsimps [inst_cprod_po]) 1)
        ]);

qed_goal "monofun_pair" thy "[|x1<<x2; y1<<y2|] ==> (x1::'a::cpo,y1::'b::cpo)<<(x2,y2)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans_less 1),
        (rtac (monofun_pair1 RS monofunE RS spec RS spec RS mp RS 
        (less_fun RS iffD1 RS spec)) 1),
        (rtac (monofun_pair2 RS monofunE RS spec RS spec RS mp) 2),
        (atac 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* fst and snd are monotone                                                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_fst" thy [monofun] "monofun fst"
 (fn prems =>
        [
        (strip_tac 1),
        (res_inst_tac [("p","x")] PairE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","y")] PairE 1),
        (hyp_subst_tac 1),
        (Asm_simp_tac  1),
        (etac (less_cprod4c RS conjunct1) 1)
        ]);

qed_goalw "monofun_snd" thy [monofun] "monofun snd"
 (fn prems =>
        [
        (strip_tac 1),
        (res_inst_tac [("p","x")] PairE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","y")] PairE 1),
        (hyp_subst_tac 1),
        (Asm_simp_tac  1),
        (etac (less_cprod4c RS conjunct2) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the type 'a * 'b is a cpo                                                *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_cprod" thy 
"is_chain S ==> range S<<|(lub(range(%i. fst(S i))),lub(range(%i. snd(S i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (conjI RS is_lubI) 1),
        (rtac (allI RS ub_rangeI) 1),
        (res_inst_tac [("t","S i")] (surjective_pairing RS ssubst) 1),
        (rtac monofun_pair 1),
        (rtac is_ub_thelub 1),
        (etac (monofun_fst RS ch2ch_monofun) 1),
        (rtac is_ub_thelub 1),
        (etac (monofun_snd RS ch2ch_monofun) 1),
        (strip_tac 1),
        (res_inst_tac [("t","u")] (surjective_pairing RS ssubst) 1),
        (rtac monofun_pair 1),
        (rtac is_lub_thelub 1),
        (etac (monofun_fst RS ch2ch_monofun) 1),
        (etac (monofun_fst RS ub2ub_monofun) 1),
        (rtac is_lub_thelub 1),
        (etac (monofun_snd RS ch2ch_monofun) 1),
        (etac (monofun_snd RS ub2ub_monofun) 1)
        ]);

bind_thm ("thelub_cprod", lub_cprod RS thelubI);
(*
"is_chain ?S1 ==>
 lub (range ?S1) =
 (lub (range (%i. fst (?S1 i))), lub (range (%i. snd (?S1 i))))" : thm

*)

qed_goal "cpo_cprod" thy "is_chain(S::nat=>'a::cpo*'b::cpo)==>? x. range S<<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac exI 1),
        (etac lub_cprod 1)
        ]);


