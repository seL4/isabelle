(*  Title:      HOLCF/Cprod2
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance *::(pcpo,pcpo)po
*)

(* for compatibility with old HOLCF-Version *)
val prems = goal thy "(op <<)=(%x y. fst x<<fst y & snd x<<snd y)";
by (fold_goals_tac [less_cprod_def]);
by (rtac refl 1);
qed "inst_cprod_po";

val prems = goalw thy [inst_cprod_po RS eq_reflection] 
 "(x1,y1) << (x2,y2) ==> x1 << x2 & y1 << y2";
by (cut_facts_tac prems 1);
by (etac conjE 1);
by (dtac (fst_conv RS subst) 1);
by (dtac (fst_conv RS subst) 1);
by (dtac (fst_conv RS subst) 1);
by (dtac (snd_conv RS subst) 1);
by (dtac (snd_conv RS subst) 1);
by (dtac (snd_conv RS subst) 1);
by (rtac conjI 1);
by (atac 1);
by (atac 1);
qed "less_cprod4c";

(* ------------------------------------------------------------------------ *)
(* type cprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy  "(UU,UU)<<p";
by (simp_tac(simpset() addsimps[inst_cprod_po])1);
qed "minimal_cprod";

bind_thm ("UU_cprod_def",minimal_cprod RS minimal2UU RS sym);

val prems = goal thy "? x::'a*'b.!y. x<<y";
by (res_inst_tac [("x","(UU,UU)")] exI 1);
by (rtac (minimal_cprod RS allI) 1);
qed "least_cprod";

(* ------------------------------------------------------------------------ *)
(* Pair <_,_>  is monotone in both arguments                                *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [monofun]  "monofun Pair";
by (strip_tac 1);
by (rtac (less_fun RS iffD2) 1);
by (strip_tac 1);
by (asm_simp_tac (simpset() addsimps [inst_cprod_po]) 1);
qed "monofun_pair1";

val prems = goalw thy [monofun]  "monofun(Pair x)";
by (asm_simp_tac (simpset() addsimps [inst_cprod_po]) 1);
qed "monofun_pair2";

val prems = goal thy "[|x1<<x2; y1<<y2|] ==> (x1::'a::cpo,y1::'b::cpo)<<(x2,y2)";
by (cut_facts_tac prems 1);
by (rtac trans_less 1);
by (rtac (monofun_pair1 RS monofunE RS spec RS spec RS mp RS (less_fun RS iffD1 RS spec)) 1);
by (rtac (monofun_pair2 RS monofunE RS spec RS spec RS mp) 2);
by (atac 1);
by (atac 1);
qed "monofun_pair";

(* ------------------------------------------------------------------------ *)
(* fst and snd are monotone                                                 *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [monofun]  "monofun fst";
by (strip_tac 1);
by (res_inst_tac [("p","x")] PairE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","y")] PairE 1);
by (hyp_subst_tac 1);
by (Asm_simp_tac  1);
by (etac (less_cprod4c RS conjunct1) 1);
qed "monofun_fst";

val prems = goalw thy [monofun]  "monofun snd";
by (strip_tac 1);
by (res_inst_tac [("p","x")] PairE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","y")] PairE 1);
by (hyp_subst_tac 1);
by (Asm_simp_tac  1);
by (etac (less_cprod4c RS conjunct2) 1);
qed "monofun_snd";

(* ------------------------------------------------------------------------ *)
(* the type 'a * 'b is a cpo                                                *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy 
"chain S ==> range S<<|(lub(range(%i. fst(S i))),lub(range(%i. snd(S i))))";
by (cut_facts_tac prems 1);
by (rtac (conjI RS is_lubI) 1);
by (rtac (allI RS ub_rangeI) 1);
by (res_inst_tac [("t","S i")] (surjective_pairing RS ssubst) 1);
by (rtac monofun_pair 1);
by (rtac is_ub_thelub 1);
by (etac (monofun_fst RS ch2ch_monofun) 1);
by (rtac is_ub_thelub 1);
by (etac (monofun_snd RS ch2ch_monofun) 1);
by (strip_tac 1);
by (res_inst_tac [("t","u")] (surjective_pairing RS ssubst) 1);
by (rtac monofun_pair 1);
by (rtac is_lub_thelub 1);
by (etac (monofun_fst RS ch2ch_monofun) 1);
by (etac (monofun_fst RS ub2ub_monofun) 1);
by (rtac is_lub_thelub 1);
by (etac (monofun_snd RS ch2ch_monofun) 1);
by (etac (monofun_snd RS ub2ub_monofun) 1);
qed "lub_cprod";

bind_thm ("thelub_cprod", lub_cprod RS thelubI);
(*
"chain ?S1 ==>
 lub (range ?S1) =
 (lub (range (%i. fst (?S1 i))), lub (range (%i. snd (?S1 i))))" : thm

*)

val prems = goal thy "chain(S::nat=>'a::cpo*'b::cpo)==>? x. range S<<| x";
by (cut_facts_tac prems 1);
by (rtac exI 1);
by (etac lub_cprod 1);
qed "cpo_cprod";


