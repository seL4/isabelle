(*  Title:      HOLCF/Cprod2
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance *::(pcpo,pcpo)po
*)

(* for compatibility with old HOLCF-Version *)
Goal "(op <<)=(%x y. fst x<<fst y & snd x<<snd y)";
by (fold_goals_tac [less_cprod_def]);
by (rtac refl 1);
qed "inst_cprod_po";

Goal "(x1,y1) << (x2,y2) ==> x1 << x2 & y1 << y2";
by (asm_full_simp_tac (simpset() addsimps [inst_cprod_po]) 1);
qed "less_cprod4c";

(* ------------------------------------------------------------------------ *)
(* type cprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

Goal  "(UU,UU)<<p";
by (simp_tac(simpset() addsimps[inst_cprod_po])1);
qed "minimal_cprod";

bind_thm ("UU_cprod_def",minimal_cprod RS minimal2UU RS sym);

Goal "EX x::'a*'b. ALL y. x<<y";
by (res_inst_tac [("x","(UU,UU)")] exI 1);
by (rtac (minimal_cprod RS allI) 1);
qed "least_cprod";

(* ------------------------------------------------------------------------ *)
(* Pair <_,_>  is monotone in both arguments                                *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun]  "monofun Pair";
by (strip_tac 1);
by (rtac (less_fun RS iffD2) 1);
by (strip_tac 1);
by (asm_simp_tac (simpset() addsimps [inst_cprod_po]) 1);
qed "monofun_pair1";

Goalw [monofun]  "monofun(Pair x)";
by (asm_simp_tac (simpset() addsimps [inst_cprod_po]) 1);
qed "monofun_pair2";

Goal "[|x1<<x2; y1<<y2|] ==> (x1::'a::cpo,y1::'b::cpo)<<(x2,y2)";
by (rtac trans_less 1);
by (rtac (monofun_pair1 RS monofunE RS spec RS spec RS mp RS (less_fun RS iffD1 RS spec)) 1);
by (rtac (monofun_pair2 RS monofunE RS spec RS spec RS mp) 2);
by (atac 1);
by (atac 1);
qed "monofun_pair";

(* ------------------------------------------------------------------------ *)
(* fst and snd are monotone                                                 *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun]  "monofun fst";
by (strip_tac 1);
by (res_inst_tac [("p","x")] PairE 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","y")] PairE 1);
by (hyp_subst_tac 1);
by (Asm_simp_tac  1);
by (etac (less_cprod4c RS conjunct1) 1);
qed "monofun_fst";

Goalw [monofun]  "monofun snd";
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

Goal 
"chain S ==> range S<<|(lub(range(%i. fst(S i))),lub(range(%i. snd(S i))))";
by (rtac (is_lubI) 1);
by (rtac (ub_rangeI) 1);
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

Goal "chain(S::nat=>'a::cpo*'b::cpo)==>EX x. range S<<| x";
by (rtac exI 1);
by (etac lub_cprod 1);
qed "cpo_cprod";


