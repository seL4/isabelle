(*  Title:      HOLCF/Sprod2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance **::(pcpo,pcpo)po
*)

(* for compatibility with old HOLCF-Version *)
Goal "(op <<)=(%x y. Isfst x<<Isfst y&Issnd x<<Issnd y)";
by (fold_goals_tac [less_sprod_def]);
by (rtac refl 1);
qed "inst_sprod_po";

(* ------------------------------------------------------------------------ *)
(* type sprod is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

Goal "Ispair UU UU << p";
by (simp_tac(Sprod0_ss addsimps[inst_sprod_po,minimal])1);
qed "minimal_sprod";

bind_thm ("UU_sprod_def",minimal_sprod RS minimal2UU RS sym);

Goal "? x::'a**'b.!y. x<<y";
by (res_inst_tac [("x","Ispair UU UU")] exI 1);
by (rtac (minimal_sprod RS allI) 1);
qed "least_sprod";

(* ------------------------------------------------------------------------ *)
(* Ispair is monotone in both arguments                                     *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun]  "monofun(Ispair)";
by (strip_tac 1);
by (rtac (less_fun RS iffD2) 1);
by (strip_tac 1);
by (res_inst_tac [("Q","xa=UU")] (excluded_middle RS disjE) 1);
by (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1);
by (ftac notUU_I 1);
by (atac 1);
by (REPEAT(asm_simp_tac(Sprod0_ss addsimps[inst_sprod_po,refl_less,minimal]) 1));
qed "monofun_Ispair1";

Goalw [monofun]  "monofun(Ispair(x))";
by (strip_tac 1);
by (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1);
by (res_inst_tac [("Q","xa=UU")] (excluded_middle RS disjE) 1);
by (ftac notUU_I 1);
by (atac 1);
by (REPEAT(asm_simp_tac(Sprod0_ss addsimps[inst_sprod_po,refl_less,minimal]) 1));
qed "monofun_Ispair2";      

Goal "[|x1<<x2; y1<<y2|] ==> Ispair x1 y1 << Ispair x2 y2";
by (rtac trans_less 1);
by (rtac (monofun_Ispair1 RS monofunE RS spec RS spec RS mp RS 
        (less_fun RS iffD1 RS spec)) 1);
by (rtac (monofun_Ispair2 RS monofunE RS spec RS spec RS mp) 2);
by (atac 1);
by (atac 1);
qed "monofun_Ispair";

(* ------------------------------------------------------------------------ *)
(* Isfst and Issnd are monotone                                             *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun]  "monofun(Isfst)";
by (simp_tac (HOL_ss addsimps [inst_sprod_po]) 1);
qed "monofun_Isfst";

Goalw [monofun]  "monofun(Issnd)";
by (simp_tac (HOL_ss addsimps [inst_sprod_po]) 1);
qed "monofun_Issnd";

(* ------------------------------------------------------------------------ *)
(* the type 'a ** 'b is a cpo                                               *)
(* ------------------------------------------------------------------------ *)

Goal 
"[|chain(S)|] ==> range(S) <<| \
\ Ispair (lub(range(%i. Isfst(S i)))) (lub(range(%i. Issnd(S i))))";
by (rtac (is_lubI) 1);
by (rtac (ub_rangeI) 1);
by (res_inst_tac [("t","S(i)")] (surjective_pairing_Sprod RS ssubst) 1);
by (rtac monofun_Ispair 1);
by (rtac is_ub_thelub 1);
by (etac (monofun_Isfst RS ch2ch_monofun) 1);
by (rtac is_ub_thelub 1);
by (etac (monofun_Issnd RS ch2ch_monofun) 1);
by (strip_tac 1);
by (res_inst_tac [("t","u")] (surjective_pairing_Sprod RS ssubst) 1);
by (rtac monofun_Ispair 1);
by (rtac is_lub_thelub 1);
by (etac (monofun_Isfst RS ch2ch_monofun) 1);
by (etac (monofun_Isfst RS ub2ub_monofun) 1);
by (rtac is_lub_thelub 1);
by (etac (monofun_Issnd RS ch2ch_monofun) 1);
by (etac (monofun_Issnd RS ub2ub_monofun) 1);
qed "lub_sprod";

bind_thm ("thelub_sprod", lub_sprod RS thelubI);


Goal "chain(S::nat=>'a**'b)==>? x. range(S)<<| x";
by (rtac exI 1);
by (etac lub_sprod 1);
qed "cpo_sprod";
