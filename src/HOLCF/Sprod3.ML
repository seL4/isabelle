(*  Title:      HOLCF/Sprod3
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  ** for class pcpo
*)

(* for compatibility with old HOLCF-Version *)
val prems = goal thy "UU = Ispair UU UU";
by (simp_tac (HOL_ss addsimps [UU_def,UU_sprod_def]) 1);
qed "inst_sprod_pcpo";

Addsimps [inst_sprod_pcpo RS sym];

(* ------------------------------------------------------------------------ *)
(* continuity of Ispair, Isfst, Issnd                                       *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy 
"[| chain(Y);  x~= UU;  lub(range(Y))~= UU |] ==>\
\ Ispair (lub(range Y)) x =\
\ Ispair (lub(range(%i. Isfst(Ispair(Y i) x)))) \
\        (lub(range(%i. Issnd(Ispair(Y i) x))))";
by (cut_facts_tac prems 1);
by (res_inst_tac [("f1","Ispair")] (arg_cong RS cong) 1);
by (rtac lub_equal 1);
by (atac 1);
by (rtac (monofun_Isfst RS ch2ch_monofun) 1);
by (rtac ch2ch_fun 1);
by (rtac (monofun_Ispair1 RS ch2ch_monofun) 1);
by (atac 1);
by (rtac allI 1);
by (asm_simp_tac Sprod0_ss 1);
by (rtac sym 1);
by (rtac lub_chain_maxelem 1);
by (res_inst_tac [("P","%j.~Y(j)=UU")] exE 1);
by (rtac (not_all RS iffD1) 1);
by (res_inst_tac [("Q","lub(range(Y)) = UU")] contrapos 1);
by (atac 1);
by (rtac chain_UU_I_inverse 1);
by (atac 1);
by (rtac exI 1);
by (etac Issnd2 1);
by (rtac allI 1);
by (res_inst_tac [("Q","Y(i)=UU")] (excluded_middle RS disjE) 1);
by (asm_simp_tac Sprod0_ss 1);
by (rtac refl_less 1);
by (res_inst_tac [("s","UU"),("t","Y(i)")] subst 1);
by (etac sym 1);
by (asm_simp_tac Sprod0_ss  1);
by (rtac minimal 1);
qed "sprod3_lemma1";

val prems = goal thy 
"[| chain(Y); x ~= UU; lub(range(Y)) = UU |] ==>\
\   Ispair (lub(range Y)) x =\
\   Ispair (lub(range(%i. Isfst(Ispair(Y i) x))))\
\          (lub(range(%i. Issnd(Ispair(Y i) x))))";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","UU"),("t","lub(range(Y))")] ssubst 1);
by (atac 1);
by (rtac trans 1);
by (rtac strict_Ispair1 1);
by (rtac (strict_Ispair RS sym) 1);
by (rtac disjI1 1);
by (rtac chain_UU_I_inverse 1);
by (rtac allI 1);
by (asm_simp_tac Sprod0_ss  1);
by (etac (chain_UU_I RS spec) 1);
by (atac 1);
qed "sprod3_lemma2";


val prems = goal thy 
"[| chain(Y); x = UU |] ==>\
\          Ispair (lub(range Y)) x =\
\          Ispair (lub(range(%i. Isfst(Ispair (Y i) x))))\
\                 (lub(range(%i. Issnd(Ispair (Y i) x))))";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","UU"),("t","x")] ssubst 1);
by (atac 1);
by (rtac trans 1);
by (rtac strict_Ispair2 1);
by (rtac (strict_Ispair RS sym) 1);
by (rtac disjI1 1);
by (rtac chain_UU_I_inverse 1);
by (rtac allI 1);
by (simp_tac Sprod0_ss  1);
qed "sprod3_lemma3";

Goal "contlub(Ispair)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac (expand_fun_eq RS iffD2) 1);
by (strip_tac 1);
by (stac (lub_fun RS thelubI) 1);
by (etac (monofun_Ispair1 RS ch2ch_monofun) 1);
by (rtac trans 1);
by (rtac (thelub_sprod RS sym) 2);
by (rtac ch2ch_fun 2);
by (etac (monofun_Ispair1 RS ch2ch_monofun) 2);
by (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1);
by (res_inst_tac [("Q","lub(range(Y))=UU")] (excluded_middle RS disjE) 1);
by (etac sprod3_lemma1 1);
by (atac 1);
by (atac 1);
by (etac sprod3_lemma2 1);
by (atac 1);
by (atac 1);
by (etac sprod3_lemma3 1);
by (atac 1);
qed "contlub_Ispair1";

val prems = goal thy 
"[| chain(Y); x ~= UU; lub(range(Y)) ~= UU |] ==>\
\         Ispair x (lub(range Y)) =\
\         Ispair (lub(range(%i. Isfst (Ispair x (Y i)))))\
\                (lub(range(%i. Issnd (Ispair x (Y i)))))";
by (cut_facts_tac prems 1);
by (res_inst_tac [("f1","Ispair")] (arg_cong RS cong) 1);
by (rtac sym 1);
by (rtac lub_chain_maxelem 1);
by (res_inst_tac [("P","%j. Y(j)~=UU")] exE 1);
by (rtac (not_all RS iffD1) 1);
by (res_inst_tac [("Q","lub(range(Y)) = UU")] contrapos 1);
by (atac 1);
by (rtac chain_UU_I_inverse 1);
by (atac 1);
by (rtac exI 1);
by (etac Isfst2 1);
by (rtac allI 1);
by (res_inst_tac [("Q","Y(i)=UU")] (excluded_middle RS disjE) 1);
by (asm_simp_tac Sprod0_ss 1);
by (rtac refl_less 1);
by (res_inst_tac [("s","UU"),("t","Y(i)")] subst 1);
by (etac sym 1);
by (asm_simp_tac Sprod0_ss  1);
by (rtac minimal 1);
by (rtac lub_equal 1);
by (atac 1);
by (rtac (monofun_Issnd RS ch2ch_monofun) 1);
by (rtac (monofun_Ispair2 RS ch2ch_monofun) 1);
by (atac 1);
by (rtac allI 1);
by (asm_simp_tac Sprod0_ss 1);
qed "sprod3_lemma4";

val prems = goal thy 
"[| chain(Y); x ~= UU; lub(range(Y)) = UU |] ==>\
\         Ispair x (lub(range Y)) =\
\         Ispair (lub(range(%i. Isfst(Ispair x (Y i)))))\
\                (lub(range(%i. Issnd(Ispair x (Y i)))))";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","UU"),("t","lub(range(Y))")] ssubst 1);
by (atac 1);
by (rtac trans 1);
by (rtac strict_Ispair2 1);
by (rtac (strict_Ispair RS sym) 1);
by (rtac disjI2 1);
by (rtac chain_UU_I_inverse 1);
by (rtac allI 1);
by (asm_simp_tac Sprod0_ss  1);
by (etac (chain_UU_I RS spec) 1);
by (atac 1);
qed "sprod3_lemma5";

val prems = goal thy 
"[| chain(Y); x = UU |] ==>\
\         Ispair x (lub(range Y)) =\
\         Ispair (lub(range(%i. Isfst (Ispair x (Y i)))))\
\                (lub(range(%i. Issnd (Ispair x (Y i)))))";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","UU"),("t","x")] ssubst 1);
by (atac 1);
by (rtac trans 1);
by (rtac strict_Ispair1 1);
by (rtac (strict_Ispair RS sym) 1);
by (rtac disjI1 1);
by (rtac chain_UU_I_inverse 1);
by (rtac allI 1);
by (simp_tac Sprod0_ss  1);
qed "sprod3_lemma6";

val prems = goal thy "contlub(Ispair(x))";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_sprod RS sym) 2);
by (etac (monofun_Ispair2 RS ch2ch_monofun) 2);
by (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1);
by (res_inst_tac [("Q","lub(range(Y))=UU")] (excluded_middle RS disjE) 1);
by (etac sprod3_lemma4 1);
by (atac 1);
by (atac 1);
by (etac sprod3_lemma5 1);
by (atac 1);
by (atac 1);
by (etac sprod3_lemma6 1);
by (atac 1);
qed "contlub_Ispair2";

val prems = goal thy "cont(Ispair)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Ispair1 1);
by (rtac contlub_Ispair1 1);
qed "cont_Ispair1";


val prems = goal thy "cont(Ispair(x))";
by (rtac monocontlub2cont 1);
by (rtac monofun_Ispair2 1);
by (rtac contlub_Ispair2 1);
qed "cont_Ispair2";

val prems = goal thy "contlub(Isfst)";
by (rtac contlubI 1);
by (strip_tac 1);
by (stac (lub_sprod RS thelubI) 1);
by (atac 1);
by (res_inst_tac [("Q","lub(range(%i. Issnd(Y(i))))=UU")] (excluded_middle RS disjE) 1);
by (asm_simp_tac Sprod0_ss  1);
by (res_inst_tac [("s","UU"),("t","lub(range(%i. Issnd(Y(i))))")] ssubst 1);
by (atac 1);
by (rtac trans 1);
by (asm_simp_tac Sprod0_ss  1);
by (rtac sym 1);
by (rtac chain_UU_I_inverse 1);
by (rtac allI 1);
by (rtac strict_Isfst 1);
by (rtac swap 1);
by (etac (defined_IsfstIssnd RS conjunct2) 2);
by (fast_tac (HOL_cs addSDs [monofun_Issnd RS ch2ch_monofun RS chain_UU_I RS spec]) 1);
qed "contlub_Isfst";

val prems = goal thy "contlub(Issnd)";
by (rtac contlubI 1);
by (strip_tac 1);
by (stac (lub_sprod RS thelubI) 1);
by (atac 1);
by (res_inst_tac [("Q","lub(range(%i. Isfst(Y(i))))=UU")] (excluded_middle RS disjE) 1);
by (asm_simp_tac Sprod0_ss  1);
by (res_inst_tac [("s","UU"),("t","lub(range(%i. Isfst(Y(i))))")] ssubst 1);
by (atac 1);
by (asm_simp_tac Sprod0_ss  1);
by (rtac sym 1);
by (rtac chain_UU_I_inverse 1);
by (rtac allI 1);
by (rtac strict_Issnd 1);
by (rtac swap 1);
by (etac (defined_IsfstIssnd RS conjunct1) 2);
by (fast_tac (HOL_cs addSDs [monofun_Isfst RS ch2ch_monofun RS chain_UU_I RS spec]) 1);
qed "contlub_Issnd";

val prems = goal thy "cont(Isfst)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Isfst 1);
by (rtac contlub_Isfst 1);
qed "cont_Isfst";

val prems = goal thy "cont(Issnd)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Issnd 1);
by (rtac contlub_Issnd 1);
qed "cont_Issnd";

val prems = goal thy "[|x1=x2;y1=y2|] ==> (:x1,y1:) = (:x2,y2:)";
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
qed "spair_eq";

(* ------------------------------------------------------------------------ *)
(* convert all lemmas to the continuous versions                            *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [spair_def]
        "(LAM x y. Ispair x y)`a`b = Ispair a b";
by (stac beta_cfun 1);
by (simp_tac (simpset() addsimps [cont_Ispair2, cont_Ispair1, cont2cont_CF1L]) 1);
by (stac beta_cfun 1);
by (rtac cont_Ispair2 1);
by (rtac refl 1);
qed "beta_cfun_sprod";

Addsimps [beta_cfun_sprod];

val prems = goalw thy [spair_def]
        "[| aa~=UU ; ba~=UU ; (:a,b:)=(:aa,ba:) |] ==> a=aa & b=ba";
by (cut_facts_tac prems 1);
by (etac inject_Ispair 1);
by (atac 1);
by (etac box_equals 1);
by (rtac beta_cfun_sprod 1);
by (rtac beta_cfun_sprod 1);
qed "inject_spair";

val prems = goalw thy [spair_def] "UU = (:UU,UU:)";
by (rtac sym 1);
by (rtac trans 1);
by (rtac beta_cfun_sprod 1);
by (rtac sym 1);
by (rtac inst_sprod_pcpo 1);
qed "inst_sprod_pcpo2";

val prems = goalw thy [spair_def] 
        "(a=UU | b=UU) ==> (:a,b:)=UU";
by (cut_facts_tac prems 1);
by (rtac trans 1);
by (rtac beta_cfun_sprod 1);
by (rtac trans 1);
by (rtac (inst_sprod_pcpo RS sym) 2);
by (etac strict_Ispair 1);
qed "strict_spair";

val prems = goalw thy [spair_def] "(:UU,b:) = UU";
by (stac beta_cfun_sprod 1);
by (rtac trans 1);
by (rtac (inst_sprod_pcpo RS sym) 2);
by (rtac strict_Ispair1 1);
qed "strict_spair1";

val prems = goalw thy [spair_def] "(:a,UU:) = UU";
by (stac beta_cfun_sprod 1);
by (rtac trans 1);
by (rtac (inst_sprod_pcpo RS sym) 2);
by (rtac strict_Ispair2 1);
qed "strict_spair2";

Addsimps [strict_spair1,strict_spair2];

Goalw [spair_def] "(:x,y:)~=UU ==> ~x=UU & ~y=UU";
by (rtac strict_Ispair_rev 1);
by Auto_tac;  
qed "strict_spair_rev";

Goalw [spair_def] "(:a,b:) = UU ==> (a = UU | b = UU)";
by (rtac defined_Ispair_rev 1);
by Auto_tac;  
qed "defined_spair_rev";

val prems = goalw thy [spair_def]
        "[|a~=UU; b~=UU|] ==> (:a,b:) ~= UU";
by (cut_facts_tac prems 1);
by (stac beta_cfun_sprod 1);
by (stac inst_sprod_pcpo 1);
by (etac defined_Ispair 1);
by (atac 1);
qed "defined_spair";

val prems = goalw thy [spair_def]
        "z=UU | (? a b. z=(:a,b:) & a~=UU & b~=UU)";
by (rtac (Exh_Sprod RS disjE) 1);
by (rtac disjI1 1);
by (stac inst_sprod_pcpo 1);
by (atac 1);
by (rtac disjI2 1);
by (etac exE 1);
by (etac exE 1);
by (rtac exI 1);
by (rtac exI 1);
by (rtac conjI 1);
by (stac beta_cfun_sprod 1);
by (fast_tac HOL_cs 1);
by (fast_tac HOL_cs 1);
qed "Exh_Sprod2";


val [prem1,prem2] = Goalw [spair_def]
   "[|p=UU ==> Q;  !!x y. [| p=(:x,y:); x~=UU; y~=UU|] ==> Q|] ==> Q";
by (rtac IsprodE 1);
by (rtac prem1 1);
by (stac inst_sprod_pcpo 1);
by (atac 1);
by (rtac prem2 1);
by (atac 2);
by (atac 2);
by (stac beta_cfun_sprod 1);
by (atac 1);
qed "sprodE";


val prems = goalw thy [sfst_def] 
        "p=UU==>sfst`p=UU";
by (cut_facts_tac prems 1);
by (stac beta_cfun 1);
by (rtac cont_Isfst 1);
by (rtac strict_Isfst 1);
by (rtac (inst_sprod_pcpo RS subst) 1);
by (atac 1);
qed "strict_sfst";

val prems = goalw thy [sfst_def,spair_def] 
        "sfst`(:UU,y:) = UU";
by (stac beta_cfun_sprod 1);
by (stac beta_cfun 1);
by (rtac cont_Isfst 1);
by (rtac strict_Isfst1 1);
qed "strict_sfst1";
 
val prems = goalw thy [sfst_def,spair_def] 
        "sfst`(:x,UU:) = UU";
by (stac beta_cfun_sprod 1);
by (stac beta_cfun 1);
by (rtac cont_Isfst 1);
by (rtac strict_Isfst2 1);
qed "strict_sfst2";

val prems = goalw thy [ssnd_def] 
        "p=UU==>ssnd`p=UU";
by (cut_facts_tac prems 1);
by (stac beta_cfun 1);
by (rtac cont_Issnd 1);
by (rtac strict_Issnd 1);
by (rtac (inst_sprod_pcpo RS subst) 1);
by (atac 1);
qed "strict_ssnd";

val prems = goalw thy [ssnd_def,spair_def] 
        "ssnd`(:UU,y:) = UU";
by (stac beta_cfun_sprod 1);
by (stac beta_cfun 1);
by (rtac cont_Issnd 1);
by (rtac strict_Issnd1 1);
qed "strict_ssnd1";

val prems = goalw thy [ssnd_def,spair_def] 
        "ssnd`(:x,UU:) = UU";
by (stac beta_cfun_sprod 1);
by (stac beta_cfun 1);
by (rtac cont_Issnd 1);
by (rtac strict_Issnd2 1);
qed "strict_ssnd2";

val prems = goalw thy [sfst_def,spair_def] 
        "y~=UU ==>sfst`(:x,y:)=x";
by (cut_facts_tac prems 1);
by (stac beta_cfun_sprod 1);
by (stac beta_cfun 1);
by (rtac cont_Isfst 1);
by (etac Isfst2 1);
qed "sfst2";

val prems = goalw thy [ssnd_def,spair_def] 
        "x~=UU ==>ssnd`(:x,y:)=y";
by (cut_facts_tac prems 1);
by (stac beta_cfun_sprod 1);
by (stac beta_cfun 1);
by (rtac cont_Issnd 1);
by (etac Issnd2 1);
qed "ssnd2";


val prems = goalw thy [sfst_def,ssnd_def,spair_def]
        "p~=UU ==> sfst`p ~=UU & ssnd`p ~=UU";
by (cut_facts_tac prems 1);
by (stac beta_cfun 1);
by (rtac cont_Issnd 1);
by (stac beta_cfun 1);
by (rtac cont_Isfst 1);
by (rtac defined_IsfstIssnd 1);
by (rtac (inst_sprod_pcpo RS subst) 1);
by (atac 1);
qed "defined_sfstssnd";
 
val prems = goalw thy [sfst_def,ssnd_def,spair_def] "(:sfst`p , ssnd`p:) = p";
by (stac beta_cfun_sprod 1);
by (stac beta_cfun 1);
by (rtac cont_Issnd 1);
by (stac beta_cfun 1);
by (rtac cont_Isfst 1);
by (rtac (surjective_pairing_Sprod RS sym) 1);
qed "surjective_pairing_Sprod2";

val prems = goalw thy [sfst_def,ssnd_def,spair_def]
"[|chain(S)|] ==> range(S) <<| \
\ (: lub(range(%i. sfst`(S i))), lub(range(%i. ssnd`(S i))) :)";
by (cut_facts_tac prems 1);
by (stac beta_cfun_sprod 1);
by (stac (beta_cfun RS ext) 1);
by (rtac cont_Issnd 1);
by (stac (beta_cfun RS ext) 1);
by (rtac cont_Isfst 1);
by (rtac lub_sprod 1);
by (resolve_tac prems 1);
qed "lub_sprod2";


bind_thm ("thelub_sprod2", lub_sprod2 RS thelubI);
(*
 "chain ?S1 ==>
 lub (range ?S1) =
 (:lub (range (%i. sfst`(?S1 i))), lub (range (%i. ssnd`(?S1 i))):)" : thm
*)

val prems = goalw thy [ssplit_def]
        "ssplit`f`UU=UU";
by (stac beta_cfun 1);
by (Simp_tac 1);
by (stac strictify1 1);
by (rtac refl 1);
qed "ssplit1";

val prems = goalw thy [ssplit_def]
        "[|x~=UU;y~=UU|] ==> ssplit`f`(:x,y:)= f`x`y";
by (stac beta_cfun 1);
by (Simp_tac 1);
by (stac strictify2 1);
by (rtac defined_spair 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
by (stac beta_cfun 1);
by (Simp_tac 1);
by (stac sfst2 1);
by (resolve_tac prems 1);
by (stac ssnd2 1);
by (resolve_tac prems 1);
by (rtac refl 1);
qed "ssplit2";


val prems = goalw thy [ssplit_def]
  "ssplit`spair`z=z";
by (stac beta_cfun 1);
by (Simp_tac 1);
by (case_tac "z=UU" 1);
by (hyp_subst_tac 1);
by (rtac strictify1 1);
by (rtac trans 1);
by (rtac strictify2 1);
by (atac 1);
by (stac beta_cfun 1);
by (Simp_tac 1);
by (rtac surjective_pairing_Sprod2 1);
qed "ssplit3";

(* ------------------------------------------------------------------------ *)
(* install simplifier for Sprod                                             *)
(* ------------------------------------------------------------------------ *)

val Sprod_rews = [strict_sfst1,strict_sfst2,
                strict_ssnd1,strict_ssnd2,sfst2,ssnd2,defined_spair,
                ssplit1,ssplit2];
Addsimps Sprod_rews;

