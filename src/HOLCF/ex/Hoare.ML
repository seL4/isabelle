(*  Title:      HOLCF/ex/hoare.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

(* --------- pure HOLCF logic, some little lemmas ------ *)

Goal "b~=TT ==> b=FF | b=UU";
by (rtac (Exh_tr RS disjE) 1);
by (fast_tac HOL_cs 1);
by (etac disjE 1);
by (contr_tac 1);
by (fast_tac HOL_cs 1);
qed "hoare_lemma2";

Goal " (ALL k. b1$(iterate k g x) = TT) | (EX k. b1$(iterate k g x)~=TT)";
by (fast_tac HOL_cs 1);
qed "hoare_lemma3";

Goal "(EX k. b1$(iterate k g x) ~= TT) ==> \
\ EX k. b1$(iterate k g x) = FF | b1$(iterate k g x) = UU";
by (etac exE 1);
by (rtac exI 1);
by (rtac hoare_lemma2 1);
by (atac 1);
qed "hoare_lemma4";

Goal "[|(EX k. b1$(iterate k g x) ~= TT);\
\   k=Least(%n. b1$(iterate n g x) ~= TT)|] ==> \
\ b1$(iterate k g x)=FF | b1$(iterate k g x)=UU";
by (hyp_subst_tac 1);
by (rtac hoare_lemma2 1);
by (etac exE 1);
by (etac LeastI 1);
qed "hoare_lemma5";

Goal "b=UU ==> b~=TT";
by (hyp_subst_tac 1);
by (resolve_tac dist_eq_tr 1);
qed "hoare_lemma6";

Goal "b=FF ==> b~=TT";
by (hyp_subst_tac 1);
by (resolve_tac dist_eq_tr 1);
qed "hoare_lemma7";

Goal "[|(EX k. b1$(iterate k g x) ~= TT);\
\   k=Least(%n. b1$(iterate n g x) ~= TT)|] ==> \
\ ALL m. m < k --> b1$(iterate m g x)=TT";
by (hyp_subst_tac 1);
by (etac exE 1);
by (strip_tac 1);
by (res_inst_tac [("p","b1$(iterate m g x)")] trE 1);
by (atac 2);
by (rtac (le_less_trans RS less_irrefl) 1);
by (atac 2);
by (rtac Least_le 1);
by (etac hoare_lemma6 1);
by (rtac (le_less_trans RS less_irrefl) 1);
by (atac 2);
by (rtac Least_le 1);
by (etac hoare_lemma7 1);
qed "hoare_lemma8";


Goal "f$(y::'a)=(UU::tr) ==> f$UU = UU";
by (etac (flat_codom RS disjE) 1);
by Auto_tac;  
qed "hoare_lemma28";


(* ----- access to definitions ----- *)

Goal "p$x = If b1$x then p$(g$x) else x fi";
by (fix_tac3 p_def 1);
by (Simp_tac 1);
qed "p_def3";

Goal "q$x = If b1$x orelse b2$x then q$(g$x) else x fi";
by (fix_tac3 q_def 1);
by (Simp_tac 1);
qed "q_def3";

(** --------- proves about iterations of p and q ---------- **)

Goal "(ALL m. m< Suc k --> b1$(iterate m g x)=TT) -->\
\  p$(iterate k g x)=p$x";
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (strip_tac 1);
by (res_inst_tac [("s","p$(iterate k g x)")] trans 1);
by (rtac trans 1);
by (rtac (p_def3 RS sym) 2);
by (res_inst_tac [("s","TT"),("t","b1$(iterate k g x)")] ssubst 1);
by (rtac mp 1);
by (etac spec 1);
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (simp_tac HOLCF_ss 1);
by (etac mp 1);
by (strip_tac 1);
by (rtac mp 1);
by (etac spec 1);
by (etac less_trans 1);
by (Simp_tac 1);
qed "hoare_lemma9";

Goal "(ALL m. m< Suc k --> b1$(iterate m g x)=TT) --> \
\ q$(iterate k g x)=q$x";
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (strip_tac 1);
by (res_inst_tac [("s","q$(iterate k g x)")] trans 1);
by (rtac trans 1);
by (rtac (q_def3 RS sym) 2);
by (res_inst_tac [("s","TT"),("t","b1$(iterate k g x)")] ssubst 1);
by (fast_tac HOL_cs 1);
by (simp_tac HOLCF_ss 1);
by (etac mp 1);
by (strip_tac 1);
by (fast_tac (HOL_cs addSDs [less_Suc_eq RS iffD1]) 1);
qed "hoare_lemma24";

(* -------- results about p for case (EX k. b1$(iterate k g x)~=TT) ------- *)


val hoare_lemma10 = (hoare_lemma8 RS (hoare_lemma9 RS mp));
(* 
val hoare_lemma10 = "[| EX k. b1$(iterate k g ?x1) ~= TT;
    Suc ?k3 = Least(%n. b1$(iterate n g ?x1) ~= TT) |] ==>
 p$(iterate ?k3 g ?x1) = p$?x1" : thm

*)

Goal "(EX n. b1$(iterate n g x) ~= TT) ==>\
\ k=(LEAST n. b1$(iterate n g x) ~= TT) & b1$(iterate k g x)=FF \
\ --> p$x = iterate k g x";
by (case_tac "k" 1);
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (rtac trans 1);
by (rtac p_def3 1);
by (asm_simp_tac HOLCF_ss 1);
by (hyp_subst_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (rtac trans 1);
by (etac (hoare_lemma10 RS sym) 1);
by (atac 1);
by (rtac trans 1);
by (rtac p_def3 1);
by (res_inst_tac [("s","TT"),("t","b1$(iterate nat g x)")] ssubst 1);
by (rtac (hoare_lemma8 RS spec RS mp) 1);
by (atac 1);
by (atac 1);
by (Simp_tac 1);
by (simp_tac HOLCF_ss 1);
by (rtac trans 1);
by (rtac p_def3 1);
by (simp_tac (simpset() delsimps [iterate_Suc] addsimps [iterate_Suc RS sym]) 1);
by (eres_inst_tac [("s","FF")] ssubst 1);
by (simp_tac HOLCF_ss 1);
qed "hoare_lemma11";

Goal "(EX n. b1$(iterate n g x) ~= TT) ==>\
\ k=Least(%n. b1$(iterate n g x)~=TT) & b1$(iterate k g x)=UU \
\ --> p$x = UU";
by (case_tac "k" 1);
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (rtac trans 1);
by (rtac p_def3 1);
by (asm_simp_tac HOLCF_ss 1);
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (rtac trans 1);
by (rtac (hoare_lemma10 RS sym) 1);
by (atac 1);
by (atac 1);
by (rtac trans 1);
by (rtac p_def3 1);
by (res_inst_tac [("s","TT"),("t","b1$(iterate nat g x)")] ssubst 1);
by (rtac (hoare_lemma8 RS spec RS mp) 1);
by (atac 1);
by (atac 1);
by (Simp_tac 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac trans 1);
by (rtac p_def3 1);
by (asm_simp_tac HOLCF_ss 1);
qed "hoare_lemma12";

(* -------- results about p for case  (ALL k. b1$(iterate k g x)=TT) ------- *)

Goal "(ALL k. b1$(iterate k g x)=TT) ==> ALL k. p$(iterate k g x) = UU";
by (rtac (p_def RS def_fix_ind) 1);
by (rtac adm_all 1);
by (rtac allI 1);
by (rtac adm_eq 1);
by (cont_tacR 1);
by (rtac allI 1);
by (stac strict_Rep_CFun1 1);
by (rtac refl 1);
by (Simp_tac 1);
by (rtac allI 1);
by (res_inst_tac [("s","TT"),("t","b1$(iterate k g x)")] ssubst 1);
by (etac spec 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac (iterate_Suc RS subst) 1);
by (etac spec 1);
qed "fernpass_lemma";

Goal "(ALL k. b1$(iterate k g x)=TT) ==> p$x = UU";
by (res_inst_tac [("F1","g"),("t","x")] (iterate_0 RS subst) 1);
by (etac (fernpass_lemma RS spec) 1);
qed "hoare_lemma16";

(* -------- results about q for case  (ALL k. b1$(iterate k g x)=TT) ------- *)

Goal "(ALL k. b1$(iterate k g x)=TT) ==> ALL k. q$(iterate k g x) = UU";
by (rtac (q_def RS def_fix_ind) 1);
by (rtac adm_all 1);
by (rtac allI 1);
by (rtac adm_eq 1);
by (cont_tacR 1);
by (rtac allI 1);
by (stac strict_Rep_CFun1 1);
by (rtac refl 1);
by (rtac allI 1);
by (Simp_tac 1);
by (res_inst_tac [("s","TT"),("t","b1$(iterate k g x)")] ssubst 1);
by (etac spec 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac (iterate_Suc RS subst) 1);
by (etac spec 1);
qed "hoare_lemma17";

Goal "(ALL k. b1$(iterate k g x)=TT) ==> q$x = UU";
by (res_inst_tac [("F1","g"),("t","x")] (iterate_0 RS subst) 1);
by (etac (hoare_lemma17 RS spec) 1);
qed "hoare_lemma18";

Goal "(ALL k. (b1::'a->tr)$(iterate k g x)=TT) ==> b1$(UU::'a) = UU | (ALL y. b1$(y::'a)=TT)";
by (rtac (flat_codom) 1);
by (res_inst_tac [("t","x1")] (iterate_0 RS subst) 1);
by (etac spec 1);
qed "hoare_lemma19";

Goal "(ALL y. b1$(y::'a)=TT) ==> ALL k. q$(iterate k g (x::'a)) = UU";
by (rtac (q_def RS def_fix_ind) 1);
by (rtac adm_all 1);
by (rtac allI 1);
by (rtac adm_eq 1);
by (cont_tacR 1);
by (rtac allI 1);
by (stac strict_Rep_CFun1 1);
by (rtac refl 1);
by (rtac allI 1);
by (Simp_tac 1);
by (res_inst_tac [("s","TT"),("t","b1$(iterate k g (x::'a))")] ssubst 1);
by (etac spec 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac (iterate_Suc RS subst) 1);
by (etac spec 1);
qed "hoare_lemma20";

Goal "(ALL y. b1$(y::'a)=TT) ==> q$(x::'a) = UU";
by (res_inst_tac [("F1","g"),("t","x")] (iterate_0 RS subst) 1);
by (etac (hoare_lemma20 RS spec) 1);
qed "hoare_lemma21";

Goal "b1$(UU::'a)=UU ==> q$(UU::'a) = UU";
by (stac q_def3 1);
by (asm_simp_tac HOLCF_ss 1);
qed "hoare_lemma22";

(* -------- results about q for case (EX k. b1$(iterate k g x) ~= TT) ------- *)

val hoare_lemma25 = (hoare_lemma8 RS (hoare_lemma24 RS mp) );
(* 
val hoare_lemma25 = "[| EX k. b1$(iterate k g ?x1) ~= TT;
    Suc ?k3 = Least(%n. b1$(iterate n g ?x1) ~= TT) |] ==>
 q$(iterate ?k3 g ?x1) = q$?x1" : thm
*)

Goal "(EX n. b1$(iterate n g x)~=TT) ==>\
\ k=Least(%n. b1$(iterate n g x) ~= TT) & b1$(iterate k g x) =FF \
\ --> q$x = q$(iterate k g x)";
by (case_tac "k" 1);
by (hyp_subst_tac 1);
by (strip_tac 1);
by (Simp_tac 1);
by (hyp_subst_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (rtac trans 1);
by (rtac (hoare_lemma25 RS sym) 1);
by (atac 1);
by (atac 1);
by (rtac trans 1);
by (rtac q_def3 1);
by (res_inst_tac [("s","TT"),("t","b1$(iterate nat g x)")] ssubst 1);
by (rtac (hoare_lemma8 RS spec RS mp) 1);
by (atac 1);
by (atac 1);
by (Simp_tac 1);
by (simp_tac HOLCF_ss 1);
qed "hoare_lemma26";


Goal "(EX n. b1$(iterate n g x) ~= TT) ==>\
\ k=Least(%n. b1$(iterate n g x)~=TT) & b1$(iterate k g x)=UU \
\ --> q$x = UU";
by (case_tac "k" 1);
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (stac q_def3 1);
by (asm_simp_tac HOLCF_ss 1);
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (rtac trans 1);
by (rtac (hoare_lemma25 RS sym) 1);
by (atac 1);
by (atac 1);
by (rtac trans 1);
by (rtac q_def3 1);
by (res_inst_tac [("s","TT"),("t","b1$(iterate nat g x)")] ssubst 1);
by (rtac (hoare_lemma8 RS spec RS mp) 1);
by (atac 1);
by (atac 1);
by (Simp_tac 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac trans 1);
by (rtac q_def3 1);
by (asm_simp_tac HOLCF_ss 1);
qed "hoare_lemma27";

(* ------- (ALL k. b1$(iterate k g x)=TT) ==> q o p = q   ----- *)

Goal "(ALL k. b1$(iterate k g x)=TT) ==> q$(p$x) = q$x";
by (stac hoare_lemma16 1);
by (atac 1);
by (rtac (hoare_lemma19 RS disjE) 1);
by (atac 1);
by (stac hoare_lemma18 1);
by (atac 1);
by (stac hoare_lemma22 1);
by (atac 1);
by (rtac refl 1);
by (stac hoare_lemma21 1);
by (atac 1);
by (stac hoare_lemma21 1);
by (atac 1);
by (rtac refl 1);
qed "hoare_lemma23";

(* ------------  EX k. b1~(iterate k g x) ~= TT ==> q o p = q   ----- *)

Goal "EX k. b1$(iterate k g x) ~= TT ==> q$(p$x) = q$x";
by (rtac (hoare_lemma5 RS disjE) 1);
by (atac 1);
by (rtac refl 1);
by (stac (hoare_lemma11 RS mp) 1);
by (atac 1);
by (rtac conjI 1);
by (rtac refl 1);
by (atac 1);
by (rtac (hoare_lemma26 RS mp RS subst) 1);
by (atac 1);
by (rtac conjI 1);
by (rtac refl 1);
by (atac 1);
by (rtac refl 1);
by (stac (hoare_lemma12 RS mp) 1);
by (atac 1);
by (rtac conjI 1);
by (rtac refl 1);
by (atac 1);
by (stac hoare_lemma22 1);
by (stac hoare_lemma28 1);
by (atac 1);
by (rtac refl 1);
by (rtac sym 1);
by (stac (hoare_lemma27 RS mp) 1);
by (atac 1);
by (rtac conjI 1);
by (rtac refl 1);
by (atac 1);
by (rtac refl 1);
qed "hoare_lemma29";

(* ------ the main prove q o p = q ------ *)

Goal "q oo p = q";
by (rtac ext_cfun 1);
by (stac cfcomp2 1);
by (rtac (hoare_lemma3 RS disjE) 1);
by (etac hoare_lemma23 1);
by (etac hoare_lemma29 1);
qed "hoare_main";


