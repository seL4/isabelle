(*  Title:      HOLCF/Sprod0
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Strict product with typedef.
*)

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Sprod                                         *)
(* ------------------------------------------------------------------------ *)

Goalw [Sprod_def] "(Spair_Rep a b):Sprod";
by (EVERY1 [rtac CollectI, rtac exI,rtac exI, rtac refl]);
qed "SprodI";

Goal "inj_on Abs_Sprod Sprod";
by (rtac inj_on_inverseI 1);
by (etac Abs_Sprod_inverse 1);
qed "inj_on_Abs_Sprod";

(* ------------------------------------------------------------------------ *)
(* Strictness and definedness of Spair_Rep                                  *)
(* ------------------------------------------------------------------------ *)

Goalw [Spair_Rep_def]
 "(a=UU | b=UU) ==> (Spair_Rep a b) = (Spair_Rep UU UU)";
by (rtac ext 1);
by (rtac ext 1);
by (rtac iffI 1);
by (fast_tac HOL_cs 1);
by (fast_tac HOL_cs 1);
qed "strict_Spair_Rep";

Goalw [Spair_Rep_def]
 "(Spair_Rep a b) = (Spair_Rep UU UU) ==> (a=UU | b=UU)";
by (case_tac "a=UU|b=UU" 1);
by (atac 1);
by (fast_tac (claset() addDs [fun_cong]) 1);
qed "defined_Spair_Rep_rev";

(* ------------------------------------------------------------------------ *)
(* injectivity of Spair_Rep and Ispair                                      *)
(* ------------------------------------------------------------------------ *)

Goalw [Spair_Rep_def]
"[|~aa=UU ; ~ba=UU ; Spair_Rep a b = Spair_Rep aa ba |] ==> a=aa & b=ba";
by (dtac fun_cong 1);
by (dtac fun_cong 1);
by (etac (iffD1 RS mp) 1);
by Auto_tac;  
qed "inject_Spair_Rep";


Goalw [Ispair_def]
        "[|~aa=UU ; ~ba=UU ; Ispair a b = Ispair aa ba |] ==> a=aa & b=ba";
by (etac inject_Spair_Rep 1);
by (atac 1);
by (etac (inj_on_Abs_Sprod  RS inj_onD) 1);
by (rtac SprodI 1);
by (rtac SprodI 1);
qed "inject_Ispair";


(* ------------------------------------------------------------------------ *)
(* strictness and definedness of Ispair                                     *)
(* ------------------------------------------------------------------------ *)

Goalw [Ispair_def] 
 "(a=UU | b=UU) ==> Ispair a b = Ispair UU UU";
by (etac (strict_Spair_Rep RS arg_cong) 1);
qed "strict_Ispair";

Goalw [Ispair_def]
        "Ispair UU b  = Ispair UU UU";
by (rtac (strict_Spair_Rep RS arg_cong) 1);
by (rtac disjI1 1);
by (rtac refl 1);
qed "strict_Ispair1";

Goalw [Ispair_def]
        "Ispair a UU = Ispair UU UU";
by (rtac (strict_Spair_Rep RS arg_cong) 1);
by (rtac disjI2 1);
by (rtac refl 1);
qed "strict_Ispair2";

Goal "~Ispair x y = Ispair UU UU ==> ~x=UU & ~y=UU";
by (rtac (de_Morgan_disj RS subst) 1);
by (etac contrapos 1);
by (etac strict_Ispair 1);
qed "strict_Ispair_rev";

Goalw [Ispair_def]
        "Ispair a b  = Ispair UU UU ==> (a = UU | b = UU)";
by (rtac defined_Spair_Rep_rev 1);
by (rtac (inj_on_Abs_Sprod  RS inj_onD) 1);
by (atac 1);
by (rtac SprodI 1);
by (rtac SprodI 1);
qed "defined_Ispair_rev";

Goal "[|a~=UU; b~=UU|] ==> (Ispair a b) ~= (Ispair UU UU)";
by (rtac contrapos 1);
by (etac defined_Ispair_rev 2);
by (rtac (de_Morgan_disj RS iffD2) 1);
by (etac conjI 1);
by (atac 1);
qed "defined_Ispair";


(* ------------------------------------------------------------------------ *)
(* Exhaustion of the strict product **                                      *)
(* ------------------------------------------------------------------------ *)

Goalw [Ispair_def]
        "z=Ispair UU UU | (? a b. z=Ispair a b & a~=UU & b~=UU)";
by (rtac (rewrite_rule [Sprod_def] Rep_Sprod RS CollectE) 1);
by (etac exE 1);
by (etac exE 1);
by (rtac (excluded_middle RS disjE) 1);
by (rtac disjI2 1);
by (rtac exI 1);
by (rtac exI 1);
by (rtac conjI 1);
by (rtac (Rep_Sprod_inverse RS sym RS trans) 1);
by (etac arg_cong 1);
by (rtac (de_Morgan_disj RS subst) 1);
by (atac 1);
by (rtac disjI1 1);
by (rtac (Rep_Sprod_inverse RS sym RS trans) 1);
by (res_inst_tac [("f","Abs_Sprod")] arg_cong 1);
by (etac trans 1);
by (etac strict_Spair_Rep 1);
qed "Exh_Sprod";

(* ------------------------------------------------------------------------ *)
(* general elimination rule for strict product                              *)
(* ------------------------------------------------------------------------ *)

val [prem1,prem2] = Goal
"  [| p=Ispair UU UU ==> Q ; !!x y. [|p=Ispair x y; x~=UU ; y~=UU|] ==> Q|] \
\  ==> Q";
by (rtac (Exh_Sprod RS disjE) 1);
by (etac prem1 1);
by (etac exE 1);
by (etac exE 1);
by (etac conjE 1);
by (etac conjE 1);
by (etac prem2 1);
by (atac 1);
by (atac 1);
qed "IsprodE";


(* ------------------------------------------------------------------------ *)
(* some results about the selectors Isfst, Issnd                            *)
(* ------------------------------------------------------------------------ *)

Goalw [Isfst_def] "p=Ispair UU UU ==> Isfst p = UU";
by (rtac some_equality 1);
by (rtac conjI 1);
by (fast_tac HOL_cs  1);
by (strip_tac 1);
by (res_inst_tac [("P","Ispair UU UU = Ispair a b")] notE 1);
by (rtac not_sym 1);
by (rtac defined_Ispair 1);
by (REPEAT (fast_tac HOL_cs  1));
qed "strict_Isfst";


Goal "Isfst(Ispair UU y) = UU";
by (stac strict_Ispair1 1);
by (rtac strict_Isfst 1);
by (rtac refl 1);
qed "strict_Isfst1";

Addsimps [strict_Isfst1];

Goal "Isfst(Ispair x UU) = UU";
by (stac strict_Ispair2 1);
by (rtac strict_Isfst 1);
by (rtac refl 1);
qed "strict_Isfst2";

Addsimps [strict_Isfst2];


Goalw [Issnd_def] "p=Ispair UU UU ==>Issnd p=UU";
by (rtac some_equality 1);
by (rtac conjI 1);
by (fast_tac HOL_cs  1);
by (strip_tac 1);
by (res_inst_tac [("P","Ispair UU UU = Ispair a b")] notE 1);
by (rtac not_sym 1);
by (rtac defined_Ispair 1);
by (REPEAT (fast_tac HOL_cs  1));
qed "strict_Issnd";

Goal "Issnd(Ispair UU y) = UU";
by (stac strict_Ispair1 1);
by (rtac strict_Issnd 1);
by (rtac refl 1);
qed "strict_Issnd1";

Addsimps [strict_Issnd1];

Goal "Issnd(Ispair x UU) = UU";
by (stac strict_Ispair2 1);
by (rtac strict_Issnd 1);
by (rtac refl 1);
qed "strict_Issnd2";

Addsimps [strict_Issnd2];

Goalw [Isfst_def] "[|x~=UU ;y~=UU |] ==> Isfst(Ispair x y) = x";
by (rtac some_equality 1);
by (rtac conjI 1);
by (strip_tac 1);
by (res_inst_tac [("P","Ispair x y = Ispair UU UU")] notE 1);
by (etac defined_Ispair 1);
by (atac 1);
by (atac 1);
by (strip_tac 1);
by (rtac (inject_Ispair RS conjunct1) 1);
by (fast_tac HOL_cs  3);
by (fast_tac HOL_cs  1);
by (fast_tac HOL_cs  1);
by (fast_tac HOL_cs  1);
qed "Isfst";

Goalw [Issnd_def] "[|x~=UU ;y~=UU |] ==> Issnd(Ispair x y) = y";
by (rtac some_equality 1);
by (rtac conjI 1);
by (strip_tac 1);
by (res_inst_tac [("P","Ispair x y = Ispair UU UU")] notE 1);
by (etac defined_Ispair 1);
by (atac 1);
by (atac 1);
by (strip_tac 1);
by (rtac (inject_Ispair RS conjunct2) 1);
by (fast_tac HOL_cs  3);
by (fast_tac HOL_cs  1);
by (fast_tac HOL_cs  1);
by (fast_tac HOL_cs  1);
qed "Issnd";

Goal "y~=UU ==>Isfst(Ispair x y)=x";
by (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1);
by (etac Isfst 1);
by (atac 1);
by (hyp_subst_tac 1);
by (rtac strict_Isfst1 1);
qed "Isfst2";

Goal "~x=UU ==>Issnd(Ispair x y)=y";
by (res_inst_tac [("Q","y=UU")] (excluded_middle RS disjE) 1);
by (etac Issnd 1);
by (atac 1);
by (hyp_subst_tac 1);
by (rtac strict_Issnd2 1);
qed "Issnd2";


(* ------------------------------------------------------------------------ *)
(* instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

val Sprod0_ss = 
        HOL_ss 
        addsimps [strict_Isfst1,strict_Isfst2,strict_Issnd1,strict_Issnd2,
                 Isfst2,Issnd2];

Addsimps [Isfst2,Issnd2];

Goal "p~=Ispair UU UU ==> Isfst p ~= UU & Issnd p ~= UU";
by (res_inst_tac [("p","p")] IsprodE 1);
by (contr_tac 1);
by (hyp_subst_tac 1);
by (rtac conjI 1);
by (asm_simp_tac Sprod0_ss 1);
by (asm_simp_tac Sprod0_ss 1);
qed "defined_IsfstIssnd";


(* ------------------------------------------------------------------------ *)
(* Surjective pairing: equivalent to Exh_Sprod                              *)
(* ------------------------------------------------------------------------ *)

Goal "z = Ispair(Isfst z)(Issnd z)";
by (res_inst_tac [("z1","z")] (Exh_Sprod RS disjE) 1);
by (asm_simp_tac Sprod0_ss 1);
by (etac exE 1);
by (etac exE 1);
by (asm_simp_tac Sprod0_ss 1);
qed "surjective_pairing_Sprod";

Goal "[|Isfst x = Isfst y; Issnd x = Issnd y|] ==> x = y";
by (subgoal_tac "Ispair(Isfst x)(Issnd x)=Ispair(Isfst y)(Issnd y)" 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac(HOL_ss addsimps[surjective_pairing_Sprod RS sym])1);
by (Asm_simp_tac 1);
qed "Sel_injective_Sprod";
