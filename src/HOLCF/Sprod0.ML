(*  Title:      HOLCF/sprod0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for theory sprod0.thy
*)

open Sprod0;

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Sprod                                         *)
(* ------------------------------------------------------------------------ *)

qed_goalw "SprodI" Sprod0.thy [Sprod_def]
        "(Spair_Rep a b):Sprod"
(fn prems =>
        [
        (EVERY1 [rtac CollectI, rtac exI,rtac exI, rtac refl])
        ]);

qed_goal "inj_onto_Abs_Sprod" Sprod0.thy 
        "inj_onto Abs_Sprod Sprod"
(fn prems =>
        [
        (rtac inj_onto_inverseI 1),
        (etac Abs_Sprod_inverse 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Strictness and definedness of Spair_Rep                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "strict_Spair_Rep" Sprod0.thy [Spair_Rep_def]
 "(a=UU | b=UU) ==> (Spair_Rep a b) = (Spair_Rep UU UU)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac ext 1),
        (rtac ext 1),
        (rtac iffI 1),
        (fast_tac HOL_cs 1),
        (fast_tac HOL_cs 1)
        ]);

qed_goalw "defined_Spair_Rep_rev" Sprod0.thy [Spair_Rep_def]
 "(Spair_Rep a b) = (Spair_Rep UU UU) ==> (a=UU | b=UU)"
 (fn prems =>
        [
        (case_tac "a=UU|b=UU" 1),
        (atac 1),
        (rtac disjI1 1),
        (rtac ((hd prems) RS fun_cong RS fun_cong RS iffD2 RS mp RS 
        conjunct1 RS sym) 1),
        (fast_tac HOL_cs 1),
        (fast_tac HOL_cs 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* injectivity of Spair_Rep and Ispair                                      *)
(* ------------------------------------------------------------------------ *)

qed_goalw "inject_Spair_Rep" Sprod0.thy [Spair_Rep_def]
"[|~aa=UU ; ~ba=UU ; Spair_Rep a b = Spair_Rep aa ba |] ==> a=aa & b=ba"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac ((nth_elem (2,prems)) RS fun_cong  RS fun_cong 
                RS iffD1 RS mp) 1),
        (fast_tac HOL_cs 1),
        (fast_tac HOL_cs 1)
        ]);


qed_goalw "inject_Ispair" Sprod0.thy [Ispair_def]
        "[|~aa=UU ; ~ba=UU ; Ispair a b = Ispair aa ba |] ==> a=aa & b=ba"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac inject_Spair_Rep 1),
        (atac 1),
        (etac (inj_onto_Abs_Sprod  RS inj_ontoD) 1),
        (rtac SprodI 1),
        (rtac SprodI 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* strictness and definedness of Ispair                                     *)
(* ------------------------------------------------------------------------ *)

qed_goalw "strict_Ispair" Sprod0.thy [Ispair_def] 
 "(a=UU | b=UU) ==> Ispair a b = Ispair UU UU"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac (strict_Spair_Rep RS arg_cong) 1)
        ]);

qed_goalw "strict_Ispair1" Sprod0.thy [Ispair_def]
        "Ispair UU b  = Ispair UU UU"
(fn prems =>
        [
        (rtac (strict_Spair_Rep RS arg_cong) 1),
        (rtac disjI1 1),
        (rtac refl 1)
        ]);

qed_goalw "strict_Ispair2" Sprod0.thy [Ispair_def]
        "Ispair a UU = Ispair UU UU"
(fn prems =>
        [
        (rtac (strict_Spair_Rep RS arg_cong) 1),
        (rtac disjI2 1),
        (rtac refl 1)
        ]);

qed_goal "strict_Ispair_rev" Sprod0.thy 
        "~Ispair x y = Ispair UU UU ==> ~x=UU & ~y=UU"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (de_Morgan_disj RS subst) 1),
        (etac contrapos 1),
        (etac strict_Ispair 1)
        ]);

qed_goalw "defined_Ispair_rev" Sprod0.thy [Ispair_def]
        "Ispair a b  = Ispair UU UU ==> (a = UU | b = UU)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac defined_Spair_Rep_rev 1),
        (rtac (inj_onto_Abs_Sprod  RS inj_ontoD) 1),
        (atac 1),
        (rtac SprodI 1),
        (rtac SprodI 1)
        ]);

qed_goal "defined_Ispair" Sprod0.thy  
"[|a~=UU; b~=UU|] ==> (Ispair a b) ~= (Ispair UU UU)" 
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac contrapos 1),
        (etac defined_Ispair_rev 2),
        (rtac (de_Morgan_disj RS iffD2) 1),
        (etac conjI 1),
        (atac 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Exhaustion of the strict product **                                      *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Exh_Sprod" Sprod0.thy [Ispair_def]
        "z=Ispair UU UU | (? a b. z=Ispair a b & a~=UU & b~=UU)"
(fn prems =>
        [
        (rtac (rewrite_rule [Sprod_def] Rep_Sprod RS CollectE) 1),
        (etac exE 1),
        (etac exE 1),
        (rtac (excluded_middle RS disjE) 1),
        (rtac disjI2 1),
        (rtac exI 1),
        (rtac exI 1),
        (rtac conjI 1),
        (rtac (Rep_Sprod_inverse RS sym RS trans) 1),
        (etac arg_cong 1),
        (rtac (de_Morgan_disj RS subst) 1),
        (atac 1),
        (rtac disjI1 1),
        (rtac (Rep_Sprod_inverse RS sym RS trans) 1),
        (res_inst_tac [("f","Abs_Sprod")] arg_cong 1),
        (etac trans 1),
        (etac strict_Spair_Rep 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* general elimination rule for strict product                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "IsprodE" Sprod0.thy
"[|p=Ispair UU UU ==> Q ;!!x y. [|p=Ispair x y; x~=UU ; y~=UU|] ==> Q|] ==> Q"
(fn prems =>
        [
        (rtac (Exh_Sprod RS disjE) 1),
        (etac (hd prems) 1),
        (etac exE 1),
        (etac exE 1),
        (etac conjE 1),
        (etac conjE 1),
        (etac (hd (tl prems)) 1),
        (atac 1),
        (atac 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* some results about the selectors Isfst, Issnd                            *)
(* ------------------------------------------------------------------------ *)

qed_goalw "strict_Isfst" Sprod0.thy [Isfst_def] 
        "p=Ispair UU UU ==> Isfst p = UU"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac  select_equality 1),
        (rtac conjI 1),
        (fast_tac HOL_cs  1),
        (strip_tac 1),
        (res_inst_tac [("P","Ispair UU UU = Ispair a b")] notE 1),
        (rtac not_sym 1),
        (rtac defined_Ispair 1),
        (REPEAT (fast_tac HOL_cs  1))
        ]);


qed_goal "strict_Isfst1" Sprod0.thy
        "Isfst(Ispair UU y) = UU"
(fn prems =>
        [
        (stac strict_Ispair1 1),
        (rtac strict_Isfst 1),
        (rtac refl 1)
        ]);

qed_goal "strict_Isfst2" Sprod0.thy
        "Isfst(Ispair x UU) = UU"
(fn prems =>
        [
        (stac strict_Ispair2 1),
        (rtac strict_Isfst 1),
        (rtac refl 1)
        ]);


qed_goalw "strict_Issnd" Sprod0.thy [Issnd_def] 
        "p=Ispair UU UU ==>Issnd p=UU"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac  select_equality 1),
        (rtac conjI 1),
        (fast_tac HOL_cs  1),
        (strip_tac 1),
        (res_inst_tac [("P","Ispair UU UU = Ispair a b")] notE 1),
        (rtac not_sym 1),
        (rtac defined_Ispair 1),
        (REPEAT (fast_tac HOL_cs  1))
        ]);

qed_goal "strict_Issnd1" Sprod0.thy
        "Issnd(Ispair UU y) = UU"
(fn prems =>
        [
        (stac strict_Ispair1 1),
        (rtac strict_Issnd 1),
        (rtac refl 1)
        ]);

qed_goal "strict_Issnd2" Sprod0.thy
        "Issnd(Ispair x UU) = UU"
(fn prems =>
        [
        (stac strict_Ispair2 1),
        (rtac strict_Issnd 1),
        (rtac refl 1)
        ]);

qed_goalw "Isfst" Sprod0.thy [Isfst_def]
        "[|x~=UU ;y~=UU |] ==> Isfst(Ispair x y) = x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac  select_equality 1),
        (rtac conjI 1),
        (strip_tac 1),
        (res_inst_tac [("P","Ispair x y = Ispair UU UU")] notE 1),
        (etac defined_Ispair 1),
        (atac 1),
        (atac 1),
        (strip_tac 1),
        (rtac (inject_Ispair RS conjunct1) 1),
        (fast_tac HOL_cs  3),
        (fast_tac HOL_cs  1),
        (fast_tac HOL_cs  1),
        (fast_tac HOL_cs  1)
        ]);

qed_goalw "Issnd" Sprod0.thy [Issnd_def]
        "[|x~=UU ;y~=UU |] ==> Issnd(Ispair x y) = y"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac  select_equality 1),
        (rtac conjI 1),
        (strip_tac 1),
        (res_inst_tac [("P","Ispair x y = Ispair UU UU")] notE 1),
        (etac defined_Ispair 1),
        (atac 1),
        (atac 1),
        (strip_tac 1),
        (rtac (inject_Ispair RS conjunct2) 1),
        (fast_tac HOL_cs  3),
        (fast_tac HOL_cs  1),
        (fast_tac HOL_cs  1),
        (fast_tac HOL_cs  1)
        ]);

qed_goal "Isfst2" Sprod0.thy "y~=UU ==>Isfst(Ispair x y)=x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
        (etac Isfst 1),
        (atac 1),
        (hyp_subst_tac 1),
        (rtac strict_Isfst1 1)
        ]);

qed_goal "Issnd2" Sprod0.thy "~x=UU ==>Issnd(Ispair x y)=y"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("Q","y=UU")] (excluded_middle RS disjE) 1),
        (etac Issnd 1),
        (atac 1),
        (hyp_subst_tac 1),
        (rtac strict_Issnd2 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

val Sprod0_ss = 
        HOL_ss 
        addsimps [strict_Isfst1,strict_Isfst2,strict_Issnd1,strict_Issnd2,
                 Isfst2,Issnd2];

qed_goal "defined_IsfstIssnd" Sprod0.thy 
        "p~=Ispair UU UU ==> Isfst p ~= UU & Issnd p ~= UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("p","p")] IsprodE 1),
        (contr_tac 1),
        (hyp_subst_tac 1),
        (rtac conjI 1),
        (asm_simp_tac Sprod0_ss 1),
        (asm_simp_tac Sprod0_ss 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Surjective pairing: equivalent to Exh_Sprod                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "surjective_pairing_Sprod" Sprod0.thy 
        "z = Ispair(Isfst z)(Issnd z)"
(fn prems =>
        [
        (res_inst_tac [("z1","z")] (Exh_Sprod RS disjE) 1),
        (asm_simp_tac Sprod0_ss 1),
        (etac exE 1),
        (etac exE 1),
        (asm_simp_tac Sprod0_ss 1)
        ]);

qed_goal "Sel_injective_Sprod" thy 
        "[|Isfst x = Isfst y; Issnd x = Issnd y|] ==> x = y"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (subgoal_tac "Ispair(Isfst x)(Issnd x)=Ispair(Isfst y)(Issnd y)" 1),
        (rotate_tac ~1 1),
        (asm_full_simp_tac(HOL_ss addsimps[surjective_pairing_Sprod RS sym])1),
        (Asm_simp_tac 1)
        ]);
