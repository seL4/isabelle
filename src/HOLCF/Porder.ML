(*  Title:      HOLCF/Porder.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for theory Porder.thy 
*)

open Porder;

(* ------------------------------------------------------------------------ *)
(* lubs are unique                                                          *)
(* ------------------------------------------------------------------------ *)

qed_goalw "unique_lub" thy [is_lub, is_ub] 
        "[| S <<| x ; S <<| y |] ==> x=y"
( fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac conjE 1),
        (etac conjE 1),
        (rtac antisym_less 1),
        (rtac mp 1),((etac allE 1) THEN (atac 1) THEN (atac 1)),
        (rtac mp 1),((etac allE 1) THEN (atac 1) THEN (atac 1))
        ]);

(* ------------------------------------------------------------------------ *)
(* chains are monotone functions                                            *)
(* ------------------------------------------------------------------------ *)

qed_goalw "chain_mono" thy [chain] "chain F ==> x<y --> F x<<F y"
( fn prems =>
        [
        (cut_facts_tac prems 1),
        (nat_ind_tac "y" 1),
        (rtac impI 1),
        (etac less_zeroE 1),
        (stac less_Suc_eq 1),
        (strip_tac 1),
        (etac disjE 1),
        (rtac trans_less 1),
        (etac allE 2),
        (atac 2),
        (fast_tac HOL_cs 1),
        (hyp_subst_tac 1),
        (etac allE 1),
        (atac 1)
        ]);

qed_goal "chain_mono3" thy "[| chain F; x <= y |] ==> F x << F y"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (le_imp_less_or_eq RS disjE) 1),
        (atac 1),
        (etac (chain_mono RS mp) 1),
        (atac 1),
        (hyp_subst_tac 1),
        (rtac refl_less 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* The range of a chain is a totaly ordered     <<                           *)
(* ------------------------------------------------------------------------ *)

qed_goalw "chain_tord" thy [tord] 
"!!F. chain(F) ==> tord(range(F))"
 (fn _ =>
        [
        Safe_tac,
        (rtac nat_less_cases 1),
        (ALLGOALS (fast_tac (claset() addIs [refl_less, chain_mono RS mp])))]);

(* ------------------------------------------------------------------------ *)
(* technical lemmas about lub and is_lub                                    *)
(* ------------------------------------------------------------------------ *)
bind_thm("lub",lub_def RS meta_eq_to_obj_eq);

qed_goal "lubI" thy "? x. M <<| x ==> M <<| lub(M)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac lub 1),
        (etac (select_eq_Ex RS iffD2) 1)
        ]);

qed_goal "lubE" thy "M <<| lub(M) ==> ? x. M <<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac exI 1)
        ]);

qed_goal "lub_eq" thy "(? x. M <<| x)  = M <<| lub(M)"
(fn prems => 
        [
        (stac lub 1),
        (rtac (select_eq_Ex RS subst) 1),
        (rtac refl 1)
        ]);


qed_goal "thelubI" thy "M <<| l ==> lub(M) = l"
(fn prems =>
        [
        (cut_facts_tac prems 1), 
        (rtac unique_lub 1),
        (stac lub 1),
        (etac selectI 1),
        (atac 1)
        ]);


goal thy "lub{x} = x";
by (rtac thelubI 1);
by (simp_tac (simpset() addsimps [is_lub,is_ub]) 1);
qed "lub_singleton";
Addsimps [lub_singleton];

(* ------------------------------------------------------------------------ *)
(* access to some definition as inference rule                              *)
(* ------------------------------------------------------------------------ *)

qed_goalw "is_lubE" thy [is_lub]
        "S <<| x  ==> S <| x & (! u. S <| u  --> x << u)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);

qed_goalw "is_lubI" thy [is_lub]
        "S <| x & (! u. S <| u  --> x << u) ==> S <<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);

qed_goalw "chainE" thy [chain] "chain F ==> !i. F(i) << F(Suc(i))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)]);

qed_goalw "chainI" thy [chain] "!i. F i << F(Suc i) ==> chain F"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)]);

(* ------------------------------------------------------------------------ *)
(* technical lemmas about (least) upper bounds of chains                    *)
(* ------------------------------------------------------------------------ *)

qed_goalw "ub_rangeE" thy [is_ub] "range S <| x  ==> !i. S(i) << x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (rtac mp 1),
        (etac spec 1),
        (rtac rangeI 1)
        ]);

qed_goalw "ub_rangeI" thy [is_ub] "!i. S i << x  ==> range S <| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (etac rangeE 1),
        (hyp_subst_tac 1),
        (etac spec 1)
        ]);

bind_thm ("is_ub_lub", is_lubE RS conjunct1 RS ub_rangeE RS spec);
(* range(?S1) <<| ?x1 ==> ?S1(?x) << ?x1                                    *)

bind_thm ("is_lub_lub", is_lubE RS conjunct2 RS spec RS mp);
(* [| ?S3 <<| ?x3; ?S3 <| ?x1 |] ==> ?x3 << ?x1                             *)

(* ------------------------------------------------------------------------ *)
(* results about finite chains                                              *)
(* ------------------------------------------------------------------------ *)

qed_goalw "lub_finch1" thy [max_in_chain_def]
        "[| chain C; max_in_chain i C|] ==> range C <<| C i"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (res_inst_tac [("m","i")] nat_less_cases 1),
        (rtac (antisym_less_inverse RS conjunct2) 1),
        (etac (disjI1 RS less_or_eq_imp_le RS rev_mp) 1),
        (etac spec 1),
        (rtac (antisym_less_inverse RS conjunct2) 1),
        (etac (disjI2 RS less_or_eq_imp_le RS rev_mp) 1),
        (etac spec 1),
        (etac (chain_mono RS mp) 1),
        (atac 1),
        (strip_tac 1),
        (etac (ub_rangeE RS spec) 1)
        ]);     

qed_goalw "lub_finch2" thy [finite_chain_def]
        "finite_chain(C) ==> range(C) <<| C(@ i. max_in_chain i C)"
 (fn prems=>
        [
        (cut_facts_tac prems 1),
        (rtac lub_finch1 1),
        (etac conjunct1 1),
        (rtac (select_eq_Ex RS iffD2) 1),
        (etac conjunct2 1)
        ]);


qed_goal "bin_chain" thy "x<<y ==> chain (%i. if i=0 then x else y)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac chainI 1),
        (rtac allI 1),
        (nat_ind_tac "i" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1)
        ]);

qed_goalw "bin_chainmax" thy [max_in_chain_def,le_def]
        "x<<y ==> max_in_chain (Suc 0) (%i. if (i=0) then x else y)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac allI 1),
        (nat_ind_tac "j" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1)
        ]);

qed_goal "lub_bin_chain" thy 
        "x << y ==> range(%i. if (i=0) then x else y) <<| y"
(fn prems=>
        [ (cut_facts_tac prems 1),
        (res_inst_tac [("s","if (Suc 0) = 0 then x else y")] subst 1),
        (rtac lub_finch1 2),
        (etac bin_chain 2),
        (etac bin_chainmax 2),
        (Simp_tac  1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the maximal element in a chain is its lub                                *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_chain_maxelem" thy
"[|? i. Y i=c;!i. Y i<<c|] ==> lub(range Y) = c"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac thelubI 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (etac ub_rangeI 1),
        (strip_tac 1),
        (etac exE 1),
        (hyp_subst_tac 1),
        (etac (ub_rangeE RS spec) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the lub of a constant chain is the constant                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_const" thy "range(%x. c) <<| c"
 (fn prems =>
        [
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (strip_tac 1),
        (rtac refl_less 1),
        (strip_tac 1),
        (etac (ub_rangeE RS spec) 1)
        ]);



