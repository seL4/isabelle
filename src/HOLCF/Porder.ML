(*  Title:      HOLCF/porder.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for theory porder.thy 
*)

open Porder0;
open Porder;


(* ------------------------------------------------------------------------ *)
(* the reverse law of anti--symmetrie of <<                                 *)
(* ------------------------------------------------------------------------ *)

qed_goal "antisym_less_inverse" Porder.thy "x=y ==> x << y & y << x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac conjI 1),
        ((rtac subst 1) THEN (rtac refl_less 2) THEN (atac 1)),
        ((rtac subst 1) THEN (rtac refl_less 2) THEN (etac sym 1))
        ]);


qed_goal "box_less" Porder.thy 
"[| a << b; c << a; b << d|] ==> c << d"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac trans_less 1),
        (etac trans_less 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* lubs are unique                                                          *)
(* ------------------------------------------------------------------------ *)

qed_goalw "unique_lub " Porder.thy [is_lub, is_ub] 
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

qed_goalw "chain_mono" Porder.thy [is_chain]
        " is_chain(F) ==> x<y --> F(x)<<F(y)"
( fn prems =>
        [
        (cut_facts_tac prems 1),
        (nat_ind_tac "y" 1),
        (rtac impI 1),
        (etac less_zeroE 1),
        (rtac (less_Suc_eq RS ssubst) 1),
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

qed_goal "chain_mono3"  Porder.thy 
        "[| is_chain(F); x <= y |] ==> F(x) << F(y)"
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

qed_goalw "chain_is_tord" Porder.thy [is_tord,range_def] 
"is_chain(F) ==> is_tord(range(F))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (REPEAT (rtac allI 1 )),
        (rtac (mem_Collect_eq RS ssubst) 1),
        (rtac (mem_Collect_eq RS ssubst) 1),
        (strip_tac 1),
        (etac conjE 1),
        (REPEAT (etac exE 1)),
        (REPEAT (hyp_subst_tac 1)),
        (rtac nat_less_cases 1),
        (rtac disjI1 1),
        (etac (chain_mono RS mp) 1),
        (atac 1),
        (rtac disjI1 1),
        (hyp_subst_tac 1),
        (rtac refl_less 1),
        (rtac disjI2 1),
        (etac (chain_mono RS mp) 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* technical lemmas about lub and is_lub                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "lubI" Porder.thy "(? x. M <<| x) ==> M <<| lub(M)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (lub RS ssubst) 1),
        (etac (select_eq_Ex RS iffD2) 1)
        ]);

qed_goal "lubE" Porder.thy " M <<| lub(M) ==>  ? x. M <<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac exI 1)
        ]);

qed_goal "lub_eq" Porder.thy 
        "(? x. M <<| x)  = M <<| lub(M)"
(fn prems => 
        [
        (rtac (lub RS ssubst) 1),
        (rtac (select_eq_Ex RS subst) 1),
        (rtac refl 1)
        ]);


qed_goal "thelubI"  Porder.thy " M <<| l ==> lub(M) = l"
(fn prems =>
        [
        (cut_facts_tac prems 1), 
        (rtac unique_lub 1),
        (rtac (lub RS ssubst) 1),
        (etac selectI 1),
        (atac 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* access to some definition as inference rule                              *)
(* ------------------------------------------------------------------------ *)

qed_goalw "is_lubE"  Porder.thy [is_lub]
        "S <<| x  ==> S <| x & (! u. S <| u  --> x << u)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);

qed_goalw "is_lubI"  Porder.thy [is_lub]
        "S <| x & (! u. S <| u  --> x << u) ==> S <<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)
        ]);

qed_goalw "is_chainE" Porder.thy [is_chain] 
 "is_chain(F) ==> ! i. F(i) << F(Suc(i))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)]);

qed_goalw "is_chainI" Porder.thy [is_chain] 
 "! i. F(i) << F(Suc(i)) ==> is_chain(F) "
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (atac 1)]);

(* ------------------------------------------------------------------------ *)
(* technical lemmas about (least) upper bounds of chains                    *)
(* ------------------------------------------------------------------------ *)

qed_goalw "ub_rangeE"  Porder.thy [is_ub]
        "range(S) <| x  ==> ! i. S(i) << x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (rtac mp 1),
        (etac spec 1),
        (rtac rangeI 1)
        ]);

qed_goalw "ub_rangeI" Porder.thy [is_ub]
        "! i. S(i) << x  ==> range(S) <| x"
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
(* Prototype lemmas for class pcpo                                          *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* a technical argument about << on void                                    *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_void" Porder.thy "((u1::void) << u2) = (u1 = u2)"
(fn prems =>
        [
        (rtac (inst_void_po RS ssubst) 1),
        (rewtac less_void_def),
        (rtac iffI 1),
        (rtac injD 1),
        (atac 2),
        (rtac inj_inverseI 1),
        (rtac Rep_Void_inverse 1),
        (etac arg_cong 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* void is pointed. The least element is UU_void                            *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_void" Porder.thy      "UU_void << x"
(fn prems =>
        [
        (rtac (inst_void_po RS ssubst) 1),
        (rewtac less_void_def),
        (simp_tac (!simpset addsimps [unique_void]) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* UU_void is the trivial lub of all chains in void                         *)
(* ------------------------------------------------------------------------ *)

qed_goalw "lub_void"  Porder.thy [is_lub] "M <<| UU_void"
(fn prems =>
        [
        (rtac conjI 1),
        (rewtac is_ub),
        (strip_tac 1),
        (rtac (inst_void_po RS ssubst) 1),
        (rewtac less_void_def),
        (simp_tac (!simpset addsimps [unique_void]) 1),
        (strip_tac 1),
        (rtac minimal_void 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* lub(?M) = UU_void                                                        *)
(* ------------------------------------------------------------------------ *)

bind_thm ("thelub_void", lub_void RS thelubI);

(* ------------------------------------------------------------------------ *)
(* void is a cpo wrt. countable chains                                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "cpo_void" Porder.thy
        "is_chain((S::nat=>void)) ==> ? x. range(S) <<| x "
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("x","UU_void")] exI 1),
        (rtac lub_void 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* end of prototype lemmas for class pcpo                                   *)
(* ------------------------------------------------------------------------ *)


(* ------------------------------------------------------------------------ *)
(* results about finite chains                                              *)
(* ------------------------------------------------------------------------ *)

qed_goalw "lub_finch1" Porder.thy [max_in_chain_def]
        "[| is_chain(C) ; max_in_chain i C|] ==> range(C) <<| C(i)"
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

qed_goalw "lub_finch2" Porder.thy [finite_chain_def]
        "finite_chain(C) ==> range(C) <<| C(@ i. max_in_chain i C)"
 (fn prems=>
        [
        (cut_facts_tac prems 1),
        (rtac lub_finch1 1),
        (etac conjunct1 1),
        (rtac (select_eq_Ex RS iffD2) 1),
        (etac conjunct2 1)
        ]);


qed_goal "bin_chain" Porder.thy "x<<y ==> is_chain (%i. if i=0 then x else y)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_chainI 1),
        (rtac allI 1),
        (nat_ind_tac "i" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1),
        (rtac refl_less 1)
        ]);

qed_goalw "bin_chainmax" Porder.thy [max_in_chain_def,le_def]
        "x<<y ==> max_in_chain (Suc 0) (%i. if (i=0) then x else y)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac allI 1),
        (nat_ind_tac "j" 1),
        (Asm_simp_tac 1),
        (Asm_simp_tac 1)
        ]);

qed_goal "lub_bin_chain" Porder.thy 
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

qed_goal "lub_chain_maxelem" Porder.thy
"[|? i.Y(i)=c;!i.Y(i)<<c|] ==> lub(range(Y)) = c"
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

qed_goal "lub_const" Porder.thy "range(%x.c) <<| c"
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



