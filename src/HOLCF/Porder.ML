(*  Title:      HOLCF/Porder
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Conservative extension of theory Porder0 by constant definitions 
*)

(* ------------------------------------------------------------------------ *)
(* lubs are unique                                                          *)
(* ------------------------------------------------------------------------ *)


val prems = goalw thy [is_lub, is_ub] 
        "[| S <<| x ; S <<| y |] ==> x=y";
by (cut_facts_tac prems 1);
by (etac conjE 1);
by (etac conjE 1);
by (rtac antisym_less 1);
by (rtac mp 1);
by ((etac allE 1) THEN (atac 1) THEN (atac 1));
by (rtac mp 1);
by ((etac allE 1) THEN (atac 1) THEN (atac 1));
qed "unique_lub";

(* ------------------------------------------------------------------------ *)
(* chains are monotone functions                                            *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [chain] "chain F ==> x<y --> F x<<F y";
by (cut_facts_tac prems 1);
by (induct_tac "y" 1);
by (rtac impI 1);
by (etac less_zeroE 1);
by (stac less_Suc_eq 1);
by (strip_tac 1);
by (etac disjE 1);
by (rtac trans_less 1);
by (etac allE 2);
by (atac 2);
by (fast_tac HOL_cs 1);
by (hyp_subst_tac 1);
by (etac allE 1);
by (atac 1);
qed "chain_mono";

Goal "[| chain F; x <= y |] ==> F x << F y";
by (rtac (le_imp_less_or_eq RS disjE) 1);
by (atac 1);
by (etac (chain_mono RS mp) 1);
by (atac 1);
by (hyp_subst_tac 1);
by (rtac refl_less 1);
qed "chain_mono3";


(* ------------------------------------------------------------------------ *)
(* The range of a chain is a totally ordered     <<                         *)
(* ------------------------------------------------------------------------ *)

val _ = goalw thy [tord] 
"!!F. chain(F) ==> tord(range(F))";
by (Safe_tac);
by (rtac nat_less_cases 1);
by (ALLGOALS (fast_tac (claset() addIs [refl_less, chain_mono RS mp])));
qed "chain_tord";


(* ------------------------------------------------------------------------ *)
(* technical lemmas about lub and is_lub                                    *)
(* ------------------------------------------------------------------------ *)
bind_thm("lub",lub_def RS meta_eq_to_obj_eq);

Goal "? x. M <<| x ==> M <<| lub(M)";
by (stac lub 1);
by (etac (select_eq_Ex RS iffD2) 1);
qed "lubI";

Goal "M <<| lub(M) ==> ? x. M <<| x";
by (etac exI 1);
qed "lubE";

Goal "(? x. M <<| x)  = M <<| lub(M)";
by (stac lub 1);
by (rtac (select_eq_Ex RS subst) 1);
by (rtac refl 1);
qed "lub_eq";


Goal "M <<| l ==> lub(M) = l";
by (rtac unique_lub 1);
by (stac lub 1);
by (etac selectI 1);
by (atac 1);
qed "thelubI";


Goal "lub{x} = x";
by (rtac thelubI 1);
by (simp_tac (simpset() addsimps [is_lub,is_ub]) 1);
qed "lub_singleton";
Addsimps [lub_singleton];

(* ------------------------------------------------------------------------ *)
(* access to some definition as inference rule                              *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [is_lub]
        "S <<| x  ==> S <| x & (! u. S <| u  --> x << u)";
by (cut_facts_tac prems 1);
by (atac 1);
qed "is_lubE";

val prems = goalw thy [is_lub]
        "S <| x & (! u. S <| u  --> x << u) ==> S <<| x";
by (cut_facts_tac prems 1);
by (atac 1);
qed "is_lubI";

val prems = goalw thy [chain] "chain F ==> !i. F(i) << F(Suc(i))";
by (cut_facts_tac prems 1);
by (atac 1);
qed "chainE";

val prems = goalw thy [chain] "!i. F i << F(Suc i) ==> chain F";
by (cut_facts_tac prems 1);
by (atac 1);
qed "chainI";

(* ------------------------------------------------------------------------ *)
(* technical lemmas about (least) upper bounds of chains                    *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [is_ub] "range S <| x  ==> !i. S(i) << x";
by (cut_facts_tac prems 1);
by (strip_tac 1);
by (rtac mp 1);
by (etac spec 1);
by (rtac rangeI 1);
qed "ub_rangeE";

val prems = goalw thy [is_ub] "!i. S i << x  ==> range S <| x";
by (cut_facts_tac prems 1);
by (strip_tac 1);
by (etac rangeE 1);
by (hyp_subst_tac 1);
by (etac spec 1);
qed "ub_rangeI";

bind_thm ("is_ub_lub", is_lubE RS conjunct1 RS ub_rangeE RS spec);
(* range(?S1) <<| ?x1 ==> ?S1(?x) << ?x1                                    *)

bind_thm ("is_lub_lub", is_lubE RS conjunct2 RS spec RS mp);
(* [| ?S3 <<| ?x3; ?S3 <| ?x1 |] ==> ?x3 << ?x1                             *)

(* ------------------------------------------------------------------------ *)
(* results about finite chains                                              *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [max_in_chain_def]
        "[| chain C; max_in_chain i C|] ==> range C <<| C i";
by (cut_facts_tac prems 1);
by (rtac is_lubI 1);
by (rtac conjI 1);
by (rtac ub_rangeI 1);
by (rtac allI 1);
by (res_inst_tac [("m","i")] nat_less_cases 1);
by (rtac (antisym_less_inverse RS conjunct2) 1);
by (etac (disjI1 RS less_or_eq_imp_le RS rev_mp) 1);
by (etac spec 1);
by (rtac (antisym_less_inverse RS conjunct2) 1);
by (etac (disjI2 RS less_or_eq_imp_le RS rev_mp) 1);
by (etac spec 1);
by (etac (chain_mono RS mp) 1);
by (atac 1);
by (strip_tac 1);
by (etac (ub_rangeE RS spec) 1);
qed "lub_finch1";     

val prems= goalw thy [finite_chain_def]
        "finite_chain(C) ==> range(C) <<| C(@ i. max_in_chain i C)";
by (cut_facts_tac prems 1);
by (rtac lub_finch1 1);
by (etac conjunct1 1);
by (rtac (select_eq_Ex RS iffD2) 1);
by (etac conjunct2 1);
qed "lub_finch2";


Goal "x<<y ==> chain (%i. if i=0 then x else y)";
by (rtac chainI 1);
by (rtac allI 1);
by (induct_tac "i" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed "bin_chain";

val prems = goalw thy [max_in_chain_def,le_def]
        "x<<y ==> max_in_chain (Suc 0) (%i. if (i=0) then x else y)";
by (cut_facts_tac prems 1);
by (rtac allI 1);
by (induct_tac "j" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed "bin_chainmax";

Goal "x << y ==> range(%i::nat. if (i=0) then x else y) <<| y";
by (res_inst_tac [("s","if (Suc 0) = 0 then x else y")] subst 1
    THEN rtac lub_finch1 2);
by (etac bin_chain 2);
by (etac bin_chainmax 2);
by (Simp_tac  1);
qed "lub_bin_chain";

(* ------------------------------------------------------------------------ *)
(* the maximal element in a chain is its lub                                *)
(* ------------------------------------------------------------------------ *)

Goal "[|? i. Y i=c;!i. Y i<<c|] ==> lub(range Y) = c";
by (rtac thelubI 1);
by (rtac is_lubI 1);
by (rtac conjI 1);
by (etac ub_rangeI 1);
by (strip_tac 1);
by (etac exE 1);
by (hyp_subst_tac 1);
by (etac (ub_rangeE RS spec) 1);
qed "lub_chain_maxelem";

(* ------------------------------------------------------------------------ *)
(* the lub of a constant chain is the constant                              *)
(* ------------------------------------------------------------------------ *)

Goal "range(%x. c) <<| c";
by (rtac is_lubI 1);
by (rtac conjI 1);
by (rtac ub_rangeI 1);
by (strip_tac 1);
by (rtac refl_less 1);
by (strip_tac 1);
by (etac (ub_rangeE RS spec) 1);
qed "lub_const";



