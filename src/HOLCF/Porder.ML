(*  Title:      HOLCF/Porder
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Conservative extension of theory Porder0 by constant definitions 
*)

(* ------------------------------------------------------------------------ *)
(* lubs are unique                                                          *)
(* ------------------------------------------------------------------------ *)


Goalw [is_lub, is_ub] 
        "[| S <<| x ; S <<| y |] ==> x=y";
by (blast_tac (claset() addIs [antisym_less]) 1);
qed "unique_lub";

(* ------------------------------------------------------------------------ *)
(* chains are monotone functions                                            *)
(* ------------------------------------------------------------------------ *)

Goalw [chain] "chain F ==> x<y --> F x<<F y";
by (induct_tac "y" 1);
by Auto_tac;  
by (blast_tac (claset() addIs [trans_less]) 2);
by (blast_tac (claset() addSEs [less_SucE]) 1);
qed_spec_mp "chain_mono";

Goal "[| chain F; x <= y |] ==> F x << F y";
by (dtac le_imp_less_or_eq 1);
by (blast_tac (claset() addIs [chain_mono]) 1);
qed "chain_mono3";


(* ------------------------------------------------------------------------ *)
(* The range of a chain is a totally ordered     <<                         *)
(* ------------------------------------------------------------------------ *)

Goalw [tord] "chain(F) ==> tord(range(F))";
by (Safe_tac);
by (rtac nat_less_cases 1);
by (ALLGOALS (fast_tac (claset() addIs [chain_mono])));
qed "chain_tord";


(* ------------------------------------------------------------------------ *)
(* technical lemmas about lub and is_lub                                    *)
(* ------------------------------------------------------------------------ *)
bind_thm("lub",lub_def RS meta_eq_to_obj_eq);

Goal "EX x. M <<| x ==> M <<| lub(M)";
by (asm_full_simp_tac (simpset() addsimps [lub, Ex_def]) 1);
bind_thm ("lubI", exI RS result());

Goal "M <<| l ==> lub(M) = l";
by (rtac unique_lub 1);
by (stac lub 1);
by (etac someI 1);
by (atac 1);
qed "thelubI";


Goal "lub{x} = x";
by (simp_tac (simpset() addsimps [thelubI,is_lub,is_ub]) 1);
qed "lub_singleton";
Addsimps [lub_singleton];

(* ------------------------------------------------------------------------ *)
(* access to some definition as inference rule                              *)
(* ------------------------------------------------------------------------ *)

Goalw [is_lub] "S <<| x ==> S <| x";
by Auto_tac;
qed "is_lubD1";

Goalw [is_lub] "[| S <<| x; S <| u |] ==> x << u";
by Auto_tac;
qed "is_lub_lub";

val prems = Goalw [is_lub]
        "[| S <| x; !!u. S <| u ==> x << u |] ==> S <<| x";
by (blast_tac (claset() addIs prems) 1);
qed "is_lubI";

Goalw [chain] "chain F ==> F(i) << F(Suc(i))";
by Auto_tac;
qed "chainE";

val prems = Goalw [chain] "(!!i. F i << F(Suc i)) ==> chain F";
by (blast_tac (claset() addIs prems) 1);
qed "chainI";

(* ------------------------------------------------------------------------ *)
(* technical lemmas about (least) upper bounds of chains                    *)
(* ------------------------------------------------------------------------ *)

Goalw [is_ub] "range S <| x  ==> S(i) << x";
by (Blast_tac 1);
qed "ub_rangeD";

val prems = Goalw [is_ub] "(!!i. S i << x) ==> range S <| x";
by (blast_tac (claset() addIs prems) 1);
qed "ub_rangeI";

bind_thm ("is_ub_lub", is_lubD1 RS ub_rangeD);
(* range(?S1) <<| ?x1 ==> ?S1(?x) << ?x1                                    *)


(* ------------------------------------------------------------------------ *)
(* results about finite chains                                              *)
(* ------------------------------------------------------------------------ *)

Goalw [max_in_chain_def]
        "[| chain C; max_in_chain i C|] ==> range C <<| C i";
by (rtac is_lubI 1);
by (rtac ub_rangeI 1);
by (res_inst_tac [("m","i")] nat_less_cases 1);
by (rtac (antisym_less_inverse RS conjunct2) 1);
by (etac (disjI1 RS less_or_eq_imp_le RS rev_mp) 1);
by (etac spec 1);
by (rtac (antisym_less_inverse RS conjunct2) 1);
by (etac (disjI2 RS less_or_eq_imp_le RS rev_mp) 1);
by (etac spec 1);
by (etac chain_mono 1);
by (atac 1);
by (etac (ub_rangeD) 1);
qed "lub_finch1";     

Goalw [finite_chain_def]
        "finite_chain(C) ==> range(C) <<| C(@ i. max_in_chain i C)";
by (rtac lub_finch1 1);
by (best_tac (claset() addIs [someI]) 2);
by (Blast_tac 1);
qed "lub_finch2";


Goal "x<<y ==> chain (%i. if i=0 then x else y)";
by (rtac chainI 1);
by (induct_tac "i" 1);
by Auto_tac;  
qed "bin_chain";

Goalw [max_in_chain_def,le_def]
        "x<<y ==> max_in_chain (Suc 0) (%i. if (i=0) then x else y)";
by (rtac allI 1);
by (induct_tac "j" 1);
by Auto_tac; 
qed "bin_chainmax";

Goal "x << y ==> range(%i::nat. if (i=0) then x else y) <<| y";
by (res_inst_tac [("s","if (Suc 0) = 0 then x else y")] subst 1
    THEN rtac lub_finch1 2);
by (etac bin_chain 2);
by (etac bin_chainmax 2);
by (Simp_tac 1);
qed "lub_bin_chain";

(* ------------------------------------------------------------------------ *)
(* the maximal element in a chain is its lub                                *)
(* ------------------------------------------------------------------------ *)

Goal "[| Y i = c;  ALL i. Y i<<c |] ==> lub(range Y) = c";
by (blast_tac (claset()  addDs [ub_rangeD] 
                         addIs [thelubI, is_lubI, ub_rangeI]) 1);
qed "lub_chain_maxelem";

(* ------------------------------------------------------------------------ *)
(* the lub of a constant chain is the constant                              *)
(* ------------------------------------------------------------------------ *)

Goal "range(%x. c) <<| c";
by (blast_tac (claset()  addDs [ub_rangeD] addIs [is_lubI, ub_rangeI]) 1);
qed "lub_const";



