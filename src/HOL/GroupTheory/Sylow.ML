(*  Title:      HOL/GroupTheory/Group
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   2001  University of Cambridge
*)

(* The clean version, no comments, more tacticals*)

AddIffs [p1 RS prime_imp_one_less];

val [q1,q2,q3] = goal Sylow.thy "[|M <= carrier G; g\\<in>carrier G; h\\<in>carrier G |]\
\       ==> (M #> g) #> h = M #> (g ## h)";
by (rewrite_goals_tac [r_coset_abbr, bin_op_abbr]);
by (rtac coset_mul_assoc 1);
by (rtac p2 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac q3 1);
qed "Icoset_mul_assoc";

val [q1] = goal Sylow.thy "[| M <= carrier G |] ==> M #> e = M";
by (rewrite_goals_tac [r_coset_abbr,e_def]);
by (rtac coset_mul_unity 1);
by (rtac p2 1);
by (rtac q1 1);
qed "Icoset_mul_unity";

val [q1,q2,q3,q4] = goal Sylow.thy "[| x\\<in>carrier G; y\\<in>carrier G;\
\       M <= carrier G; M #> (x ## inv y) = M |] ==> M #> x = M #> y";
by (rewtac r_coset_abbr);
by (rtac coset_mul_invers1 1);
by (rtac p2 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac q3 1);
by (fold_goals_tac [r_coset_abbr, bin_op_abbr,inv_def]);
by (rtac q4 1);
qed "Icoset_mul_invers1";

val [q1,q2,q3,q4] = goal Sylow.thy "[| x\\<in>carrier G; y\\<in>carrier G;\
\       M <= carrier G; M #> x = M #> y|] ==> M #> (x ## inv y) = M ";
by (rewrite_goals_tac [r_coset_abbr,inv_def,bin_op_abbr]);
by (rtac coset_mul_invers2 1);
by (rtac p2 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac q3 1);
by (fold_goals_tac [r_coset_abbr]);
by (rtac q4 1);
qed "Icoset_mul_invers2";

val [q1,q2,q3] = goal Sylow.thy "[| x\\<in>carrier G; H <<= G;\
\                   H #> x = H |] ==> x\\<in>H";       
by (rtac coset_join1 1);
by (rtac p2 1);
by (rtac q1 1);
by (rtac q2 1);
by (fold_goals_tac [r_coset_abbr]);
by (rtac q3 1);
qed "Icoset_join1";

val [q1,q2,q3] = goal Sylow.thy "[| x\\<in>carrier G; H <<= G;\
\                   x\\<in>H |] ==> H #> x = H";
by (rewtac r_coset_abbr);
by (rtac coset_join2 1);
by (rtac p2 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac q3 1);
qed "Icoset_join2";

val [q1,q2,q3,q4] = goal Sylow.thy "[| x\\<in>carrier G; y\\<in>carrier G;\
\ z\\<in>carrier G; x ## y = x ## z |] ==> y = z";
by (rtac left_cancellation 1);
by (rtac p2 1);
by (fold_goals_tac [bin_op_abbr]);
by (rtac q1 1);
by (rtac q2 1);
by (rtac q3 1);
by (rtac q4 1);
qed "Ileft_cancellation";

val [q1,q2,q3,q4] = goal Sylow.thy "[| x\\<in>carrier G; y\\<in>carrier G;\
\ z\\<in>carrier G; y ## x = z ## x |] ==> y = z";
by (rtac right_cancellation 1);
by (rtac p2 1);
by (fold_goals_tac [bin_op_abbr]);
by (rtac q1 1);
by (rtac q2 1);
by (rtac q3 1);
by (rtac q4 1);
qed "Iright_cancellation";

goal Sylow.thy "e\\<in>carrier G";
by (rewtac e_def);
by (rtac (p2 RS unity_closed) 1);
qed "Iunity_closed";

val [q1,q2] = goal Sylow.thy "[|x\\<in>carrier G; y\\<in>carrier G |]\
\           ==> x ## y\\<in>carrier G";
by (rewtac bin_op_abbr);
by (rtac bin_op_closed 1);
by (rtac p2 1);
by (rtac q1 1);
by (rtac q2 1);
qed "Ibin_op_closed";

val [q1] = goal Sylow.thy "[|x\\<in>carrier G |] ==> inv x\\<in>carrier G";
by (rewtac inv_def);
by (rtac invers_closed 1);
by (rtac p2 1);
by (rtac q1 1);
qed "Iinvers_closed";

val [q1] = goal Sylow.thy "[| x\\<in>carrier G |] ==> e ## x = x";
by (rewrite_goals_tac [e_def,bin_op_abbr]);
by (rtac unity_ax1 1);
by (rtac p2 1);
by (rtac q1 1);
qed "Iunity_ax1";

val [q1] = goal Sylow.thy "[| x\\<in>carrier G |] ==> x ## e = x";
by (rewrite_goals_tac [e_def,bin_op_abbr]);
by (rtac unity_ax2 1);
by (rtac p2 1);
by (rtac q1 1);
qed "Iunity_ax2";

val [q1] = goal Sylow.thy "[| x\\<in>carrier G |] ==> x ## inv x = e";
by (rewrite_goals_tac [e_def,inv_def,bin_op_abbr]);
by (rtac invers_ax1 1);
by (rtac p2 1);
by (rtac q1 1);
qed "Iinvers_ax1";

val [q1] = goal Sylow.thy "[| x\\<in>carrier G |] ==> inv x ## x = e";
by (rewrite_goals_tac [e_def,inv_def,bin_op_abbr]);
by (rtac invers_ax2 1);
by (rtac p2 1);
by (rtac q1 1);
qed "Iinvers_ax2";

val [q1,q2,q3] = goal Sylow.thy "[| x\\<in>carrier G; y\\<in>carrier G; z\\<in>carrier G |] \
\                 ==> (x ## y)## z = x ##(y ## z)";
by (rewtac bin_op_abbr);
by (rtac bin_op_assoc 1);
by (rtac p2 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac q3 1);
qed "Ibin_op_assoc";

val [q1] = goal Sylow.thy "H <<= G ==> e\\<in>H";
by (rewtac e_def);
by (rtac SG_unity 1);
by (rtac p2 1);
by (rtac q1 1);
qed "ISG_unity";

val prems = goal Sylow.thy "[| H <= carrier G; H \\<noteq> {};\
\ \\<forall> x \\<in> H. inv x \\<in> H; \\<forall> x \\<in> H. \\<forall> y \\<in> H. x ## y \\<in> H |] ==> H <<= G";
by (rtac subgroupI 1);
by (fold_goals_tac [bin_op_abbr, inv_def]);
by (REPEAT (ares_tac (p2 :: prems)  1));
qed "IsubgroupI";

goal Sylow.thy "equiv calM RelM";
by (rewtac equiv_def);
by (Step_tac 1);
by (rewrite_goals_tac [refl_def,RelM_def]);
by (rtac conjI 1);
by (Step_tac 1);
by (res_inst_tac [("x","e")] bexI 1);
by (rtac Iunity_closed 2);
by (rtac (Icoset_mul_unity RS sym) 1);
by (SELECT_GOAL (rewtac calM_def) 1);
by (Fast_tac 1);
by (rewtac sym_def);
by (Step_tac 1);
by (res_inst_tac [("x","inv g")] bexI 1);
by (etac Iinvers_closed 2);
by (stac Icoset_mul_assoc 1);
by (etac Iinvers_closed 3);
by (assume_tac 2);
by (SELECT_GOAL (rewtac calM_def) 1);
by (Fast_tac 1);
by (etac (Iinvers_ax1 RS ssubst) 1);
by (stac Icoset_mul_unity 1);
by (SELECT_GOAL (rewtac calM_def) 1);
by (Fast_tac 1);
by (rtac refl 1);
by (rewtac trans_def);
by (Step_tac 1);
by (res_inst_tac [("x","ga ## g")] bexI 1);
by (rtac Icoset_mul_assoc 1);
by (rewtac calM_def);
by (rotate_tac 4 1);
by (Fast_tac 1);
by (assume_tac 1);
by (assume_tac 1);
by (etac Ibin_op_closed 1);
by (assume_tac 1);
qed "RelM_equiv";


val [q1] = goal Sylow.thy 
" M\\<in>calM // RelM  ==> M <= calM";
by (rtac quotientE 1);
by (rtac q1 1);
by (etac ssubst 1);
by (rewrite_goals_tac [Image_def, RelM_def,subset_def]);
by (rtac ballI 1);
by (dtac CollectD 1);
(* change *)
by (etac bexE 1);
by (dtac CollectD_prod 1);
by (dtac conjunct1 1);
by (etac SigmaD2 1);
qed "M_subset_calM_prep";

val [q1] = goal Sylow.thy 
" M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M)) ==> M <= calM";
by (rtac M_subset_calM_prep 1);
by (rtac (q1 RS conjunct1) 1);
qed "M_subset_calM";

val [q1,q2] = goal Sylow.thy "[|M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1\\<in>M|] ==> card(M1) = p ^ a";
by (res_inst_tac [("P", "M1 <= carrier G")] conjunct2 1);
by (res_inst_tac [("a","M1")]  CollectD 1);
by (fold_goals_tac [calM_def]);
by (rtac (q2 RSN(2, subsetD)) 1);
by (rtac (q1 RS M_subset_calM) 1);
qed "card_M1";

val [q1,q2] = goal Sylow.thy
     "[|M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\       M1\\<in>M|] ==>  \\<exists>x. x\\<in>M1";
by (rtac NotEmpty_ExEl 1);
by (rtac card_nonempty 1);
by (rtac (q2 RS (q1 RS card_M1) RS ssubst) 1);
by (rtac zero_less_prime_power 1);
by (rtac p1 1);
qed "exists_x_in_M1";

val [q1,q2] = goal Sylow.thy "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1\\<in>M|] ==>   M1 <= carrier G";
by (rtac PowD 1);
by (rtac subsetD 1);
by (rtac q2 2);
by (rtac subset_trans 1);
by (rtac (q1 RS M_subset_calM) 1);
by (rewtac calM_def);
by (rtac subsetI 1);
by (rtac PowI 1);
by (rtac conjunct1 1);
by (etac CollectD 1); 
qed "M1_subset_G";

val [q1,q2] = goal Sylow.thy 
"[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M)); M1\\<in>M|] ==> \
\    \\<exists>f \\<in> {g. g\\<in>carrier G & M1 #> g = M1} -> M1. inj_on f {g. g\\<in>carrier G & M1 #> g = M1}";
by (rtac exE 1);
by (rtac (q2 RS (q1 RS exists_x_in_M1)) 1);
by (res_inst_tac [("x", "% z. x ## z")] bexI 1);
by (rewtac funcset_def);
by (rtac CollectI 2);
by (rtac ballI 2);
by (dtac CollectD 2);
by (ftac conjunct2 2);
by (SELECT_GOAL (rewrite_goals_tac [r_coset_abbr, r_coset_def]) 2);
by (dtac equalityD1 2);
by (rewtac subset_def);
by (fold_goals_tac [bin_op_abbr]);
by (res_inst_tac [("P","%z. z\\<in>M1")] bspec 2);
by (assume_tac 2);
by (rtac CollectI 2);
by (rtac bexI 2);
by (assume_tac 3);
by (rtac refl 2);
by (rtac inj_onI 1);
by (rtac Ileft_cancellation 1);
by (assume_tac 4);
by (dres_inst_tac [("a","y")] CollectD 3);
by (etac conjunct1 3);
by (dtac CollectD 2);
by (etac conjunct1 2);
by (etac (q2 RS (q1 RS M1_subset_G) RS subsetD) 1);
val  M1_inj_H = result();

val [q1,q2] = goal Sylow.thy  "[| {} = RelM `` {x}; x\\<in>calM |] ==> False";
by (res_inst_tac [("a","x")] emptyE 1);
by (stac q1 1);
by (rtac (q2 RS(RelM_equiv RS equiv_class_self)) 1);
qed "RangeNotEmpty";

goal Sylow.thy  "{} \\<notin> calM // RelM";
by (rtac notI 1);
by (rtac (RangeNotEmpty RSN (2, quotientE)) 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 1);
qed "EmptyNotInEquivSet";

val [q1] = goal Sylow.thy  
"M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M))==> \\<exists>M1. M1\\<in>M";
by (rtac NotEmpty_ExEl 1);
by (rtac (q1 RS conjunct1 RSN (2, MnotEqempty)) 1);
by (rtac EmptyNotInEquivSet 1);
qed "existsM1inM";

goal Sylow.thy "0 < order(G)";
by (rewtac order_def);
by (fold_goals_tac [carrier_def]);
by (rtac zero_less_card_empty 1);
by (rtac p4 1);
by (rtac ExEl_NotEmpty 1);
by (res_inst_tac [("x","e")] exI 1);
by (rtac Iunity_closed 1);
qed "zero_less_o_G";

goal Sylow.thy "0 < m";
by (res_inst_tac [("P","0 < p ^ a")] conjunct2 1);
by (rtac (zero_less_mult_iff RS subst) 1);
by (rtac (p3 RS subst) 1);
by (rtac zero_less_o_G 1);
qed "zero_less_m";

goal Sylow.thy  "card(calM) = ((p ^ a) * m choose p ^ a)";
by (simp_tac
    (simpset() addsimps [calM_def, p3 RS sym, order_eq, n_subsets, p4]) 1); 
qed "card_calM";

Goal "0 < card calM";
by (asm_full_simp_tac (simpset() addsimps [card_calM]) 1); 
by (rtac zero_less_binomial 1);
by (rtac le_extend_mult 1);
by (rtac le_refl 2);
by (rtac zero_less_m 1);
qed "zero_less_card_calM";

Goal "~ (p ^ ((exponent p m)+ 1) dvd card(calM))";
by (subgoal_tac "exponent p m = exponent p (card calM)" 1);
 by (asm_full_simp_tac (simpset() addsimps [card_calM, 
                           zero_less_m RS const_p_fac]) 2);
by (cut_facts_tac [zero_less_card_calM, p1] 1);
by (force_tac (claset() addDs [power_Suc_exponent_Not_dvd], simpset()) 1); 
qed "max_p_div_calM";

goal Sylow.thy "finite calM";
by (rtac finite_subset 1);
by (rtac (finite_Pow_iff RS iffD2) 2); 
by (rtac p4 2);
by (rtac subsetI 1);
by (rtac PowI 1);
by (SELECT_GOAL (rewtac calM_def) 1);
by (dtac CollectD 1);
by (etac conjunct1 1);
qed "finite_calM";



Goal "~(\\<forall> x\\<in>M. P x) ==> \\<exists>x\\<in>M. ~P x";
by (blast_tac (claset() addIs []) 1); 
qed "Set_NotAll_ExNot";


goal Sylow.thy "\\<exists>M. M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M))";
by (fold_goals_tac [Bex_def]);
by (rtac Set_NotAll_ExNot 1);
by (rtac contrapos_nn 1);
by (rtac max_p_div_calM 1);
by (rtac (RelM_equiv RSN(2, equiv_imp_dvd_card)) 1);
by (rtac finite_calM 1);
by (assume_tac 1); 
qed "lemma_A1";

val [q1,q2,q3,q4] = goal Sylow.thy "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\       M1\\<in>M; x\\<in>{g. g\\<in>carrier G & M1 #> g = M1}; xa\\<in>{g. g\\<in>carrier G & M1 #> g = M1}|]\
\      ==> x ## xa\\<in>{g. g\\<in>carrier G & M1 #> g = M1}";
val l1 = q3 RS CollectD RS conjunct2;
val l2 = q4 RS CollectD RS conjunct2;
val l3 = q3 RS CollectD RS conjunct1;
val l4 = q4 RS CollectD RS conjunct1;
by (rtac CollectI 1);
by (rtac conjI 1);
by (rtac Ibin_op_closed 1);
by (rtac l3 1);
by (rtac l4 1);
by (rtac (Icoset_mul_assoc RS subst) 1);
by (rtac l3 2);
by (rtac l4 2);
by (rtac (q2 RS (q1 RS M1_subset_G)) 1);
by (stac l1 1);
by (stac l2 1);
by (rtac refl 1);
qed "bin_op_closed_lemma";

val [q1,q2] = goal Sylow.thy "[|M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\        M1\\<in>M |] ==> {g. g\\<in>carrier G & M1 #> g = M1} <<= G";
by (rtac IsubgroupI 1);
by (rtac subsetI 1);
by (etac subset_lemma1 1);
by (rtac ExEl_NotEmpty 1);
by (res_inst_tac [("x","e")] exI 1);
by (rtac CollectI 1);
by (rtac conjI 1);
by (rtac Iunity_closed 1);
by (rtac Icoset_mul_unity 1);
by (rtac (q2 RS (q1 RS M1_subset_G)) 1);
by (rtac ballI 1);
by (rtac CollectI 1);
by (dtac CollectD 1);
by (rtac conjI 1);
by (rtac Iinvers_closed 1);
by (etac conjunct1 1);
by (ftac conjunct2 1);
by (eres_inst_tac [("P","%z. z #> inv x = M1")] subst 1);
by (stac Icoset_mul_assoc 1);
by (rtac (q2 RS (q1 RS M1_subset_G)) 1);
by (etac conjunct1 1);
by (rtac Iinvers_closed 1);
by (etac conjunct1 1);
by (stac Iinvers_ax1 1);
by (etac conjunct1 1);
by (rtac Icoset_mul_unity 1);
by (rtac (q2 RS (q1 RS M1_subset_G)) 1);
by (rtac ballI 1);
by (rtac ballI 1);
by (rtac (q2 RS( q1 RS bin_op_closed_lemma)) 1);
by (assume_tac 1);
by (assume_tac 1);
qed "H_is_SG";

val [q1,q2,q3] = goal Sylow.thy  "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1 \\<in> M; M2 \\<in> M|] ==> \\<exists>g \\<in> carrier G. M1 #> g = M2";
val l1 = (q1 RS conjunct1) RS (RelM_equiv RS ElemClassEquiv);
val l2 = q2 RS ((q3 RS (l1 RS bspec)) RS bspec);
by (rtac bex_sym 1);
by (res_inst_tac [("P","(M2, M1)\\<in>calM <*> calM")] conjunct2 1);
by (res_inst_tac [("x","M2"),("y","M1")] CollectD_prod 1);
by (fold_goals_tac [RelM_def]);
by (rtac l2 1);
qed "M_elem_map";

val [q1,q2,q3] = goal Sylow.thy  "[|M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1 \\<in> M; H\\<in>set_r_cos G {g. g\\<in>carrier G & M1 #> g = M1} |] ==>\
\                \\<exists>g \\<in> carrier G. {g. g\\<in>carrier G & M1 #> g = M1} #> g = H";
by (rtac bex_sym 1);
by (res_inst_tac [("a","H")] CollectD 1);
by (rewtac r_coset_abbr);
by (fold_goals_tac [set_r_cos_def]);
by (fold_goals_tac [r_coset_abbr]);
by (rtac q3 1);
qed "H_elem_map";

val [q1,q2,q3,q4] = goal Sylow.thy  "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1 \\<in> M; g\\<in>carrier G; x\\<in>M1 #>  g |] ==> x\\<in>carrier G";
by (rtac (q4 RSN(2, mp)) 1);
by (rtac impI 1);
by (rewrite_goals_tac [r_coset_abbr,r_coset_def]);
by (fold_goals_tac [bin_op_abbr]);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac subst 1);
by (rtac Ibin_op_closed 1);
by (rtac q3 2);
by (etac (q2 RS( q1 RS M1_subset_G) RS subsetD) 1);
qed "rcosetGM1g_subset_G";

val [q1,q2] = goal Sylow.thy  "[|M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1 \\<in> M|] ==> finite M1";
by (rtac finite_subset 1);
by (rtac (q2 RS (q1 RS M1_subset_G)) 1);
by (rtac p4 1);
qed "finite_M1";

val [q1,q2,q3] = goal Sylow.thy  "[|M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1 \\<in> M; g\\<in>carrier G|] ==> finite (M1 #> g)";
by (rtac finite_subset 1);
by (rtac subsetI 1);
by (etac (q3 RS( q2 RS (q1 RS rcosetGM1g_subset_G))) 1);
by (rtac p4 1);
qed "finite_rcosetGM1g";

val [q1,q2,q3] = goal Sylow.thy  "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1 \\<in> M; g\\<in>carrier G|] ==> card(M1) = card(M1 #> g)";
by (rewtac r_coset_abbr);
by (rtac sym 1);
by (rtac (p2 RS card_cosets_equal RS bspec) 1);
by (rtac (q2 RS (q1 RS M1_subset_G)) 1);
by (rtac p4 1);
by (rewtac set_r_cos_def);
by (Step_tac 1);
by (rtac bexI 1);
by (rtac refl 1);
by (rtac q3 1);
qed "M1_cardeq_rcosetGM1g";

val [q1,q2,q3] = goal Sylow.thy  "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1 \\<in> M; g\\<in>carrier G|] ==> (M1, M1 #> g)\\<in>RelM";
val l1 = (q2 RS (q1 RS M1_subset_G));
val l2 = q3 RS (q2 RS (q1 RS rcosetGM1g_subset_G));
by (rewtac RelM_def);
by (rtac CollectI_prod 1);
by (rtac conjI 1);
by (rtac SigmaI 1);
by (SELECT_GOAL (rewtac calM_def) 1);
by (rtac CollectI 1);
by (rtac conjI 1);
by (rtac (q2 RS (q1 RS card_M1)) 2);
by (rtac l1 1);

by (rewtac calM_def);
by (rtac CollectI 1);
by (rtac conjI 1);
by (rtac (q3 RS (q2 RS (q1 RS M1_cardeq_rcosetGM1g)) RS subst) 2);
by (rtac (q2 RS (q1 RS card_M1)) 2);
by (rtac subsetI 1);
by (etac l2 1);
by (res_inst_tac [("x","inv g")] bexI 1);
by (stac Icoset_mul_assoc 1);
by (rtac l1 1);
by (rtac q3 1);
by (rtac (q3 RS Iinvers_closed) 1);
by (stac Iinvers_ax1 1);
by (rtac q3 1);
by (rtac (Icoset_mul_unity RS sym) 1);
by (rtac l1 1);
by (rtac (q3 RS Iinvers_closed) 1);
qed "M1_RelM_rcosetGM1g";

val [q1,q2] = goal Sylow.thy  "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\        M1\\<in>M|] ==> (\\<exists>f \\<in> M -> set_r_cos G {g. g\\<in>carrier G & M1 #> g = M1}. inj_on f M )\
\                   & (\\<exists>g \\<in> (set_r_cos G {g. g\\<in>carrier G & M1 #> g = M1}) -> M. \
\                                  inj_on g (set_r_cos G {g. g\\<in>carrier G & M1 #> g = M1}))";
by (rtac conjI 1);
by (res_inst_tac 
[("x","% M. {g. g\\<in>carrier G & M1 #> g = M1} #> (@ g. g\\<in>carrier G & M1 #> g = M)")]
bexI 1);
by (SELECT_GOAL (rewtac funcset_def) 2);
by (rtac CollectI 2);
by (rtac ballI 2);
by (SELECT_GOAL (rewtac set_r_cos_def) 2);
by (fold_goals_tac [r_coset_abbr]);
by (rtac CollectI 2);
by (rtac bexI 2);
by (rtac refl 2);
val l1 = (q2 RS(q1 RS M_elem_map)) RS (Bex_def RS apply_def) RS (Ex_def RS apply_def);
by (rtac (l1 RS conjunct1) 2);
by (assume_tac 2);
by (rtac inj_onI 1);
by (rtac ((l1 RS conjunct2) RS subst) 1);
by (assume_tac 1);
by (res_inst_tac [("P","% z. z = M1 #> (@ x. x\\<in>carrier G & M1 #> x = y)")] subst 1);
by (rtac (l1 RS conjunct2) 1);
by (assume_tac 1);
by (rtac Icoset_mul_invers1 1);
by (etac (l1 RS conjunct1) 1);
by (etac (l1 RS conjunct1) 1);
by (rtac (q2 RS (q1 RS M1_subset_G)) 1);
by (res_inst_tac 
[("P","(@ xa. xa\\<in>carrier G & M1 #> xa = x) ## (inv (@ x. x\\<in>carrier G & M1 #> x = y))\\<in>carrier G")] 
conjunct2 1);
by (res_inst_tac 
[("a","(@ xa. xa\\<in>carrier G & M1 #> xa = x) ## (inv (@ x. x\\<in>carrier G & M1 #> x = y))")] 
CollectD 1);
by (rtac (H_is_SG RSN(2, Icoset_join1)) 1);
by (rtac Ibin_op_closed 1);
by (etac (l1 RS conjunct1) 1);
by (rtac Iinvers_closed 1);
by (etac (l1 RS conjunct1) 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac Icoset_mul_invers2 1);
by (etac (l1 RS conjunct1) 1);
by (etac (l1 RS conjunct1) 1);
by (rtac subsetI 1);
by (dtac CollectD 1);
by (etac conjunct1 1);
by (assume_tac 1);
by (res_inst_tac [("x","% C. M1 #> (@g. g\\<in>carrier G &\
\ {g. g \\<in> carrier G & M1 #> g = M1} #> g = C)")] bexI 1);
by (rewtac funcset_def);
by (rtac CollectI 2);
by (rtac ballI 2);
by (rtac ((q2 RS (q1 RS M1_RelM_rcosetGM1g)) RSN (4, EquivElemClass)) 2);
by (rtac RelM_equiv 2);
by (rtac (q1 RS conjunct1) 2);
by (rtac q2 2);
by (SELECT_GOAL (rewtac set_r_cos_def) 2);
by (dtac CollectD 2);
by (dtac bex_sym 2);
by (fold_goals_tac [r_coset_abbr]);
by (rewrite_goals_tac [Bex_def,Ex_def]);
by (etac conjunct1 2);
by (rtac inj_onI 1);
val l1 = (q2 RS (q1 RS H_elem_map)) RS (Bex_def RS apply_def) RS (Ex_def RS apply_def);
by (rtac (l1 RS conjunct2 RS subst) 1);
by (assume_tac 1); 
by (res_inst_tac [("t","x")] (l1 RS conjunct2 RS subst) 1);
by (assume_tac 1);
by (rtac Icoset_mul_invers1 1);
by (etac (l1 RS conjunct1) 1);
by (etac (l1 RS conjunct1) 1);
val l2 = (q2 RS (q1 RS H_is_SG));
by (rtac (l2 RS (subgroup_def RS apply_def) RS conjunct1) 1);
by (rtac Icoset_join2 1);
by (rtac Ibin_op_closed 1);
by (etac (l1 RS conjunct1) 1);
by (rtac Iinvers_closed 1);
by (etac (l1 RS conjunct1) 1);
by (rtac l2 1);
by (rtac CollectI 1);
by (rtac conjI 1);
by (rtac Ibin_op_closed 1);
by (etac (l1 RS conjunct1) 1);
by (rtac Iinvers_closed 1);
by (etac (l1 RS conjunct1) 1);
by (rtac Icoset_mul_invers2 1);
by (assume_tac 4);
by (etac (l1 RS conjunct1) 1);
by (etac (l1 RS conjunct1) 1);
by (rtac (q2 RS (q1 RS M1_subset_G)) 1);
qed "bij_M_GmodH";

goal Sylow.thy "calM <= Pow(carrier G)";
by (rtac subsetI 1);
by (rtac PowI 1);
by (rewtac calM_def);
by (dtac CollectD 1);
by (etac conjunct1 1);
qed "calM_subset_PowG";

val [q1] = goal Sylow.thy "M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M)) ==> finite M";
by (rtac finite_subset 1);
by (rtac (q1 RS M_subset_calM RS subset_trans) 1);
by (rtac calM_subset_PowG 1);
by (rtac (p4 RS (finite_Pow_iff RS iffD2)) 1);
qed "finite_M";

val [q1,q2] = goal Sylow.thy "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1\\<in>M|] ==> card(M) = card(set_r_cos G {g. g\\<in>carrier G & M1 #> g = M1})";
by (rtac card_bij 1);
by (rtac (q1 RS finite_M) 1);
by (rtac finite_subset 1);
by (rtac (p2 RS set_r_cos_subset_PowG) 1);
by (rtac (q2 RS( q1 RS H_is_SG)) 1);
by (rtac (p4 RS (finite_Pow_iff RS iffD2)) 1);
val l1 = (q2 RS (q1 RS bij_M_GmodH));
by (rtac (l1 RS conjunct1) 1);
by (rtac (l1 RS conjunct2) 1);
qed "cardMeqIndexH";

val [q1,q2] = goal Sylow.thy "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1\\<in>M|] ==> (card(M) *  card({g. g\\<in>carrier G & M1 #> g = M1})) = order(G)";
by (rtac ((q2 RS( q1 RS cardMeqIndexH)) RS ssubst) 1);
by (rtac Lagrange 1);
by (rtac p2 1);
by (rtac p4 1);
by (rtac (q2 RS (q1 RS H_is_SG)) 1);
qed "index_lem";

val [q1,q2] = goal Sylow.thy
     "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\        M1\\<in>M |] \
\     ==> p ^ a <= card({g. g\\<in>carrier G & M1 #> g = M1})";
by (rtac dvd_imp_le 1);
by (res_inst_tac [("r","exponent p m"),("n", "card(M)")] div_combine 1);
by (rtac p1 1);
by (rtac SG_card1 3);
by (rtac p2 3);
by (rtac p4 3);
by (rtac (q2 RS (q1 RS H_is_SG)) 3);
by (rtac (q1 RS conjunct2) 1);
by (rtac (q2 RS (q1 RS index_lem) RS ssubst) 1);
by (stac p3 1);
by (stac power_add 1);
by (rtac mult_dvd_mono 1);
by (rtac dvd_refl 1);
by (rtac power_exponent_dvd 1);
by (rtac zero_less_m 1);
qed "lemma_leq1";

val [q1,q2] = goal Sylow.thy "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\    M1\\<in>M |] ==> card({g. g\\<in>carrier G & M1 #> g = M1}) <= p ^ a";
by (rtac (q2 RS (q1 RS card_M1) RS subst) 1);
by (rtac bexE 1);
by (rtac (q2 RS (q1 RS M1_inj_H)) 1);
by (rtac card_inj 1);
by (assume_tac 3);
by (assume_tac 3);
by (rtac finite_subset 2);
by (rtac p4 3);
by (rtac (q2 RS (q1 RS M1_subset_G)) 2);
by (rtac finite_subset 1);
by (rtac p4 2);
by (rtac subsetI 1);
by (etac subset_lemma1 1);
qed "lemma_leq2";

val [q1,q2] = goal Sylow.thy "[| M\\<in>calM // RelM & ~(p ^ ((exponent p m)+ 1) dvd card(M));\
\                M1\\<in>M|] ==> {g. g\\<in>carrier G & M1 #> g = M1} <<= G & \
\                 card({g. g\\<in>carrier G & M1 #> g = M1}) = p ^ a";
by (rtac conjI 1);
by (rtac le_anti_sym 2);
by (rtac (q2 RS( q1 RS H_is_SG)) 1);
by (rtac (q2 RS( q1 RS lemma_leq2)) 1);
by (rtac (q2 RS( q1 RS lemma_leq1)) 1);
qed "main_proof";

goal Sylow.thy "\\<exists>H. H <<= G & card(H) = p ^ a";
by (rtac exE 1);
by (rtac lemma_A1 1);
by (rtac exE 1);
by (etac existsM1inM 1);
by (dtac main_proof 1);
by (assume_tac 1);
by (etac exI 1);
qed "Sylow1";
