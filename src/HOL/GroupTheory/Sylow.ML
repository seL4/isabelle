(*  Title:      HOL/GroupTheory/Sylow
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Sylow's theorem using locales (combinatorial argument in Exponent.thy)

See Florian Kamm\"uller and L. C. Paulson,
    A Formal Proof of Sylow's theorem:
	An Experiment in Abstract Algebra with Isabelle HOL
    J. Automated Reasoning 23 (1999), 235-264
*)

Open_locale "sylow";

val prime_p = thm "prime_p";
val order_G = thm "order_G";
val finite_G = thm "finite_G";
val calM_def = thm "calM_def";
val RelM_def = thm "RelM_def";

AddIffs [finite_G];
Addsimps [coset_mul_e];

Goalw [refl_def, RelM_def] "refl calM RelM";
by Auto_tac; 
by (asm_full_simp_tac (simpset() addsimps [calM_def]) 1); 
by (res_inst_tac [("x","e")] bexI 1);
by (auto_tac (claset(), simpset() addsimps [e_closed])); 
qed "RelM_refl";

Goalw [sym_def, RelM_def] "sym RelM";
by Auto_tac; 
by (res_inst_tac [("x","i g")] bexI 1);
by (etac inv_closed 2);
by (asm_full_simp_tac
    (simpset() addsimps [coset_mul_assoc, calM_def, inv_closed]) 1); 
qed "RelM_sym";

Goalw [trans_def, RelM_def] "trans RelM";
by Auto_tac; 
by (res_inst_tac [("x","ga ## g")] bexI 1);
by (ALLGOALS (asm_full_simp_tac
              (simpset() addsimps [coset_mul_assoc, calM_def, binop_closed])));
qed "RelM_trans";

Goalw [equiv_def] "equiv calM RelM";
by (blast_tac (claset() addIs [RelM_refl, RelM_sym, RelM_trans]) 1); 
qed "RelM_equiv";

Goalw [RelM_def] "M \\<in> calM // RelM  ==> M <= calM";
by (blast_tac (claset() addSEs [quotientE]) 1); 
qed "M_subset_calM_prep";

(*** Central Part of the Proof ***)

Open_locale "sylow_central";

val M_in_quot = thm "M_in_quot";
val not_dvd_M = thm "not_dvd_M";
val M1_in_M = thm "M1_in_M";
val H_def = thm "H_def";

Goal "M <= calM";
by (rtac (M_in_quot RS M_subset_calM_prep) 1);
qed "M_subset_calM";

Goal "card(M1) = p^a";
by (cut_facts_tac [M_subset_calM, M1_in_M] 1); 
by (asm_full_simp_tac (simpset() addsimps [calM_def]) 1); 
by (Blast_tac 1); 
qed "card_M1";

Goal "\\<exists>x. x\\<in>M1";
by (rtac (card_nonempty RS NotEmpty_ExEl) 1);
by (cut_facts_tac [prime_p RS prime_imp_one_less] 1);
by (asm_simp_tac (simpset() addsimps [card_M1]) 1);
qed "exists_x_in_M1";

Goal "M1 <= carrier G";
by (rtac (subsetD RS PowD) 1);
by (rtac M1_in_M 2);
by (rtac (M_subset_calM RS subset_trans) 1);
by (auto_tac (claset(), simpset() addsimps [calM_def])); 
qed "M1_subset_G";

Goal "\\<exists>f \\<in> H\\<rightarrow>M1. inj_on f H";
by (rtac (exists_x_in_M1 RS exE) 1);
by (res_inst_tac [("x", "%z: H. x ## z")] bexI 1);
by (rtac restrictI 2);
by (asm_full_simp_tac (simpset() addsimps [H_def]) 2); 
by (Clarify_tac 2);
by (etac subst 2);
by (asm_full_simp_tac (simpset() addsimps [rcosI, M1_subset_G]) 2);
by (rtac inj_onI 1);
by (rtac left_cancellation 1);
by (auto_tac (claset(), simpset() addsimps [H_def, M1_subset_G RS subsetD])); 
qed "M1_inj_H";

Goal "{} \\<notin> calM // RelM";
by (blast_tac (claset() addSEs [quotientE]
			addDs [RelM_equiv RS equiv_class_self]) 1); 
qed "EmptyNotInEquivSet";

Goal "\\<exists>M1. M1\\<in>M";
by (cut_facts_tac [M_in_quot, EmptyNotInEquivSet] 1); 
by (blast_tac (claset() addIs [NotEmpty_ExEl]) 1); 
qed "existsM1inM";
val ExistsM1inM = Export existsM1inM;

Goalw [order_def] "0 < order(G)";
by (cut_facts_tac [e_closed] 1);
by (blast_tac (claset() addIs [zero_less_card_empty]) 1); 
qed "zero_less_o_G";

Goal "0 < m";
by (cut_facts_tac [zero_less_o_G] 1);
by (asm_full_simp_tac (simpset() addsimps [order_G]) 1); 
qed "zero_less_m";

Goal "card(calM) = (p^a) * m choose p^a";
by (simp_tac (simpset() addsimps [calM_def, n_subsets, 
                                  order_G RS sym, order_def]) 1);  
qed "card_calM";

Goal "0 < card calM";
by (simp_tac (simpset() addsimps [card_calM, zero_less_binomial, 
                                  le_extend_mult, zero_less_m]) 1); 
qed "zero_less_card_calM";

Goal "~ (p ^ Suc(exponent p m) dvd card(calM))";
by (subgoal_tac "exponent p m = exponent p (card calM)" 1);
 by (asm_full_simp_tac (simpset() addsimps [card_calM, 
                           zero_less_m RS const_p_fac]) 2);
by (cut_facts_tac [zero_less_card_calM, prime_p] 1);
by (force_tac (claset() addDs [power_Suc_exponent_Not_dvd], simpset()) 1); 
qed "max_p_div_calM";

Goalw [calM_def] "finite calM";
by (res_inst_tac [("B", "Pow (carrier G)")] finite_subset 1);
by Auto_tac; 
qed "finite_calM";

Goal "\\<exists>M \\<in> calM // RelM. ~ (p ^ Suc(exponent p m) dvd card(M))";
by (rtac (max_p_div_calM RS contrapos_np) 1); 
by (asm_full_simp_tac (simpset() addsimps [finite_calM, 
                          RelM_equiv RSN(2, equiv_imp_dvd_card)]) 1); 
qed "lemma_A1";
val Lemma_A1 = Export lemma_A1;

Goal "x \\<in> H ==> x \\<in> carrier G";
by (afs [H_def] 1);
qed "H_into_carrier_G";

Goal "g : H ==> M1 #> g = M1";
by (asm_full_simp_tac (simpset() addsimps [H_def]) 1); 
qed "in_H_imp_eq";

Goalw [H_def] "[| x\\<in>H; xa\\<in>H|] ==> x ## xa\\<in>H";
by (asm_full_simp_tac (simpset() addsimps [coset_mul_assoc RS sym, 
                                    binop_closed, M1_subset_G]) 1); 
qed "bin_op_closed_lemma";

Goal "H \\<noteq> {}";
by (asm_full_simp_tac (simpset() addsimps [H_def]) 1); 
by (res_inst_tac [("x","e")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [e_closed, M1_subset_G]) 1); 
qed "H_not_empty";

Goal "H <<= G";
by (rtac subgroupI 1);
by (rtac subsetI 1);
by (etac H_into_carrier_G 1);
by (rtac H_not_empty 1);
by (afs [H_def, inv_closed] 1);
by (Clarify_tac 1); 
by (eres_inst_tac [("P","%z. z #> i a = M1")] subst 1);
by (asm_simp_tac (simpset() addsimps [coset_mul_assoc, inv_closed, 
           inv_ax1, coset_mul_e, M1_subset_G]) 1); 
by (blast_tac (claset() addIs [bin_op_closed_lemma]) 1); 
qed "H_is_SG";
val H_is_subgroup = Export H_is_SG;

Goal "[| g\\<in>carrier G; x\\<in>M1 #>  g |] ==> x\\<in>carrier G";
by (rtac (r_coset_subset_G RS subsetD) 1);
by (assume_tac 3);
by (assume_tac 2);
by (rtac M1_subset_G 1);
qed "rcosetGM1g_subset_G";

Goal "finite M1";
by (rtac ([ M1_subset_G, finite_G] MRS finite_subset) 1);
qed "finite_M1";

Goal "g\\<in>carrier G ==> finite (M1 #> g)";
by (rtac finite_subset 1);
by (rtac subsetI 1);
by (etac rcosetGM1g_subset_G 1);
by (assume_tac 1);
by (rtac finite_G 1);
qed "finite_rcosetGM1g";

Goal "g\\<in>carrier G ==> card(M1 #> g) = card(M1)";
by (asm_simp_tac
    (simpset() addsimps [M1_subset_G, card_cosets_equal, setrcosI]) 1); 
qed "M1_cardeq_rcosetGM1g";

Goal "g \\<in> carrier G ==> (M1, M1 #> g) \\<in> RelM";
by (simp_tac (simpset() addsimps [RelM_def,calM_def,card_M1,M1_subset_G]) 1); 
by (rtac conjI 1);
 by (blast_tac (claset() addIs [rcosetGM1g_subset_G]) 1); 
by (asm_simp_tac (simpset() addsimps [card_M1, M1_cardeq_rcosetGM1g]) 1); 
by (res_inst_tac [("x","i g")] bexI 1);
by (asm_full_simp_tac (simpset() addsimps [coset_mul_assoc, M1_subset_G, 
                                           inv_closed, inv_ax1]) 1); 
by (asm_simp_tac (simpset() addsimps [inv_closed]) 1); 
qed "M1_RelM_rcosetGM1g";



(*** A pair of injections between M and {*H*} shows their cardinalities are 
     equal ***)

Goal "M2 \\<in> M ==> \\<exists>g. g \\<in> carrier G & M1 #> g = M2";
by (cut_facts_tac [M1_in_M, M_in_quot RS (RelM_equiv RS ElemClassEquiv)] 1);
by (asm_full_simp_tac (simpset() addsimps [RelM_def]) 1); 
by (blast_tac (claset() addSDs [bspec]) 1); 
qed "M_elem_map";

val M_elem_map_carrier = M_elem_map RS someI_ex RS conjunct1;
val M_elem_map_eq = M_elem_map RS someI_ex RS conjunct2;

Goal "(%x:M. H #> (SOME g. g \\<in> carrier G & M1 #> g = x)) \\<in> M \\<rightarrow> {* H *}";
by (rtac (setrcosI RS restrictI) 1);
by (rtac (H_is_SG RS subgroup_imp_subset) 1);
by (etac M_elem_map_carrier 1);
qed "M_funcset_setrcos_H";

Goal "\\<exists>f \\<in> M\\<rightarrow>{* H *}. inj_on f M";
by (rtac bexI 1);
by (rtac M_funcset_setrcos_H 2);
by (rtac inj_onI 1);
by (Asm_full_simp_tac 1);
by (rtac ([asm_rl,M_elem_map_eq] MRS trans) 1);  
by (assume_tac 2);
by (rtac ((M_elem_map_eq RS sym) RS trans) 1); 
by (assume_tac 1);
by (rtac coset_mul_inv1 1);
by (REPEAT (etac M_elem_map_carrier 2));
by (rtac M1_subset_G 2);
by (rtac (coset_join1 RS in_H_imp_eq) 1); 
by (rtac H_is_SG 3);
by (blast_tac (claset() addIs [binop_closed,M_elem_map_carrier,inv_closed]) 2);
by (asm_full_simp_tac (simpset() addsimps [coset_mul_invers2, H_def, 
                            M_elem_map_carrier, subset_def]) 1); 
qed "inj_M_GmodH";


(** the opposite injection **)

Goal "H1\\<in>{* H *} ==> \\<exists>g. g \\<in> carrier G & H #> g = H1";
by (auto_tac (claset(), simpset() addsimps [setrcos_eq])); 
qed "H_elem_map";

val H_elem_map_carrier = H_elem_map RS someI_ex RS conjunct1;
val H_elem_map_eq = H_elem_map RS someI_ex RS conjunct2;

Goal "(%C:{*H*}. M1 #> (@g. g \\<in> (G .<cr>) \\<and> H #> g = C)) \\<in> {* H *} \\<rightarrow> M";
by (simp_tac (simpset() addsimps [setrcos_eq]) 1);
by (fast_tac (claset() addIs [someI2] 
            addSIs [restrictI, RelM_equiv, M_in_quot,
                    [RelM_equiv,M_in_quot,asm_rl,M1_RelM_rcosetGM1g] MRS EquivElemClass, M1_in_M]) 1);
qed "setrcos_H_funcset_M";

Goal "\\<exists>g \\<in> {* H *}\\<rightarrow>M. inj_on g ({* H *})";
by (rtac bexI 1);
by (rtac setrcos_H_funcset_M 2);
by (rtac inj_onI 1);
by (rotate_tac ~2 1);
by (Asm_full_simp_tac 1); 
by (rtac ([asm_rl,H_elem_map_eq] MRS trans) 1);  
by (assume_tac 2);
by (rtac ((H_elem_map_eq RS sym) RS trans) 1); 
by (assume_tac 1);
by (rtac coset_mul_inv1 1);
by (REPEAT (etac H_elem_map_carrier 2));
by (rtac (H_is_SG RS subgroup_imp_subset) 2);
by (rtac coset_join2 1);
by (blast_tac (claset() addIs [binop_closed,inv_closed,H_elem_map_carrier]) 1);
by (rtac H_is_SG 1);
by (asm_full_simp_tac (simpset() addsimps [H_def, coset_mul_invers2, 
                               M1_subset_G, H_elem_map_carrier]) 1); 
qed "inj_GmodH_M";

Goal "calM <= Pow(carrier G)";
by (auto_tac (claset(), simpset() addsimps [calM_def])); 
qed "calM_subset_PowG";


Goal "finite M";
by (rtac finite_subset 1);
by (rtac (M_subset_calM RS subset_trans) 1);
by (rtac calM_subset_PowG 1);
by (Blast_tac 1); 
qed "finite_M";

Goal "card(M) = card({* H *})";
by (blast_tac (claset() addSIs [inj_M_GmodH,inj_GmodH_M]
                  addIs [card_bij, finite_M, H_is_SG, 
                         setrcos_subset_PowG RS finite_subset, 
                         finite_Pow_iff RS iffD2]) 1);
qed "cardMeqIndexH";

Goal "card(M) * card(H) = order(G)";
by (simp_tac (simpset() addsimps [cardMeqIndexH,lagrange, H_is_SG]) 1); 
qed "index_lem";

Goal "p^a <= card(H)";
by (rtac ([prime_p,not_dvd_M] MRS div_combine RS dvd_imp_le) 1); 
by (blast_tac (claset() addIs [SG_card1,H_is_SG]) 2); 
by (simp_tac (simpset() addsimps [index_lem,order_G,power_add,mult_dvd_mono,
                                  power_exponent_dvd,zero_less_m]) 1); 
qed "lemma_leq1";

Goal "card(H) <= p^a";
by (stac (card_M1 RS sym) 1);
by (cut_facts_tac [M1_inj_H] 1);
by (blast_tac (claset() addSIs [M1_subset_G]
			addIs [card_inj, H_into_carrier_G,
                               finite_G RSN(2, finite_subset)]) 1); 
qed "lemma_leq2";

Goal "card(H) = p^a";
by (blast_tac (claset() addIs [le_anti_sym, lemma_leq1, lemma_leq2]) 1); 
qed "card_H_eq";
val Card_H_eq = Export card_H_eq; 

Close_locale "sylow_central";

Goal "\\<exists>H. H <<= G & card(H) = p^a";
by (cut_facts_tac [Lemma_A1] 1);
by (blast_tac (claset() addDs [ExistsM1inM, H_is_subgroup, Card_H_eq]) 1); 
qed "sylow1";
val Sylow1 = export sylow1;

Close_locale "sylow";
Close_locale "coset";
Close_locale "group";
