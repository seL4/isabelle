(*  Title:      HOL/GroupTheory/Sylow
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson

See Florian Kamm\"uller and L. C. Paulson,
    A Formal Proof of Sylow's theorem:
	An Experiment in Abstract Algebra with Isabelle HOL
    J. Automated Reasoning 23 (1999), 235-264
*)

header{*Sylow's theorem using locales*}

theory Sylow = Coset:

text{*The combinatorial argument is in theory Exponent*}

locale sylow = coset +
  fixes p and a and m and calM and RelM
  assumes prime_p:   "p \<in> prime"
      and order_G:   "order(G) = (p^a) * m"
      and finite_G [iff]:  "finite (carrier G)"
  defines "calM == {s. s <= carrier(G) & card(s) = p^a}"
      and "RelM == {(N1,N2). N1 \<in> calM & N2 \<in> calM &
		  	     (\<exists>g \<in> carrier(G). N1 = (N2 #> g) )}"

lemma (in sylow) RelM_refl: "refl calM RelM"
apply (unfold refl_def RelM_def, auto)
apply (simp add: calM_def)
apply (rule bexI [of _ \<zero>])
apply (auto simp add: zero_closed)
done

lemma (in sylow) RelM_sym: "sym RelM"
apply (unfold sym_def RelM_def, auto)
apply (rule_tac x = "gminus G g" in bexI)
apply (erule_tac [2] minus_closed)
apply (simp add: coset_sum_assoc calM_def)
done

lemma (in sylow) RelM_trans: "trans RelM"
apply (unfold trans_def RelM_def, auto)
apply (rule_tac x = "sum G ga g" in bexI)
apply (simp_all add: coset_sum_assoc calM_def)
done

lemma (in sylow) RelM_equiv: "equiv calM RelM"
apply (unfold equiv_def)
apply (blast intro: RelM_refl RelM_sym RelM_trans)
done

lemma (in sylow) M_subset_calM_prep: "M' \<in> calM // RelM  ==> M' <= calM"
apply (unfold RelM_def)
apply (blast elim!: quotientE)
done

subsection{*Main Part of the Proof*}


locale sylow_central = sylow +
  fixes H and M1 and M
  assumes M_in_quot:  "M \<in> calM // RelM"
      and not_dvd_M:  "~(p ^ Suc(exponent p m) dvd card(M))"
      and M1_in_M:    "M1 \<in> M"
  defines "H == {g. g\<in>carrier G & M1 #> g = M1}"

lemma (in sylow_central) M_subset_calM: "M <= calM"
by (rule M_in_quot [THEN M_subset_calM_prep])

lemma (in sylow_central) card_M1: "card(M1) = p^a"
apply (cut_tac M_subset_calM M1_in_M)
apply (simp add: calM_def, blast)
done

lemma (in sylow_central) exists_x_in_M1: "\<exists>x. x\<in>M1"
apply (subgoal_tac "0 < card M1") 
 apply (blast dest: card_nonempty) 
apply (cut_tac prime_p [THEN prime_imp_one_less])
apply (simp (no_asm_simp) add: card_M1)
done

lemma (in sylow_central) M1_subset_G [simp]: "M1 <= carrier G"
apply (rule subsetD [THEN PowD])
apply (rule_tac [2] M1_in_M)
apply (rule M_subset_calM [THEN subset_trans])
apply (auto simp add: calM_def)
done

lemma (in sylow_central) M1_inj_H: "\<exists>f \<in> H\<rightarrow>M1. inj_on f H"
apply (rule exists_x_in_M1 [THEN exE])
apply (rule_tac x = "%z: H. sum G x z" in bexI)
 apply (rule inj_onI)
 apply (rule left_cancellation)
    apply (auto simp add: H_def M1_subset_G [THEN subsetD])
apply (rule restrictI)
apply (simp add: H_def, clarify) 
apply (erule subst)
apply (simp add: rcosI)
done

subsection{*Discharging the Assumptions of @{text sylow_central}*}

lemma (in sylow) EmptyNotInEquivSet: "{} \<notin> calM // RelM"
by (blast elim!: quotientE dest: RelM_equiv [THEN equiv_class_self])

lemma (in sylow) existsM1inM: "M \<in> calM // RelM ==> \<exists>M1. M1 \<in> M"
apply (subgoal_tac "M \<noteq> {}") 
 apply blast 
apply (cut_tac EmptyNotInEquivSet, blast)
done

lemma (in sylow) zero_less_o_G: "0 < order(G)"
apply (unfold order_def)
apply (cut_tac zero_closed)
apply (blast intro: zero_less_card_empty)
done

lemma (in sylow) zero_less_m: "0 < m"
apply (cut_tac zero_less_o_G)
apply (simp add: order_G)
done

lemma (in sylow) card_calM: "card(calM) = (p^a) * m choose p^a"
by (simp add: calM_def n_subsets order_G [symmetric] order_def)

lemma (in sylow) zero_less_card_calM: "0 < card calM"
by (simp add: card_calM zero_less_binomial le_extend_mult zero_less_m)

lemma (in sylow) max_p_div_calM:
     "~ (p ^ Suc(exponent p m) dvd card(calM))"
apply (subgoal_tac "exponent p m = exponent p (card calM) ")
 apply (cut_tac zero_less_card_calM prime_p)
 apply (force dest: power_Suc_exponent_Not_dvd)
apply (simp add: card_calM zero_less_m [THEN const_p_fac])
done

lemma (in sylow) finite_calM: "finite calM"
apply (unfold calM_def)
apply (rule_tac B = "Pow (carrier G) " in finite_subset)
apply auto
done

lemma (in sylow) lemma_A1:
     "\<exists>M \<in> calM // RelM. ~ (p ^ Suc(exponent p m) dvd card(M))"
apply (rule max_p_div_calM [THEN contrapos_np])
apply (simp add: finite_calM equiv_imp_dvd_card [OF _ RelM_equiv])
done


subsubsection{*Introduction and Destruct Rules for @{term H}*}

lemma (in sylow_central) H_I: "[|g \<in> carrier G; M1 #> g = M1|] ==> g \<in> H"
by (simp add: H_def)

lemma (in sylow_central) H_into_carrier_G: "x \<in> H ==> x \<in> carrier G"
by (simp add: H_def)

lemma (in sylow_central) in_H_imp_eq: "g : H ==> M1 #> g = M1"
by (simp add: H_def)

lemma (in sylow_central) H_sum_closed: "[| x\<in>H; y\<in>H|] ==> x \<oplus> y \<in> H"
apply (unfold H_def)
apply (simp add: coset_sum_assoc [symmetric] sum_closed)
done

lemma (in sylow_central) H_not_empty: "H \<noteq> {}"
apply (simp add: H_def)
apply (rule exI [of _ \<zero>], simp)
done

lemma (in sylow_central) H_is_subgroup: "subgroup H G"
apply (rule subgroupI)
apply (rule subsetI)
apply (erule H_into_carrier_G)
apply (rule H_not_empty)
apply (simp add: H_def, clarify)
apply (erule_tac P = "%z. ?lhs(z) = M1" in subst)
apply (simp add: coset_sum_assoc )
apply (blast intro: H_sum_closed)
done


lemma (in sylow_central) rcosetGM1g_subset_G:
     "[| g \<in> carrier G; x \<in> M1 #>  g |] ==> x \<in> carrier G"
by (blast intro: M1_subset_G [THEN r_coset_subset_G, THEN subsetD])

lemma (in sylow_central) finite_M1: "finite M1"
by (rule finite_subset [OF M1_subset_G finite_G])

lemma (in sylow_central) finite_rcosetGM1g: "g\<in>carrier G ==> finite (M1 #> g)"
apply (rule finite_subset)
apply (rule subsetI)
apply (erule rcosetGM1g_subset_G, assumption)
apply (rule finite_G)
done

lemma (in sylow_central) M1_cardeq_rcosetGM1g:
     "g \<in> carrier G ==> card(M1 #> g) = card(M1)"
by (simp (no_asm_simp) add: M1_subset_G card_cosets_equal setrcosI)

lemma (in sylow_central) M1_RelM_rcosetGM1g:
     "g \<in> carrier G ==> (M1, M1 #> g) \<in> RelM"
apply (simp (no_asm) add: RelM_def calM_def card_M1 M1_subset_G)
apply (rule conjI)
 apply (blast intro: rcosetGM1g_subset_G)
apply (simp (no_asm_simp) add: card_M1 M1_cardeq_rcosetGM1g)
apply (rule bexI [of _ "\<ominus>g"])
apply (simp_all add: coset_sum_assoc M1_subset_G)
done



subsection{*Equal Cardinalities of @{term M} and @{term "rcosets G H"}*}

text{*Injections between @{term M} and @{term "rcosets G H"} show that
 their cardinalities are equal.*}

lemma ElemClassEquiv: 
     "[| equiv A r; C\<in>A // r |] ==> \<forall>x \<in> C. \<forall>y \<in> C. (x,y)\<in>r"
apply (unfold equiv_def quotient_def sym_def trans_def, blast)
done

lemma (in sylow_central) M_elem_map:
     "M2 \<in> M ==> \<exists>g. g \<in> carrier G & M1 #> g = M2"
apply (cut_tac M1_in_M M_in_quot [THEN RelM_equiv [THEN ElemClassEquiv]])
apply (simp add: RelM_def)
apply (blast dest!: bspec)
done

lemmas (in sylow_central) M_elem_map_carrier = 
	M_elem_map [THEN someI_ex, THEN conjunct1]

lemmas (in sylow_central) M_elem_map_eq =
	M_elem_map [THEN someI_ex, THEN conjunct2]

lemma (in sylow_central) M_funcset_setrcos_H:
     "(%x:M. H #> (SOME g. g \<in> carrier G & M1 #> g = x)) \<in> M \<rightarrow> rcosets G H"
apply (rule setrcosI [THEN restrictI])
apply (rule H_is_subgroup [THEN subgroup_imp_subset])
apply (erule M_elem_map_carrier)
done

lemma (in sylow_central) inj_M_GmodH: "\<exists>f \<in> M\<rightarrow>rcosets G H. inj_on f M"
apply (rule bexI)
apply (rule_tac [2] M_funcset_setrcos_H)
apply (rule inj_onI, simp)
apply (rule trans [OF _ M_elem_map_eq])
prefer 2 apply assumption
apply (rule M_elem_map_eq [symmetric, THEN trans], assumption)
apply (rule coset_sum_minus1)
apply (erule_tac [2] M_elem_map_carrier)+
apply (rule_tac [2] M1_subset_G)
apply (rule coset_join1 [THEN in_H_imp_eq])
apply (rule_tac [3] H_is_subgroup)
prefer 2 apply (blast intro: sum_closed M_elem_map_carrier minus_closed)
apply (simp add: coset_sum_minus2 H_def M_elem_map_carrier subset_def)
done


(** the opposite injection **)

lemma (in sylow_central) H_elem_map:
     "H1\<in>rcosets G H ==> \<exists>g. g \<in> carrier G & H #> g = H1"
by (auto simp add: setrcos_eq)

lemmas (in sylow_central) H_elem_map_carrier = 
	H_elem_map [THEN someI_ex, THEN conjunct1]

lemmas (in sylow_central) H_elem_map_eq =
	H_elem_map [THEN someI_ex, THEN conjunct2]


lemma EquivElemClass: 
     "[|equiv A r; M\<in>A // r; M1\<in>M; (M1, M2)\<in>r |] ==> M2\<in>M"
apply (unfold equiv_def quotient_def sym_def trans_def, blast)
done

lemma (in sylow_central) setrcos_H_funcset_M:
     "(\<lambda>C \<in> rcosets G H. M1 #> (@g. g \<in> carrier G \<and> H #> g = C))
      \<in> rcosets G H \<rightarrow> M"
apply (simp add: setrcos_eq)
apply (fast intro: someI2
            intro!: restrictI M1_in_M
              EquivElemClass [OF RelM_equiv M_in_quot _  M1_RelM_rcosetGM1g])
done

text{*close to a duplicate of @{text inj_M_GmodH}*}
lemma (in sylow_central) inj_GmodH_M:
     "\<exists>g \<in> rcosets G H\<rightarrow>M. inj_on g (rcosets G H)"
apply (rule bexI)
apply (rule_tac [2] setrcos_H_funcset_M)
apply (rule inj_onI)
apply (rotate_tac -2, simp)
apply (rule trans [OF _ H_elem_map_eq])
prefer 2 apply assumption
apply (rule H_elem_map_eq [symmetric, THEN trans], assumption)
apply (rule coset_sum_minus1)
apply (erule_tac [2] H_elem_map_carrier)+
apply (rule_tac [2] H_is_subgroup [THEN subgroup_imp_subset])
apply (rule coset_join2)
apply (blast intro: sum_closed minus_closed H_elem_map_carrier)
apply (rule H_is_subgroup) 
apply (simp add: H_I coset_sum_minus2 M1_subset_G H_elem_map_carrier)
done

lemma (in sylow_central) calM_subset_PowG: "calM <= Pow(carrier G)"
by (auto simp add: calM_def)


lemma (in sylow_central) finite_M: "finite M"
apply (rule finite_subset)
apply (rule M_subset_calM [THEN subset_trans])
apply (rule calM_subset_PowG, blast)
done

lemma (in sylow_central) cardMeqIndexH: "card(M) = card(rcosets G H)"
apply (insert inj_M_GmodH inj_GmodH_M) 
apply (blast intro: card_bij finite_M H_is_subgroup 
             setrcos_subset_PowG [THEN finite_subset] 
             finite_Pow_iff [THEN iffD2])
done

lemma (in sylow_central) index_lem: "card(M) * card(H) = order(G)"
by (simp add: cardMeqIndexH lagrange H_is_subgroup)

lemma (in sylow_central) lemma_leq1: "p^a <= card(H)"
apply (rule dvd_imp_le)
 apply (rule div_combine [OF prime_p not_dvd_M])
 prefer 2 apply (blast intro: subgroup_card_positive H_is_subgroup)
apply (simp add: index_lem order_G power_add mult_dvd_mono power_exponent_dvd
                 zero_less_m)
done

lemma (in sylow_central) lemma_leq2: "card(H) <= p^a"
apply (subst card_M1 [symmetric])
apply (cut_tac M1_inj_H)
apply (blast intro!: M1_subset_G intro: 
             card_inj H_into_carrier_G finite_subset [OF _ finite_G])
done

lemma (in sylow_central) card_H_eq: "card(H) = p^a"
by (blast intro: le_anti_sym lemma_leq1 lemma_leq2)

lemma (in sylow) sylow_thm: "\<exists>H. subgroup H G & card(H) = p^a"
apply (cut_tac lemma_A1, clarify) 
apply (frule existsM1inM, clarify) 
apply (subgoal_tac "sylow_central G p a m M1 M")
 apply (blast dest:  sylow_central.H_is_subgroup sylow_central.card_H_eq)
apply (simp add: sylow_central_def sylow_central_axioms_def prems) 
done

text{*Needed because the locale's automatic definition refers to
   @{term "semigroup G"} and @{term "group_axioms G"} rather than 
  simply to @{term "group G"}.*}
lemma sylow_eq: "sylow G p a m = (group G & sylow_axioms G p a m)"
by (simp add: sylow_def group_def)

theorem sylow_thm:
     "[|p \<in> prime;  group(G);  order(G) = (p^a) * m; finite (carrier G)|]
      ==> \<exists>H. subgroup H G & card(H) = p^a"
apply (rule sylow.sylow_thm [of G p a m])
apply (simp add: sylow_eq sylow_axioms_def) 
done

end
