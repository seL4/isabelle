(*  Title:      HOL/Algebra/Sylow.thy
    Author:     Florian Kammueller, with new proofs by L C Paulson
*)

theory Sylow
  imports Coset Exponent
begin

text \<open>See also @{cite "Kammueller-Paulson:1999"}.\<close>

text \<open>The combinatorial argument is in theory @{theory Exponent}.\<close>

lemma le_extend_mult: "\<lbrakk>0 < c; a \<le> b\<rbrakk> \<Longrightarrow> a \<le> b * c"
  for c :: nat
  by (metis divisors_zero dvd_triv_left leI less_le_trans nat_dvd_not_less zero_less_iff_neq_zero)

locale sylow = group +
  fixes p and a and m and calM and RelM
  assumes prime_p: "prime p"
    and order_G: "order G = (p^a) * m"
    and finite_G[iff]: "finite (carrier G)"
  defines "calM \<equiv> {s. s \<subseteq> carrier G \<and> card s = p^a}"
    and "RelM \<equiv> {(N1, N2). N1 \<in> calM \<and> N2 \<in> calM \<and> (\<exists>g \<in> carrier G. N1 = N2 #> g)}"
begin

lemma RelM_refl_on: "refl_on calM RelM"
  by (auto simp: refl_on_def RelM_def calM_def) (blast intro!: coset_mult_one [symmetric])

lemma RelM_sym: "sym RelM"
proof (unfold sym_def RelM_def, clarify)
  fix y g
  assume "y \<in> calM"
    and g: "g \<in> carrier G"
  then have "y = y #> g #> (inv g)"
    by (simp add: coset_mult_assoc calM_def)
  then show "\<exists>g'\<in>carrier G. y = y #> g #> g'"
    by (blast intro: g)
qed

lemma RelM_trans: "trans RelM"
  by (auto simp add: trans_def RelM_def calM_def coset_mult_assoc)

lemma RelM_equiv: "equiv calM RelM"
  unfolding equiv_def by (blast intro: RelM_refl_on RelM_sym RelM_trans)

lemma M_subset_calM_prep: "M' \<in> calM // RelM  \<Longrightarrow> M' \<subseteq> calM"
  unfolding RelM_def by (blast elim!: quotientE)

end

subsection \<open>Main Part of the Proof\<close>

locale sylow_central = sylow +
  fixes H and M1 and M
  assumes M_in_quot: "M \<in> calM // RelM"
    and not_dvd_M: "\<not> (p ^ Suc (multiplicity p m) dvd card M)"
    and M1_in_M: "M1 \<in> M"
  defines "H \<equiv> {g. g \<in> carrier G \<and> M1 #> g = M1}"
begin

lemma M_subset_calM: "M \<subseteq> calM"
  by (rule M_in_quot [THEN M_subset_calM_prep])

lemma card_M1: "card M1 = p^a"
  using M1_in_M M_subset_calM calM_def by blast

lemma exists_x_in_M1: "\<exists>x. x \<in> M1"
  using prime_p [THEN prime_gt_Suc_0_nat] card_M1
  by (metis Suc_lessD card_eq_0_iff empty_subsetI equalityI gr_implies_not0 nat_zero_less_power_iff subsetI)

lemma M1_subset_G [simp]: "M1 \<subseteq> carrier G"
  using M1_in_M M_subset_calM calM_def mem_Collect_eq subsetCE by blast

lemma M1_inj_H: "\<exists>f \<in> H\<rightarrow>M1. inj_on f H"
proof -
  from exists_x_in_M1 obtain m1 where m1M: "m1 \<in> M1"..
  have m1: "m1 \<in> carrier G"
    by (simp add: m1M M1_subset_G [THEN subsetD])
  show ?thesis
  proof
    show "inj_on (\<lambda>z\<in>H. m1 \<otimes> z) H"
      by (simp add: H_def inj_on_def m1)
    show "restrict ((\<otimes>) m1) H \<in> H \<rightarrow> M1"
    proof (rule restrictI)
      fix z
      assume zH: "z \<in> H"
      show "m1 \<otimes> z \<in> M1"
      proof -
        from zH
        have zG: "z \<in> carrier G" and M1zeq: "M1 #> z = M1"
          by (auto simp add: H_def)
        show ?thesis
          by (rule subst [OF M1zeq]) (simp add: m1M zG rcosI)
      qed
    qed
  qed
qed

end


subsection \<open>Discharging the Assumptions of \<open>sylow_central\<close>\<close>

context sylow
begin

lemma EmptyNotInEquivSet: "{} \<notin> calM // RelM"
  by (blast elim!: quotientE dest: RelM_equiv [THEN equiv_class_self])

lemma existsM1inM: "M \<in> calM // RelM \<Longrightarrow> \<exists>M1. M1 \<in> M"
  using RelM_equiv equiv_Eps_in by blast

lemma zero_less_o_G: "0 < order G"
  by (simp add: order_def card_gt_0_iff carrier_not_empty)

lemma zero_less_m: "m > 0"
  using zero_less_o_G by (simp add: order_G)

lemma card_calM: "card calM = (p^a) * m choose p^a"
  by (simp add: calM_def n_subsets order_G [symmetric] order_def)

lemma zero_less_card_calM: "card calM > 0"
  by (simp add: card_calM zero_less_binomial le_extend_mult zero_less_m)

lemma max_p_div_calM: "\<not> (p ^ Suc (multiplicity p m) dvd card calM)"
proof
  assume "p ^ Suc (multiplicity p m) dvd card calM"
  with zero_less_card_calM prime_p
  have "Suc (multiplicity p m) \<le> multiplicity p (card calM)"
    by (intro multiplicity_geI) auto
  then have "multiplicity p m < multiplicity p (card calM)" by simp
  also have "multiplicity p m = multiplicity p (card calM)"
    by (simp add: const_p_fac prime_p zero_less_m card_calM)
  finally show False by simp
qed

lemma finite_calM: "finite calM"
  unfolding calM_def by (rule finite_subset [where B = "Pow (carrier G)"]) auto

lemma lemma_A1: "\<exists>M \<in> calM // RelM. \<not> (p ^ Suc (multiplicity p m) dvd card M)"
  using RelM_equiv equiv_imp_dvd_card finite_calM max_p_div_calM by blast

end


subsubsection \<open>Introduction and Destruct Rules for \<open>H\<close>\<close>

context sylow_central
begin

lemma H_I: "\<lbrakk>g \<in> carrier G; M1 #> g = M1\<rbrakk> \<Longrightarrow> g \<in> H"
  by (simp add: H_def)

lemma H_into_carrier_G: "x \<in> H \<Longrightarrow> x \<in> carrier G"
  by (simp add: H_def)

lemma in_H_imp_eq: "g \<in> H \<Longrightarrow> M1 #> g = M1"
  by (simp add: H_def)

lemma H_m_closed: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
  by (simp add: H_def coset_mult_assoc [symmetric])

lemma H_not_empty: "H \<noteq> {}"
  apply (simp add: H_def)
  apply (rule exI [of _ \<one>])
  apply simp
  done

lemma H_is_subgroup: "subgroup H G"
  apply (rule subgroupI)
     apply (rule subsetI)
     apply (erule H_into_carrier_G)
    apply (rule H_not_empty)
   apply (simp add: H_def)
   apply clarify
   apply (erule_tac P = "\<lambda>z. lhs z = M1" for lhs in subst)
   apply (simp add: coset_mult_assoc )
  apply (blast intro: H_m_closed)
  done


lemma rcosetGM1g_subset_G: "\<lbrakk>g \<in> carrier G; x \<in> M1 #> g\<rbrakk> \<Longrightarrow> x \<in> carrier G"
  by (blast intro: M1_subset_G [THEN r_coset_subset_G, THEN subsetD])

lemma finite_M1: "finite M1"
  by (rule finite_subset [OF M1_subset_G finite_G])

lemma finite_rcosetGM1g: "g \<in> carrier G \<Longrightarrow> finite (M1 #> g)"
  using rcosetGM1g_subset_G finite_G M1_subset_G cosets_finite rcosetsI by blast

lemma M1_cardeq_rcosetGM1g: "g \<in> carrier G \<Longrightarrow> card (M1 #> g) = card M1"
  by (simp add: card_cosets_equal rcosetsI)

lemma M1_RelM_rcosetGM1g: "g \<in> carrier G \<Longrightarrow> (M1, M1 #> g) \<in> RelM"
  apply (simp add: RelM_def calM_def card_M1)
  apply (rule conjI)
   apply (blast intro: rcosetGM1g_subset_G)
  apply (simp add: card_M1 M1_cardeq_rcosetGM1g)
  apply (metis M1_subset_G coset_mult_assoc coset_mult_one r_inv_ex)
  done

end


subsection \<open>Equal Cardinalities of \<open>M\<close> and the Set of Cosets\<close>

text \<open>Injections between @{term M} and @{term "rcosets\<^bsub>G\<^esub> H"} show that
 their cardinalities are equal.\<close>

lemma ElemClassEquiv: "\<lbrakk>equiv A r; C \<in> A // r\<rbrakk> \<Longrightarrow> \<forall>x \<in> C. \<forall>y \<in> C. (x, y) \<in> r"
  unfolding equiv_def quotient_def sym_def trans_def by blast

context sylow_central
begin

lemma M_elem_map: "M2 \<in> M \<Longrightarrow> \<exists>g. g \<in> carrier G \<and> M1 #> g = M2"
  using M1_in_M M_in_quot [THEN RelM_equiv [THEN ElemClassEquiv]]
  by (simp add: RelM_def) (blast dest!: bspec)

lemmas M_elem_map_carrier = M_elem_map [THEN someI_ex, THEN conjunct1]

lemmas M_elem_map_eq = M_elem_map [THEN someI_ex, THEN conjunct2]

lemma M_funcset_rcosets_H:
  "(\<lambda>x\<in>M. H #> (SOME g. g \<in> carrier G \<and> M1 #> g = x)) \<in> M \<rightarrow> rcosets H"
  by (metis (lifting) H_is_subgroup M_elem_map_carrier rcosetsI restrictI subgroup_imp_subset)

lemma inj_M_GmodH: "\<exists>f \<in> M \<rightarrow> rcosets H. inj_on f M"
  apply (rule bexI)
   apply (rule_tac [2] M_funcset_rcosets_H)
  apply (rule inj_onI, simp)
  apply (rule trans [OF _ M_elem_map_eq])
   prefer 2 apply assumption
  apply (rule M_elem_map_eq [symmetric, THEN trans], assumption)
  apply (rule coset_mult_inv1)
     apply (erule_tac [2] M_elem_map_carrier)+
   apply (rule_tac [2] M1_subset_G)
  apply (rule coset_join1 [THEN in_H_imp_eq])
    apply (rule_tac [3] H_is_subgroup)
   prefer 2 apply (blast intro: M_elem_map_carrier)
  apply (simp add: coset_mult_inv2 H_def M_elem_map_carrier subset_eq)
  done

end


subsubsection \<open>The Opposite Injection\<close>

context sylow_central
begin

lemma H_elem_map: "H1 \<in> rcosets H \<Longrightarrow> \<exists>g. g \<in> carrier G \<and> H #> g = H1"
  by (auto simp: RCOSETS_def)

lemmas H_elem_map_carrier = H_elem_map [THEN someI_ex, THEN conjunct1]

lemmas H_elem_map_eq = H_elem_map [THEN someI_ex, THEN conjunct2]

lemma rcosets_H_funcset_M:
  "(\<lambda>C \<in> rcosets H. M1 #> (SOME g. g \<in> carrier G \<and> H #> g = C)) \<in> rcosets H \<rightarrow> M"
  apply (simp add: RCOSETS_def)
  apply (fast intro: someI2
      intro!: M1_in_M in_quotient_imp_closed [OF RelM_equiv M_in_quot _  M1_RelM_rcosetGM1g])
  done

text \<open>Close to a duplicate of \<open>inj_M_GmodH\<close>.\<close>
lemma inj_GmodH_M: "\<exists>g \<in> rcosets H\<rightarrow>M. inj_on g (rcosets H)"
  apply (rule bexI)
   apply (rule_tac [2] rcosets_H_funcset_M)
  apply (rule inj_onI)
  apply (simp)
  apply (rule trans [OF _ H_elem_map_eq])
   prefer 2 apply assumption
  apply (rule H_elem_map_eq [symmetric, THEN trans], assumption)
  apply (rule coset_mult_inv1)
     apply (erule_tac [2] H_elem_map_carrier)+
   apply (rule_tac [2] H_is_subgroup [THEN subgroup.subset])
  apply (rule coset_join2)
    apply (blast intro: H_elem_map_carrier)
   apply (rule H_is_subgroup)
  apply (simp add: H_I coset_mult_inv2 H_elem_map_carrier)
  done

lemma calM_subset_PowG: "calM \<subseteq> Pow (carrier G)"
  by (auto simp: calM_def)


lemma finite_M: "finite M"
  by (metis M_subset_calM finite_calM rev_finite_subset)

lemma cardMeqIndexH: "card M = card (rcosets H)"
  apply (insert inj_M_GmodH inj_GmodH_M)
  apply (blast intro: card_bij finite_M H_is_subgroup
      rcosets_subset_PowG [THEN finite_subset]
      finite_Pow_iff [THEN iffD2])
  done

lemma index_lem: "card M * card H = order G"
  by (simp add: cardMeqIndexH lagrange H_is_subgroup)

lemma lemma_leq1: "p^a \<le> card H"
  apply (rule dvd_imp_le)
   apply (rule div_combine [OF prime_imp_prime_elem[OF prime_p] not_dvd_M])
   prefer 2 apply (blast intro: subgroup.finite_imp_card_positive H_is_subgroup)
  apply (simp add: index_lem order_G power_add mult_dvd_mono multiplicity_dvd zero_less_m)
  done

lemma lemma_leq2: "card H \<le> p^a"
  apply (subst card_M1 [symmetric])
  apply (cut_tac M1_inj_H)
  apply (blast intro!: M1_subset_G intro: card_inj H_into_carrier_G finite_subset [OF _ finite_G])
  done

lemma card_H_eq: "card H = p^a"
  by (blast intro: le_antisym lemma_leq1 lemma_leq2)

end

lemma (in sylow) sylow_thm: "\<exists>H. subgroup H G \<and> card H = p^a"
  using lemma_A1
  apply clarify
  apply (frule existsM1inM, clarify)
  apply (subgoal_tac "sylow_central G p a m M1 M")
   apply (blast dest: sylow_central.H_is_subgroup sylow_central.card_H_eq)
  apply (simp add: sylow_central_def sylow_central_axioms_def sylow_axioms calM_def RelM_def)
  done

text \<open>Needed because the locale's automatic definition refers to
  @{term "semigroup G"} and @{term "group_axioms G"} rather than
  simply to @{term "group G"}.\<close>
lemma sylow_eq: "sylow G p a m \<longleftrightarrow> group G \<and> sylow_axioms G p a m"
  by (simp add: sylow_def group_def)


subsection \<open>Sylow's Theorem\<close>

theorem sylow_thm:
  "\<lbrakk>prime p; group G; order G = (p^a) * m; finite (carrier G)\<rbrakk>
    \<Longrightarrow> \<exists>H. subgroup H G \<and> card H = p^a"
  by (rule sylow.sylow_thm [of G p a m]) (simp add: sylow_eq sylow_axioms_def)

end
