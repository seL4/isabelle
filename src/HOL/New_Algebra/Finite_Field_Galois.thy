section \<open>Galois groups of finite fields\<close>

theory Finite_Field_Galois
  imports Finite_Field_Extensions Galois_Finite_Correspondence
begin

text \<open>The restricted power map is a genuine element of the carrier-set automorphism
  group: outside the top carrier it has the canonical undefined value required by \<open>PiE\<close>.\<close>
definition finite_field_frobenius ::
    "'a :: field set \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)"
  where "finite_field_frobenius K q = restrict (frobenius_power q) K"

lemma finite_field_frobenius_apply [simp]:
  "x \<in> K \<Longrightarrow> finite_field_frobenius K q x = x ^ q"
  by (simp add: finite_field_frobenius_def frobenius_power_def restrict_apply')

theorem finite_field_frobenius_in_field_auto:
  fixes F K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "finite_field_frobenius K (card F) \<in> field_auto K F"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  have finK: "finite K" by (rule T.finite_carrier_of_finite_base[OF finF])
  obtain e where e: "e > 0" "card F = CHAR('a) ^ e"
    using T.base.finite_subfield_cardinality_char_power[OF finF] by blast
  have char: "prime CHAR('a)"
    by (rule T.base.finite_subfield_CHAR_prime[OF finF])
  let ?sigma = "finite_field_frobenius K (card F)"
  have frob_bij: "bij_betw (frobenius_power (card F)) K K"
    by (rule T.ext.finite_frobenius_bij_betw[OF finK char e(2)])
  have sigma_bij: "bij_betw ?sigma K K"
    by (simp add: finite_field_frobenius_def frob_bij)
  show ?thesis
    unfolding field_auto_mem_iff
  proof (intro conjI ballI)
    show "?sigma \<in> K \<rightarrow>\<^sub>E K"
      using T.ext.frobenius_power_closed
      by (auto simp: finite_field_frobenius_def PiE_iff extensional_def restrict_apply')
    show "bij_betw ?sigma K K" by (rule sigma_bij)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> ?sigma (x + y) = ?sigma x + ?sigma y"
      using frobenius_power_add_char_power[OF char e(2)]
      by (simp add: finite_field_frobenius_def restrict_apply' T.ext.add_closed)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> ?sigma (x * y) = ?sigma x * ?sigma y"
      by (simp add: finite_field_frobenius_def restrict_apply' T.ext.mult_closed frobenius_power_mult)
    show "?sigma 1 = 1"
      by (simp add: finite_field_frobenius_def restrict_apply')
    show "?sigma x = x" if xF: "x \<in> F" for x
    proof -
      have fixed: "frobenius_power (card F) x = x"
        by (rule T.base.finite_field_frobenius_identity[OF finF xF])
      show "?sigma x = x"
        using T.vs.scale_closed xF fixed by (fastforce simp add: finite_field_frobenius_def restrict_apply')
    qed
  qed
qed

theorem finite_field_frobenius_power_apply:
  fixes F K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F" and xK: "x \<in> K"
  shows "Monoid.power (compose K) (identity K)
      (finite_field_frobenius K (card F)) i x = x ^ (card F ^ i)"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  interpret G: Group "field_auto K F" "compose K" "identity K"
    by (rule field_auto_group[OF T.ext.Subfield_axioms T.base_subset])
  let ?sigma = "finite_field_frobenius K (card F)"
  have sigma: "?sigma \<in> field_auto K F"
    by (rule finite_field_frobenius_in_field_auto[OF assms(1) finF])
  show ?thesis
  proof (induction i)
    case 0 then show ?case
      by (metis power_0 power_one_right restrict_apply' G.power_0 xK)
  next
    case (Suc i)
    have power_maps: "G.power ?sigma i x \<in> K"
      using sigma xK by (simp add: Suc T.ext.power_closed)
    have "G.power ?sigma (Suc i) x = (G.power ?sigma i x) ^ card F"
      by (simp add: compose_eq power_maps xK)
    also have "... = x ^ (card F ^ Suc i)"
      by (metis Suc power_Suc2 power_mult)
    finally show ?case .
  qed
qed

theorem finite_field_frobenius_power_degree:
  fixes F K :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
    and n: "n > 0" "card K = card F ^ n"
  shows "Monoid.power (compose K) (identity K)
      (finite_field_frobenius K (card F)) n = identity K"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  interpret G: Group "field_auto K F" "compose K" "identity K"
    by (rule field_auto_group[OF T.ext.Subfield_axioms T.base_subset])
  let ?sigma = "finite_field_frobenius K (card F)"
  have power_mem: "G.power ?sigma n \<in> field_auto K F"
    using finite_field_frobenius_in_field_auto[OF T finF] by simp
  have power_maps: "G.power ?sigma n \<in> K \<rightarrow>\<^sub>E K"
    using power_mem by (simp add: field_auto_mem_iff)
  have id_maps: "identity K \<in> K \<rightarrow>\<^sub>E K"
    by (auto simp: identity_apply PiE_iff)
  show ?thesis
  proof (rule PiE_ext[OF power_maps id_maps])
    fix x assume xK: "x \<in> K"
    have iter: "G.power ?sigma n x = x ^ (card F ^ n)"
      by (rule finite_field_frobenius_power_apply[OF T finF xK])
    have top_fixed_frob: "frobenius_power (card K) x = x"
      using Subfield.finite_field_frobenius_identity T.ext.Subfield_axioms T.finite_carrier_of_finite_base
        finF xK by blast
    have top_fixed: "x ^ card K = x"
      using top_fixed_frob by (simp add: frobenius_power_def)
    have id_x: "identity K x = x" by (rule identity_apply[OF xK])
    show "G.power ?sigma n x = identity K x"
      using id_x iter n(2) top_fixed by argo
  qed
qed

text \<open>The Frobenius automorphism has exact order the degree of a finite extension.
  The upper bound is the finite-field identity on the top carrier; a smaller order would
  make every top-field element a root of a polynomial whose degree is too small.\<close>
theorem finite_field_frobenius_order:
  fixes F K :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "Monoid.element_order (compose K) (identity K) (finite_field_frobenius K (card F)) =
         finite_subfield_tower.extension_degree F K"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  interpret G: Group "field_auto K F" "compose K" "identity K"
    by (rule field_auto_group[OF T.ext.Subfield_axioms T.base_subset])
  let ?sigma = "finite_field_frobenius K (card F)"
  have sigma: "?sigma \<in> field_auto K F"
    by (rule finite_field_frobenius_in_field_auto[OF T finF])
  have finK: "finite K" by (rule T.finite_carrier_of_finite_base[OF finF])
  have normal: "normal_extension K F"
    by (rule finite_field_extension_normal[OF T finF])
  have sep: "separable_extension K F"
    by (rule finite_field_extension_separable[OF T finF])
  have finG: "finite (field_auto K F)"
    by (rule finite_normal_separable_field_auto[OF T normal sep])
  define n where "n \<equiv> finite_subfield_tower.extension_degree F K"
  have n_pos: "n > 0"
    unfolding n_def by (rule T.extension_degree_pos)
  have card_eq: "card K = card F ^ n"
    unfolding n_def by (rule finite_field_extension_cardinality[OF T finF])
  have power_n: "G.power ?sigma n = identity K"
    by (rule finite_field_frobenius_power_degree[OF T finF n_pos card_eq])
  have ord_le: "G.element_order ?sigma \<le> n"
    by (rule G.element_order_minimal[OF finG sigma n_pos power_n])
  have q_gt1: "1 < card F"
    using T.base.cardK_gt1 finF by blast
  have ord_not_less: "\<not> G.element_order ?sigma < n"
  proof
    assume ord_less: "G.element_order ?sigma < n"
    have ord_pos: "G.element_order ?sigma > 0"
      by (rule G.element_order_pos[OF finG sigma])
    have qpow_gt1: "1 < card F ^ G.element_order ?sigma"
      by (rule one_less_power[OF q_gt1 ord_pos])
    have fixed_data:
        "finite {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x} \<and>
          card {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x} \<le>
            card F ^ G.element_order ?sigma"
      by (rule card_power_fixed_points_le[OF qpow_gt1])
    have fixed_fin:
        "finite {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x}"
      by (rule conjunct1[OF fixed_data])
    have fixed_card:
        "card {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x} \<le>
          card F ^ G.element_order ?sigma"
      by (rule conjunct2[OF fixed_data])
    have top_subset:
        "K \<subseteq> {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x}"
    proof
      fix x assume xK: "x \<in> K"
      have iter: "G.power ?sigma (G.element_order ?sigma) x = x ^ (card F ^ G.element_order ?sigma)"
        by (rule finite_field_frobenius_power_apply[OF T finF xK])
      have ord_id:
          "G.power ?sigma (G.element_order ?sigma) = identity K"
        by (rule G.power_element_order[OF finG sigma])
      have id_x: "identity K x = x" by (rule identity_apply[OF xK])
      have rev:
          "x ^ (card F ^ G.element_order ?sigma) = G.power ?sigma (G.element_order ?sigma) x"
        by (rule sym[OF iter])
      have result:
          "x ^ (card F ^ G.element_order ?sigma) = identity K x"
        using rev ord_id by (simp only: rev ord_id)
      have result_set:
          "x \<in> {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x}"
        using result id_x by simp
      show "x \<in> {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x}"
        by (rule result_set)
    qed
    have card_top_le: "card K \<le> card {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x}"
      by (rule card_mono[OF fixed_fin top_subset])
    have "card K \<le> card F ^ G.element_order ?sigma"
      by (rule order_trans[OF card_top_le fixed_card])
    with power_strict_increasing[OF ord_less q_gt1] card_eq show False by simp
  qed
  show ?thesis  
    using ord_le ord_not_less n_def by linarith
qed

text \<open>Every finite-field Galois group is generated by the relative Frobenius.  The equality
  is proved at the carrier-set level, so downstream users can use the native automorphism group
  directly without introducing a second cyclic-group representation.\<close>
theorem finite_field_galois_group_cyclic:
  fixes F K :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "Group.cyclic_subgroup (compose K) (identity K) (finite_field_frobenius K (card F)) = field_auto K F"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  interpret G: Group "field_auto K F" "compose K" "identity K"
    by (rule field_auto_group[OF T.ext.Subfield_axioms T.base_subset])
  let ?sigma = "finite_field_frobenius K (card F)"
  obtain sigma: "?sigma \<in> field_auto K F" and normal: "normal_extension K F" and sep: "separable_extension K F"
    using T finF 
    by (auto simp: finite_field_frobenius_in_field_auto finite_field_extension_normal finite_field_extension_separable)
  have finG: "finite (field_auto K F)"
    by (rule finite_normal_separable_field_auto[OF T normal sep])
  have ord: "G.element_order ?sigma = finite_subfield_tower.extension_degree F K"
    by (rule finite_field_frobenius_order[OF T finF])
  have group_card:
      "card (field_auto K F) = finite_subfield_tower.extension_degree F K"
    by (rule finite_normal_separable_galois_degree[OF T normal sep])
  have cyc_subset: "G.cyclic_subgroup ?sigma \<subseteq> field_auto K F"
    by (rule G.cyclic_subgroup_subset[OF sigma])
  have cyc_card: "card (G.cyclic_subgroup ?sigma) = finite_subfield_tower.extension_degree F K"
    using G.card_cyclic_subgroup[OF finG sigma] ord by simp
  have card_eq: "card (G.cyclic_subgroup ?sigma) = card (field_auto K F)"
    using cyc_card group_card by simp
  show ?thesis
    by (rule card_subset_eq[OF finG cyc_subset card_eq])
qed

text \<open>The canonical degree-\<open>d\<close> root set inside a finite extension.  It is written as a
  set of ambient-field elements lying in the top carrier, which keeps the statement useful for
  the native set-based subfield representation.\<close>
definition finite_field_power_roots ::
    "'a :: field set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set"
  where "finite_field_power_roots K F d = {x \<in> K. x ^ (card F ^ d) = x}"

lemma finite_field_power_roots_iff [simp]:
  "x \<in> finite_field_power_roots K F d \<longleftrightarrow>
    x \<in> K \<and> x ^ (card F ^ d) = x"
  by (simp add: finite_field_power_roots_def)

text \<open>Every intermediate field is exactly the root set of the appropriate Frobenius power.
  The root bound supplies the reverse inclusion: the intermediate field already has the full
  degree-many roots, so no additional ambient roots can occur.\<close>
theorem finite_field_intermediate_power_roots:
  fixes F K E :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
    and E: "E \<in> inter_fields K F"
  shows "E = finite_field_power_roots K F
      (finite_subfield_tower.extension_degree F E)"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  have sfE: "Subfield E" and FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
    using E by (auto simp: inter_fields_iff)
  have TFE_raw: "finite_subfield_tower F E"
    by (rule finite_subfield_tower_intermediate_left[OF T sfE FE EK])
  interpret TFE: finite_subfield_tower F E by (rule TFE_raw)
  have finE: "finite E" by (rule TFE.finite_carrier_of_finite_base[OF finF])
  have cardE: "card E = card F ^ TFE.extension_degree"
    by (rule finite_field_extension_cardinality[OF TFE_raw finF])
  have q_gt1: "1 < card F"
    using T.base.cardK_gt1 finF by blast
  have m_gt1: "1 < card F ^ TFE.extension_degree"
    by (rule one_less_power[OF q_gt1 TFE.extension_degree_pos])
  have roots:
      "finite {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x} \<and>
        card {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x} \<le> card F ^ TFE.extension_degree"
    by (rule card_power_fixed_points_le[OF m_gt1])
  have roots_fin: "finite {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x}"
    by (rule conjunct1[OF roots])
  have roots_card:
      "card {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x} \<le> card F ^ TFE.extension_degree"
    by (rule conjunct2[OF roots])
  let ?R = "finite_field_power_roots K F TFE.extension_degree"
  have R_subset:
      "?R \<subseteq> {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x}"
    by (auto simp: finite_field_power_roots_def)
  have R_card_le: "card ?R \<le> card F ^ TFE.extension_degree"
    by (rule order_trans[OF card_mono[OF roots_fin R_subset] roots_card])
  show ?thesis
  proof (intro card_subset_eq)
    show E_subset_R: "E \<subseteq> ?R"
    proof
      fix x assume xE: "x \<in> E"
      have xK: "x \<in> K" using EK xE by blast
      have "frobenius_power (card E) x = x"
        by (simp add: TFE.ext.finite_field_frobenius_identity finE xE)
      then show "x \<in> ?R"
        using xK cardE by (simp add: frobenius_power_def finite_field_power_roots_def)
    qed
    show "finite ?R"
      by (rule finite_subset[OF R_subset roots_fin])
    then show "card E = card ?R"
      by (metis E_subset_R R_card_le cardE card_seteq)
  qed
qed

text \<open>Consequently, the degree is a complete invariant for intermediate fields of a finite
  field extension.\<close>
theorem finite_field_intermediate_degree_injective:
  fixes F K :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
    and E: "E \<in> inter_fields K F" and E': "E' \<in> inter_fields K F"
    and degree_eq:
      "finite_subfield_tower.extension_degree F E =
        finite_subfield_tower.extension_degree F E'"
  shows "E = E'"
  using assms by (metis finite_field_intermediate_power_roots)

text \<open>The lower degree of every intermediate field divides the total extension degree, as
  expected from the finite-field divisor classification.\<close>
theorem finite_field_intermediate_degree_dvd:
  fixes F K E :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
    and E: "E \<in> inter_fields K F"
  shows "finite_subfield_tower.extension_degree F E dvd
      finite_subfield_tower.extension_degree F K"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  have sfE: "Subfield E" and FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
    using E by (auto simp: inter_fields_iff)
  have TFE_raw: "finite_subfield_tower F E"
    by (rule finite_subfield_tower_intermediate_left[OF T sfE FE EK])
  have TEK_raw: "finite_subfield_tower E K"
    by (rule finite_subfield_tower_intermediate_right[OF T sfE FE EK])
  interpret C: finite_subfield_tower_chain F E K
    by (rule finite_subfield_tower_chain.intro[OF TFE_raw TEK_raw])
  show ?thesis
    by (simp add: C.extension_degree_tower_law_exists)
qed

text \<open>Every divisor of the total degree is realised by a unique intermediate field.  The
  subgroup generated by the corresponding power of Frobenius has the complementary order;
finite Galois correspondence and the tower law then compute the degree of its fixed field.\<close>
theorem finite_field_intermediate_exists:
  fixes F K :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
    and d: "d dvd finite_subfield_tower.extension_degree F K"
  shows "\<exists>E. E \<in> inter_fields K F \<and>
      finite_subfield_tower.extension_degree F E = d \<and>
      E = finite_field_power_roots K F d"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  interpret G: Group "field_auto K F" "compose K" "identity K"
    by (rule field_auto_group[OF T.ext.Subfield_axioms T.base_subset])
  interpret GE: galois_extension K F
    by (rule galois_extension.intro[OF T.ext.Subfield_axioms T.base.Subfield_axioms
      T.base_subset])
  let ?sigma = "finite_field_frobenius K (card F)"
  have sigma: "?sigma \<in> field_auto K F"
    by (rule finite_field_frobenius_in_field_auto[OF T finF])
  have normal: "normal_extension K F"
    by (rule finite_field_extension_normal[OF T finF])
  have sep: "separable_extension K F"
    by (rule finite_field_extension_separable[OF T finF])
  have finG: "finite (field_auto K F)"
    by (rule finite_normal_separable_field_auto[OF T normal sep])
  define n where "n \<equiv> finite_subfield_tower.extension_degree F K"
  have n_pos: "n > 0"
    unfolding n_def by (rule T.extension_degree_pos)
  have ord_sigma: "G.element_order ?sigma = n"
    unfolding n_def by (rule finite_field_frobenius_order[OF T finF])
  let ?hgen = "G.power ?sigma d"
  have hgen: "?hgen \<in> field_auto K F"
    by (rule G.power_closed[OF sigma])
  let ?H = "G.cyclic_subgroup ?hgen"
  have Hsub: "Subgroup ?H (field_auto K F) (compose K) (identity K)"
    by (rule G.cyclic_subgroup_is_subgroup[OF finG hgen])
  have H: "?H \<in> galois_subgroups K F"
    using Hsub by (simp add: galois_subgroups_iff)
  have gcd_eq: "gcd n d = d"
    by (simp add: d n_def)
  have H_card: "card ?H = n div d"
    using G.card_cyclic_subgroup G.element_order_power finG gcd_eq hgen ord_sigma sigma by presburger
  let ?E = "fixed_field K ?H"
  have E: "?E \<in> inter_fields K F"
    by (rule GE.fixed_field_in_inter_fields[OF H])
  have sfE: "Subfield ?E" and FE: "F \<subseteq> ?E" and EK: "?E \<subseteq> K"
    using E by (auto simp add: inter_fields_iff)
  have TFE_raw: "finite_subfield_tower F ?E"
    by (rule finite_subfield_tower_intermediate_left[OF T sfE FE EK])
  have TEK_raw: "finite_subfield_tower ?E K"
    by (rule finite_subfield_tower_intermediate_right[OF T sfE FE EK])
  interpret TFE: finite_subfield_tower F ?E by (rule TFE_raw)
  interpret TEK: finite_subfield_tower ?E K by (rule TEK_raw)
  have normalEK: "normal_extension K ?E"
    by (rule finite_normal_extension_base_change[OF T normal sfE FE EK])
  have sepEK: "separable_extension K ?E"
    by (rule finite_separable_extension_base_change[OF T sep sfE FE EK])
  have fixed_group: "field_auto K ?E = ?H"
    by (rule finite_galois_fixed_group[OF T normal sep H])
  have H_degree: "n div d = TEK.extension_degree"
    using H_card fixed_group finite_normal_separable_galois_degree[OF TEK_raw normalEK sepEK] by simp
  interpret C: finite_subfield_tower_chain F ?E K
    by (rule finite_subfield_tower_chain.intro[OF TFE_raw TEK_raw])
  have tower_degree: "n = TFE.extension_degree * TEK.extension_degree"
    unfolding n_def by (rule C.extension_degree_tower_law_exists)
  have cancel_eq: "TEK.extension_degree * TFE.extension_degree = TEK.extension_degree * d"
    using H_degree dvd_div_mult_self[of d n] d tower_degree unfolding n_def by auto
  have lower_degree: "TFE.extension_degree = d"
    using cancel_eq TEK.extension_degree_pos nat_mult_eq_cancel1 by simp
  have roots: "?E = finite_field_power_roots K F TFE.extension_degree"
    by (rule finite_field_intermediate_power_roots[OF T finF E])
  have roots_d: "?E = finite_field_power_roots K F d"
    using roots lower_degree by simp
  then show ?thesis
    using E lower_degree by blast
qed

end
