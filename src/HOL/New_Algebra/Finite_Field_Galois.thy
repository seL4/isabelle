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
  proof (rule bij_betw_cong[THEN iffD2, OF _ frob_bij])
    show "\<And>x. x \<in> K \<Longrightarrow> ?sigma x = frobenius_power (card F) x"
      by (simp add: finite_field_frobenius_def restrict_apply')
  qed
  show ?thesis
    unfolding field_auto_mem_iff
  proof (intro conjI ballI)
    show "?sigma \<in> K \<rightarrow>\<^sub>E K"
      using T.ext.frobenius_power_closed
      by (auto simp: finite_field_frobenius_def PiE_iff extensional_def restrict_apply')
    show "bij_betw ?sigma K K" by (rule sigma_bij)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        ?sigma (x + y) = ?sigma x + ?sigma y"
      using frobenius_power_add_char_power[OF char e(2)]
      by (simp add: finite_field_frobenius_def restrict_apply' T.ext.add_closed)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        ?sigma (x * y) = ?sigma x * ?sigma y"
      by (simp add: finite_field_frobenius_def restrict_apply'
          T.ext.mult_closed frobenius_power_mult)
    show "?sigma 1 = 1"
      by (simp add: finite_field_frobenius_def restrict_apply')
    show "\<And>x. x \<in> F \<Longrightarrow> ?sigma x = x"
    proof -
      fix x assume xF: "x \<in> F"
      have xK: "x \<in> K" using T.base_subset xF by blast
      have fixed: "frobenius_power (card F) x = x"
        by (rule T.base.finite_field_frobenius_identity[OF finF xF])
      show "?sigma x = x"
        using xK fixed by (simp add: finite_field_frobenius_def restrict_apply')
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
    case 0
    have power0: "G.power ?sigma 0 = identity K"
      by (rule G.power_0)
    have app: "G.power ?sigma 0 x = identity K x"
      by (rule arg_cong[OF power0])
    have idapp: "identity K x = x" by (rule identity_apply[OF xK])
    have rhs: "x = x ^ (card F ^ 0)" by simp
    show ?case by (rule trans[OF app trans[OF idapp rhs]])
  next
    case (Suc i)
    have power_mem: "G.power ?sigma i \<in> field_auto K F"
      using sigma by simp
    have power_maps: "G.power ?sigma i x \<in> K"
      using power_mem xK by (auto simp: field_auto_mem_iff PiE_iff)
    have ih: "G.power ?sigma i x = x ^ (card F ^ i)"
      by (rule Suc.IH)
    have "G.power ?sigma (Suc i) x =
        ?sigma (G.power ?sigma i x)"
      using xK by (simp add: G.power_Suc compose_eq)
    also have "... = (G.power ?sigma i x) ^ card F"
      by (rule finite_field_frobenius_apply[OF power_maps])
    also have "... = (x ^ (card F ^ i)) ^ card F"
      by (rule arg_cong[OF ih])
    also have "... = x ^ ((card F ^ i) * card F)"
      by (rule power_mult[symmetric])
    also have "... = x ^ (card F ^ Suc i)"
      by (simp add: power_Suc mult.commute)
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
  have sigma: "?sigma \<in> field_auto K F"
    by (rule finite_field_frobenius_in_field_auto[OF T finF])
  have power_mem: "G.power ?sigma n \<in> field_auto K F"
    using sigma by simp
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
      by (rule T.ext.finite_field_frobenius_identity[
        OF T.finite_carrier_of_finite_base[OF finF] xK])
    have top_fixed: "x ^ card K = x"
      using top_fixed_frob by (simp add: frobenius_power_def)
    have card_power: "x ^ (card F ^ n) = x ^ card K"
      by (simp add: n(2))
    have id_x: "identity K x = x" by (rule identity_apply[OF xK])
    show "G.power ?sigma n x = identity K x"
      by (rule trans[OF iter trans[OF card_power trans[OF top_fixed id_x[symmetric]]]])
  qed
qed

text \<open>The Frobenius automorphism has exact order the degree of a finite extension.
  The upper bound is the finite-field identity on the top carrier; a smaller order would
  make every top-field element a root of a polynomial whose degree is too small.\<close>
theorem finite_field_frobenius_order:
  fixes F K :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "Monoid.element_order (compose K) (identity K)
      (finite_field_frobenius K (card F)) =
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
  define n where "n = finite_subfield_tower.extension_degree F K"
  have n_pos: "n > 0"
    unfolding n_def by (rule T.extension_degree_pos)
  have card_eq: "card K = card F ^ n"
    unfolding n_def by (rule finite_field_extension_cardinality[OF T finF])
  have power_n: "G.power ?sigma n = identity K"
    by (rule finite_field_frobenius_power_degree[OF T finF n_pos card_eq])
  have ord_le:
      "G.element_order ?sigma \<le> n"
    by (rule G.element_order_minimal[OF finG sigma n_pos power_n])
  have q_gt1: "1 < card F"
  proof -
    have pair: "{0, 1} \<subseteq> F" using T.base.zero_closed T.base.one_closed by auto
    have "card {0, 1 :: 'a} \<le> card F"
      by (rule card_mono[OF finF pair])
    then show ?thesis by simp
  qed
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
      have iter:
          "G.power ?sigma (G.element_order ?sigma) x =
            x ^ (card F ^ G.element_order ?sigma)"
        by (rule finite_field_frobenius_power_apply[OF T finF xK])
      have ord_id:
          "G.power ?sigma (G.element_order ?sigma) = identity K"
        by (rule G.power_element_order[OF finG sigma])
      have id_x: "identity K x = x" by (rule identity_apply[OF xK])
      have rev:
          "x ^ (card F ^ G.element_order ?sigma) =
            G.power ?sigma (G.element_order ?sigma) x"
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
    have card_top_le:
        "card K \<le> card {x :: 'a. x ^ (card F ^ G.element_order ?sigma) = x}"
      by (rule card_mono[OF fixed_fin top_subset])
    have qpow_less_top: "card F ^ G.element_order ?sigma < card K"
      using power_strict_increasing[OF ord_less q_gt1] card_eq by simp
    have "card K \<le> card F ^ G.element_order ?sigma"
      by (rule order_trans[OF card_top_le fixed_card])
    with qpow_less_top show False by simp
  qed
  have ord_eq: "G.element_order ?sigma = n"
    using ord_le ord_not_less by auto
  show ?thesis using ord_eq by (simp add: n_def)
qed

text \<open>Every finite-field Galois group is generated by the relative Frobenius.  The equality
  is proved at the carrier-set level, so downstream users can use the native automorphism group
  directly without introducing a second cyclic-group representation.\<close>
theorem finite_field_galois_group_cyclic:
  fixes F K :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower F K" and finF: "finite F"
  shows "Group.cyclic_subgroup (compose K) (identity K)
      (finite_field_frobenius K (card F)) = field_auto K F"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  interpret G: Group "field_auto K F" "compose K" "identity K"
    by (rule field_auto_group[OF T.ext.Subfield_axioms T.base_subset])
  let ?sigma = "finite_field_frobenius K (card F)"
  have sigma: "?sigma \<in> field_auto K F"
    by (rule finite_field_frobenius_in_field_auto[OF T finF])
  have normal: "normal_extension K F"
    by (rule finite_field_extension_normal[OF T finF])
  have sep: "separable_extension K F"
    by (rule finite_field_extension_separable[OF T finF])
  have finG: "finite (field_auto K F)"
    by (rule finite_normal_separable_field_auto[OF T normal sep])
  have ord:
      "G.element_order ?sigma = finite_subfield_tower.extension_degree F K"
    by (rule finite_field_frobenius_order[OF T finF])
  have group_card:
      "card (field_auto K F) = finite_subfield_tower.extension_degree F K"
    by (rule finite_normal_separable_galois_degree[OF T normal sep])
  have cyc_subset: "G.cyclic_subgroup ?sigma \<subseteq> field_auto K F"
    by (rule G.cyclic_subgroup_subset[OF sigma])
  have cyc_card:
      "card (G.cyclic_subgroup ?sigma) = finite_subfield_tower.extension_degree F K"
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
  have data: "Subfield E \<and> F \<subseteq> E \<and> E \<subseteq> K"
    using E by (simp add: inter_fields_iff)
  have sfE: "Subfield E" by (rule conjunct1[OF data])
  have FE: "F \<subseteq> E" by (rule conjunct1[OF conjunct2[OF data]])
  have EK: "E \<subseteq> K" by (rule conjunct2[OF conjunct2[OF data]])
  have TFE_raw: "finite_subfield_tower F E"
    by (rule finite_subfield_tower_intermediate_left[OF T sfE FE EK])
  interpret TFE: finite_subfield_tower F E by (rule TFE_raw)
  have finE: "finite E" by (rule TFE.finite_carrier_of_finite_base[OF finF])
  have cardE: "card E = card F ^ TFE.extension_degree"
    by (rule finite_field_extension_cardinality[OF TFE_raw finF])
  have q_gt1: "1 < card F"
  proof -
    have pair: "{0, 1} \<subseteq> F" using T.base.zero_closed T.base.one_closed by auto
    have "card {0, 1 :: 'a} \<le> card F"
      by (rule card_mono[OF finF pair])
    then show ?thesis by simp
  qed
  have m_gt1: "1 < card F ^ TFE.extension_degree"
    by (rule one_less_power[OF q_gt1 TFE.extension_degree_pos])
  have roots:
      "finite {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x} \<and>
        card {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x} \<le>
          card F ^ TFE.extension_degree"
    by (rule card_power_fixed_points_le[OF m_gt1])
  have roots_fin:
      "finite {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x}"
    by (rule conjunct1[OF roots])
  have roots_card:
      "card {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x} \<le>
        card F ^ TFE.extension_degree"
    by (rule conjunct2[OF roots])
  let ?R = "finite_field_power_roots K F TFE.extension_degree"
  have R_subset:
      "?R \<subseteq> {x :: 'a. x ^ (card F ^ TFE.extension_degree) = x}"
    by (auto simp: finite_field_power_roots_def)
  have R_fin: "finite ?R"
    by (rule finite_subset[OF R_subset roots_fin])
  have R_card_le: "card ?R \<le> card F ^ TFE.extension_degree"
    by (rule order_trans[OF card_mono[OF roots_fin R_subset] roots_card])
  have E_subset_R: "E \<subseteq> ?R"
  proof
    fix x assume xE: "x \<in> E"
    have xK: "x \<in> K" using EK xE by blast
    have xpow_frob: "frobenius_power (card E) x = x"
      by (rule TFE.ext.finite_field_frobenius_identity[OF finE xE])
    have xpow: "x ^ card E = x"
      using xpow_frob by (simp add: frobenius_power_def)
    show "x \<in> ?R"
      using xK xpow cardE by (simp add: finite_field_power_roots_def)
  qed
  have card_E_le_R: "card E \<le> card ?R"
    by (rule card_mono[OF R_fin E_subset_R])
  have card_eq: "card E = card ?R"
    using cardE R_card_le card_E_le_R by simp
  show ?thesis
    by (rule card_subset_eq[OF R_fin E_subset_R card_eq])
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
proof -
  have rootsE:
      "E = finite_field_power_roots K F
        (finite_subfield_tower.extension_degree F E)"
    by (rule finite_field_intermediate_power_roots[OF T finF E])
  have rootsE':
      "E' = finite_field_power_roots K F
        (finite_subfield_tower.extension_degree F E')"
    by (rule finite_field_intermediate_power_roots[OF T finF E'])
  show ?thesis using rootsE rootsE' degree_eq by simp
qed

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
  have data: "Subfield E \<and> F \<subseteq> E \<and> E \<subseteq> K"
    using E by (simp add: inter_fields_iff)
  have sfE: "Subfield E" by (rule conjunct1[OF data])
  have FE: "F \<subseteq> E" by (rule conjunct1[OF conjunct2[OF data]])
  have EK: "E \<subseteq> K" by (rule conjunct2[OF conjunct2[OF data]])
  have TFE_raw: "finite_subfield_tower F E"
    by (rule finite_subfield_tower_intermediate_left[OF T sfE FE EK])
  have TEK_raw: "finite_subfield_tower E K"
    by (rule finite_subfield_tower_intermediate_right[OF T sfE FE EK])
  interpret C: finite_subfield_tower_chain F E K
    by (rule finite_subfield_tower_chain.intro[OF TFE_raw TEK_raw])
  have tower_degree:
      "finite_subfield_tower.extension_degree F K =
        finite_subfield_tower.extension_degree F E *
        finite_subfield_tower.extension_degree E K"
    by (rule C.extension_degree_tower_law_exists)
  show ?thesis
    unfolding dvd_def
    by (rule exI[of _ "finite_subfield_tower.extension_degree E K"])
       (simp add: tower_degree mult.commute)
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
  define n where "n = finite_subfield_tower.extension_degree F K"
  have n_pos: "n > 0"
    unfolding n_def by (rule T.extension_degree_pos)
  have ord_sigma: "G.element_order ?sigma = n"
    unfolding n_def by (rule finite_field_frobenius_order[OF T finF])
  have d_n: "d dvd n"
    using d by (simp add: n_def)
  let ?hgen = "G.power ?sigma d"
  have hgen: "?hgen \<in> field_auto K F"
    by (rule G.power_closed[OF sigma])
  let ?H = "G.cyclic_subgroup ?hgen"
  have Hsub:
      "Subgroup ?H (field_auto K F) (compose K) (identity K)"
    by (rule G.cyclic_subgroup_is_subgroup[OF finG hgen])
  have H: "?H \<in> galois_subgroups K F"
    using Hsub by (simp add: galois_subgroups_iff)
  have gcd_eq: "gcd n d = d"
    by (rule gcd_proj2_if_dvd_nat[OF d_n])
  have H_card: "card ?H = n div d"
    using G.card_cyclic_subgroup[OF finG hgen]
      G.element_order_power[OF finG sigma] ord_sigma gcd_eq by simp
  let ?E = "fixed_field K ?H"
  have E: "?E \<in> inter_fields K F"
    by (rule GE.fixed_field_in_inter_fields[OF H])
  have E_data: "Subfield ?E \<and> F \<subseteq> ?E \<and> ?E \<subseteq> K"
    using E by (simp add: inter_fields_iff)
  have sfE: "Subfield ?E" by (rule conjunct1[OF E_data])
  have FE: "F \<subseteq> ?E" by (rule conjunct1[OF conjunct2[OF E_data]])
  have EK: "?E \<subseteq> K" by (rule conjunct2[OF conjunct2[OF E_data]])
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
    using H_card fixed_group
      finite_normal_separable_galois_degree[OF TEK_raw normalEK sepEK] by simp
  interpret C: finite_subfield_tower_chain F ?E K
    by (rule finite_subfield_tower_chain.intro[OF TFE_raw TEK_raw])
  have tower_degree:
      "n = TFE.extension_degree * TEK.extension_degree"
    unfolding n_def by (rule C.extension_degree_tower_law_exists)
  have n_mult: "n div d * d = n"
    by (rule dvd_div_mult_self[OF d_n])
  have cancel_eq:
      "TEK.extension_degree * TFE.extension_degree =
       TEK.extension_degree * d"
  proof -
    have left:
        "TEK.extension_degree * TFE.extension_degree = n"
      using tower_degree by (simp add: mult.commute)
    have right:
        "TEK.extension_degree * d = n"
      using n_mult H_degree by (simp add: mult.commute)
    show ?thesis by (rule trans[OF left right[symmetric]])
  qed
  have lower_degree: "TFE.extension_degree = d"
    using cancel_eq TEK.extension_degree_pos nat_mult_eq_cancel1 by simp
  have roots:
      "?E = finite_field_power_roots K F TFE.extension_degree"
    by (rule finite_field_intermediate_power_roots[OF T finF E])
  have roots_d: "?E = finite_field_power_roots K F d"
    using roots lower_degree by simp
  show ?thesis
    by (rule exI[of _ ?E], intro conjI)
       (rule E, rule lower_degree, rule roots_d)
qed

end
