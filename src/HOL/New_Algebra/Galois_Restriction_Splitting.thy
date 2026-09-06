section \<open>Restriction along a stable intermediate field of a splitting field\<close>

theory Galois_Restriction_Splitting
  imports Galois_Simple_Degree Galois_Restriction
begin

text \<open>
  The general restriction theory exposes the homomorphism and its kernel, but leaves the
  surjectivity argument in terms of a generated root field.  This theory supplies the missing
  representation bridge for the public @{const splitting_field} interface.  The stability
  hypothesis is essential: without it, restricting an @{term F}-automorphism of @{term K} need not
  map the intermediate field @{term E} to itself, so the restriction does not land in
  @{term "field_auto E F"}.
\<close>

text \<open>The roots of a splitting-field polynomial give exactly the generated-field presentation
  required by the finite homomorphism-extension theorem.\<close>
lemma splitting_field_generate_field_over:
  fixes K E :: "complex set" and p :: "complex poly"
  assumes split: "splitting_field E p K"
  shows "K = generate_field (E \<union> {r. poly p r = 0})"
proof -
  have "K = generate_field (E \<union> poly_root_set p)"
    using splitting_fieldD[OF split] by blast
  then show ?thesis
    by (simp add: gen_subfield_eq_generate_field poly_root_set_def)
qed

text \<open>For a splitting field over @{term E}, restriction onto @{term E} is surjective onto the
  @{term F}-automorphisms of @{term E}, provided the defining polynomial is already over @{term F}.
  This is the form used by the radical-solvability descent: the larger group fixes @{term F}, while
  the splitting-field generators are algebraic over @{term E}.\<close>
theorem galois_restriction_image_of_splitting_field:
  fixes K E F :: "complex set" and p :: "complex poly"
  assumes split: "splitting_field E p K"
    and sfE: "Subfield E" and sfF: "Subfield F" and FE: "F \<subseteq> E"
    and pF: "p \<in> poly_over F"
    and stable: "\<And>\<sigma>. \<sigma> \<in> field_auto K F \<Longrightarrow> \<sigma> ` E = E"
  shows "galois_restriction K E F ` field_auto K F = field_auto E F"
proof -
  have sfK: "Subfield K"
    using splitting_field_subfield[OF split]
    by (simp add: complex_subfield_iff_subfield)
  have EK: "E \<subseteq> K"
    by (rule splitting_field_base_subset[OF split])
  have pnz: "p \<noteq> 0"
    using split by (auto simp: splitting_fieldD)
  have Kdef: "K = generate_field (E \<union> {r. poly p r = 0})"
    by (rule splitting_field_generate_field_over[OF split])
  have finR: "finite {r. poly p r = 0}"
    using pnz by (rule poly_roots_finite)
  have algR: "\<And>r. poly p r = 0 \<Longrightarrow> algebraic_over E r"
  proof -
    fix r assume root: "poly p r = 0"
    have "r \<in> poly_root_set p"
      using root by (simp add: poly_root_set_def)
    then show "algebraic_over E r"
      by (rule splitting_field_root_algebraic[OF split])
  qed
  have closed: "\<And>q :: complex poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
    using fundamental_theorem_of_algebra by (simp add: constant_degree)
  have image_subset:
      "galois_restriction K E F ` field_auto K F \<subseteq> field_auto E F"
    using gal_res_mem[OF sfK sfE FE EK stable]
    by (auto simp: galois_restriction_apply)
  have target_subset:
      "field_auto E F \<subseteq> galois_restriction K E F ` field_auto K F"
  proof
    fix \<tau> assume tau: "\<tau> \<in> field_auto E F"
    obtain \<sigma> where sigma: "\<sigma> \<in> field_auto K F"
      and agree: "\<forall>x \<in> E. \<sigma> x = \<tau> x"
      using galois_restriction_surjective[OF sfE sfF FE pF Kdef finR algR closed tau] by blast
    have restrict_eq': "restrict \<sigma> E = restrict \<tau> E"
      by (rule restrict_ext) (use agree in simp)
    have tauPiE: "\<tau> \<in> E \<rightarrow>\<^sub>E E"
      using tau by (simp only: field_auto_mem_iff)
    have tau_restrict: "restrict \<tau> E = \<tau>"
      using PiE_restrict[OF tauPiE] .
    have restrict_eq: "restrict \<sigma> E = \<tau>"
      using restrict_eq' tau_restrict by (rule trans)
    have restriction: "galois_restriction K E F \<sigma> = \<tau>"
      using sigma by (simp add: galois_restriction_apply restrict_eq)
    show "\<tau> \<in> galois_restriction K E F ` field_auto K F"
      using sigma restriction by blast
  qed
  show ?thesis using image_subset target_subset by blast
qed

text \<open>Package the preceding image equality as an epimorphism.\<close>
theorem galois_restriction_epimorphism_of_splitting_field:
  fixes K E F :: "complex set" and p :: "complex poly"
  assumes split: "splitting_field E p K"
    and sfE: "Subfield E" and sfF: "Subfield F" and FE: "F \<subseteq> E"
    and pF: "p \<in> poly_over F"
    and stable: "\<And>\<sigma>. \<sigma> \<in> field_auto K F \<Longrightarrow> \<sigma> ` E = E"
shows "group_epimorphism (galois_restriction K E F)
      (field_auto K F) (compose K) (identity K)
      (field_auto E F) (compose E) (identity E)"
proof -
  have Ksub: "Subfield K"
    using splitting_field_subfield[OF split]
    by (simp add: complex_subfield_iff_subfield)
  have EK: "E \<subseteq> K"
    by (rule splitting_field_base_subset[OF split])
  have image_eq: "galois_restriction K E F ` field_auto K F = field_auto E F"
    by (rule galois_restriction_image_of_splitting_field[OF split sfE sfF FE pF stable])
  show ?thesis
    by (rule galois_restriction_epimorphism[OF Ksub sfE FE EK stable image_eq])
qed

context
  fixes K E F :: "complex set" and p :: "complex poly"
  assumes split: "splitting_field F p K"
    and sfF: "complex_subfield F"
    and E: "E \<in> inter_fields K F"
    and stable: "\<And>\<sigma>. \<sigma> \<in> field_auto K F \<Longrightarrow> \<sigma> ` E = E"
begin

text \<open>Now specialise to an intermediate field of a splitting field over the full base.\<close>
lemma splitting_field_restriction_image:
  "galois_restriction K E F ` field_auto K F = field_auto E F"
proof -
  obtain FE: "F \<subseteq> E"
    using E by (auto simp: inter_fields_iff)
  have sfE: "Subfield E"
    using E by (auto simp: inter_fields_iff complex_subfield_iff_subfield)
  have sfF': "Subfield F"
    using sfF by (simp add: complex_subfield_iff_subfield)
  have splitE: "splitting_field E p K"
    by (rule splitting_field_over_intermediate[OF split E])
  have pF: "p \<in> poly_over F"
    using split by (auto simp: splitting_fieldD)
  show ?thesis
    by (rule galois_restriction_image_of_splitting_field[OF splitE sfE sfF' FE pF stable])
qed

lemma splitting_field_restriction_kernel:
  "group_homomorphism.Ker (galois_restriction K E F)
      (field_auto K F) (identity E) = field_auto K E"
proof -
  obtain FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
    using E by (auto simp: inter_fields_iff)
  have sfE: "Subfield E"
    using E by (auto simp: inter_fields_iff complex_subfield_iff_subfield)
  have Ksub: "Subfield K"
    using splitting_field_subfield[OF split]
    by (simp add: complex_subfield_iff_subfield)
  show ?thesis
    by (unfold galois_restriction_def; rule galois_restriction_Ker[OF Ksub sfE FE EK stable])
qed

interpretation restriction: group_epimorphism
    "galois_restriction K E F"
    "field_auto K F" "compose K" "identity K"
    "field_auto E F" "compose E" "identity E"
proof -
  obtain FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
    using E by (auto simp: inter_fields_iff)
  have sfE: "Subfield E"
    using E by (auto simp: inter_fields_iff complex_subfield_iff_subfield)
  have sfF': "Subfield F"
    using sfF by (simp add: complex_subfield_iff_subfield)
  have splitE: "splitting_field E p K"
    by (rule splitting_field_over_intermediate[OF split E])
  have pF: "p \<in> poly_over F"
    using split by (auto simp: splitting_fieldD)
  show "group_epimorphism (galois_restriction K E F)
      (field_auto K F) (compose K) (identity K)
      (field_auto E F) (compose E) (identity E)"
    by (rule galois_restriction_epimorphism_of_splitting_field
      [OF splitE sfE sfF' FE pF stable])
qed

text \<open>The first isomorphism theorem identifies the quotient by the relative automorphism group
  with the Galois group of the stable intermediate field.\<close>
theorem splitting_field_restriction_factor_isomorphism:
  "(restriction.kernel.Factor_Group,
     restriction.kernel.quotient_composition,
     restriction.kernel.Class (identity K)) \<cong>\<^sub>G
    (field_auto E F, compose E, identity E)"
proof -
  have image_eq:
      "galois_restriction K E F ` field_auto K F = field_auto E F"
    using splitting_field_restriction_image .
  have iso:
      "(restriction.kernel.Factor_Group,
       restriction.kernel.quotient_composition,
       restriction.kernel.Class (identity K)) \<cong>\<^sub>G
        (galois_restriction K E F ` field_auto K F, compose E, identity E)"
    by (rule restriction.first_isomorphism)
  show ?thesis using iso image_eq by simp
qed

text \<open>For a finite splitting-field Galois group, the quotient isomorphism gives the expected
  multiplicative cardinality law.  This is a group-order statement; identifying it with a general
  extension dimension is a separate finite-dimensional theorem.\<close>
theorem splitting_field_restriction_card:
  "card (field_auto K F) =
     card (field_auto K E) * card (field_auto E F)"
proof -
  have sfF': "complex_subfield F" by (rule sfF)
  have finite_source: "finite (field_auto K F)"
    by (rule splitting_field_finite_galois_group[OF split sfF'])
  have lagrange:
      "card (field_auto K F) =
         card restriction.Ker * restriction.kernel.index"
    using restriction.kernel.lagrange[OF finite_source] by simp
  have quotient_card: "card restriction.kernel.Factor_Group = restriction.kernel.index"
    using restriction.kernel.card_Factor_Group[OF finite_source] by simp
  have f_exists:
      "\<exists>f. group_isomorphism f restriction.kernel.Factor_Group
        restriction.kernel.quotient_composition (restriction.kernel.Class (identity K))
        (field_auto E F) (compose E) (identity E)"
    using splitting_field_restriction_factor_isomorphism
    by (simp add: isomorphic_as_groups_def)
  obtain f where f_iso:
      "group_isomorphism f restriction.kernel.Factor_Group
        restriction.kernel.quotient_composition (restriction.kernel.Class (identity K))
        (field_auto E F) (compose E) (identity E)"
    using f_exists by blast
  interpret I: group_isomorphism f restriction.kernel.Factor_Group
      restriction.kernel.quotient_composition "restriction.kernel.Class (identity K)"
      "field_auto E F" "compose E" "identity E"
    by (rule f_iso)
  have quotient_target_card: "card restriction.kernel.Factor_Group = card (field_auto E F)"
    using I.bijective by (rule bij_betw_same_card)
  have card_source:
      "card (field_auto K F) = card restriction.Ker * card (field_auto E F)"
    using lagrange quotient_card quotient_target_card by simp
  show ?thesis
    using card_source splitting_field_restriction_kernel by simp
qed

end

end
