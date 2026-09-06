section \<open>Fixed fields of finite normal and separable extensions\<close>

theory Galois_Fixed_Field
  imports Galois_Correspondence Galois_Normality
begin

text \<open>
  A splitting field remains a splitting field after enlarging its base to an intermediate field.
  This is the representation bridge needed below: the root set is unchanged, while the base part of
  the generated subfield grows from @{term F} to @{term E}.
\<close>

lemma splitting_field_over_intermediate:
  fixes F E K :: "complex set" and p :: "complex poly"
  assumes split: "splitting_field F p K"
    and E: "E \<in> inter_fields K F"
  shows "splitting_field E p K"
proof -
  obtain FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
    using E by (auto simp: inter_fields_iff)
  have Ksub': "Subfield K"
    by (rule splitting_field_subfield[OF split])
  have Ksub: "complex_subfield K"
    using Ksub' by (simp add: complex_subfield_iff_subfield)
  obtain pF: "p \<in> poly_over F" and pnz: "p \<noteq> 0"
    and Kdef: "K = gen_subfield (F \<union> poly_root_set p)"
    using split by (auto simp: splitting_fieldD gen_subfield_eq_generate_field)
  have pE: "p \<in> poly_over E"
    using pF poly_over_mono[OF FE] by blast
  have RsubK: "poly_root_set p \<subseteq> K"
    using splitting_field_roots_subset[OF split] .
  have KdefE: "K = gen_subfield (E \<union> poly_root_set p)"
  proof (rule antisym)
    show "K \<subseteq> gen_subfield (E \<union> poly_root_set p)"
    proof -
      have FER: "F \<union> poly_root_set p \<subseteq> E \<union> poly_root_set p"
        by (rule Un_mono) (rule FE, rule subset_refl)
      have genE: "E \<union> poly_root_set p \<subseteq> gen_subfield (E \<union> poly_root_set p)"
        by (rule gen_subfield_subset)
      have "F \<union> poly_root_set p \<subseteq> gen_subfield (E \<union> poly_root_set p)"
        by (rule subset_trans[OF FER genE])
      then have "gen_subfield (F \<union> poly_root_set p) \<subseteq>
          gen_subfield (E \<union> poly_root_set p)"
        by (rule gen_subfield_minimal[OF gen_subfield_is_subfield])
      then show ?thesis using Kdef by simp
    qed
    show "gen_subfield (E \<union> poly_root_set p) \<subseteq> K"
    proof (rule gen_subfield_minimal[OF Ksub])
      show "E \<union> poly_root_set p \<subseteq> K"
      proof
        fix y assume y: "y \<in> E \<union> poly_root_set p"
        show "y \<in> K"
        proof (cases "y \<in> E")
          case True
          then show "y \<in> K" using EK by blast
        next
          case False
          then have "y \<in> poly_root_set p" using y by simp
          then show "y \<in> K" using RsubK by blast
        qed
      qed
    qed
  qed
  show ?thesis
    unfolding splitting_field_def
    using pE pnz KdefE by (simp add: gen_subfield_eq_generate_field)
qed

lemma card_gt_one_imp_exists_mem_ne:
  fixes A :: "'a set" and x :: "'a" and n :: nat
  assumes xA: "x \<in> A"
    and cardA: "card A = n"
    and ngt: "1 < n"
  shows "\<exists>b. b \<in> A \<and> b \<noteq> x"
proof (rule ccontr)
  assume no_b: "\<not> (\<exists>b. b \<in> A \<and> b \<noteq> x)"
  have "A \<subseteq> {x}" using no_b by auto
  then have Aeq: "A = {x}" using xA by auto
  have card_one: "card A = 1" using Aeq by simp
  have n_one: "n = 1" using card_one cardA by simp
  have impossible: "(1 :: nat) < 1"
    using ngt n_one by (simp add: n_one)
  have impossible_false: False
    using impossible by (rule less_irrefl_nat)
  from impossible_false show False .
qed

text \<open>
  The closure half of the correspondence is most transparent as a separation statement.  If an
  element of a finite splitting field is outside the intermediate field, its minimal polynomial has
  a second root: characteristic zero gives distinct roots, and degree one is exactly the criterion
  for already belonging to the base.  The root-transfer theorem then supplies an automorphism fixing
  the intermediate field that moves the element.

  The explicit @{term algebraic_extension} assumption records the finite-extension input without
  importing Artin or an algebraic-closure construction.  A later finite-generation layer can discharge
  it for the intended classes of root-generated extensions.
\<close>

theorem fixed_field_eq_of_splitting_field:
  fixes K F E :: "complex set" and p :: "complex poly"
  assumes split: "splitting_field F p K"
    and E: "E \<in> inter_fields K F"
    and alg: "algebraic_extension K E"
  shows "fixed_field K (field_auto K E) = E"
proof (rule antisym)
  have Ksub': "Subfield K"
    by (rule splitting_field_subfield[OF split])
  have Ksub: "complex_subfield K"
    using Ksub' by (simp add: complex_subfield_iff_subfield)
  have sfE: "Subfield E"
    using E by (auto simp: inter_fields_iff)
  show "fixed_field K (field_auto K E) \<subseteq> E"
  proof
    fix x assume xfix: "x \<in> fixed_field K (field_auto K E)"
    have xK: "x \<in> K"
      using xfix by (auto simp: fixed_field_def)
    have fixed: "\<forall>\<sigma> \<in> field_auto K E. \<sigma> x = x"
      using xfix by (auto simp: fixed_field_def)
    show "x \<in> E"
    proof (rule ccontr)
      assume xnotE: "x \<notin> E"
      have algx: "algebraic_over E x"
        by (rule algebraic_extensionD[OF alg xK])
      have splitE: "splitting_field E p K"
        by (rule splitting_field_over_intermediate[OF split E])
      have minp: "is_minpoly E x (minpoly E x)"
        by (rule Subfield.is_minpoly_minpoly[OF sfE algx])
      have xroot: "poly (minpoly E x) x = 0"
        by (rule Subfield.minpoly_root[OF sfE algx])
      have deg_gt: "1 < ext_degree E x"
      proof -
        have degree_ne: "ext_degree E x \<noteq> 1"
        proof
          assume "ext_degree E x = 1"
          then have "x \<in> E"
            using Subfield.ext_degree_eq_1_iff[OF sfE algx] by blast
          then show False using xnotE by simp
        qed
        have degree_pos: "0 < ext_degree E x"
          by (rule Subfield.ext_degree_pos[OF sfE algx])
        then show ?thesis using degree_ne by simp
      qed
      define R where "R = {r. poly (minpoly E x) r = 0}"
      have cardR: "card R = ext_degree E x"
        unfolding R_def by (rule card_minpoly_roots_eq_ext_degree[OF sfE algx])
      have xR: "x \<in> R"
        unfolding R_def using xroot by simp
      obtain b where bR: "b \<in> R" and bne: "b \<noteq> x"
        using card_gt_one_imp_exists_mem_ne[OF xR cardR deg_gt] by blast
      have mb: "poly (minpoly E x) b = 0"
        using bR by (simp add: R_def)
      obtain \<sigma> where s: "\<sigma> \<in> field_auto K E" and moved: "\<sigma> x = b"
        using splitting_field_root_transfer[OF splitE sfE algx xK minp mb] by blast
      have "\<sigma> x = x" using fixed s by blast
      then show False using moved bne by simp
    qed
  qed
  show "E \<subseteq> fixed_field K (field_auto K E)"
    using E by (auto simp: inter_fields_iff fixed_field_def field_auto_def)
qed

end
