section \<open>Fixed Fields and Degree Formulas for Normal Extensions\<close>

theory Galois_Simple_Degree
  imports Galois_Correspondence Galois_Normality Algebraic_Transitivity Galois_Degree
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

subsection \<open>Simple normal extensions\<close>

subsection \<open>Algebraicity of generated splitting fields\<close>

text \<open>The generic algebraicity closure for generated fields lives in
  \<open>Algebraic_Transitivity\<close>.  This complex-specific wrapper applies it to the
  root set of a splitting-field presentation.\<close>

text \<open>Complex splitting fields are algebraic over their base.  Their generators are the root
set of the defining nonzero polynomial, and the preceding closure result applies to that set
directly (in fact, it does not need the root set's finiteness).
\<close>
lemma splitting_field_algebraic_extension:
  fixes F K :: "complex set" and q :: "complex poly"
  assumes split: "splitting_field F q K" and sfF: "complex_subfield F"
  shows "algebraic_extension K F"
proof (rule algebraic_extensionI)
  fix x assume xK: "x \<in> K"
  have sfF': "Subfield F"
    using sfF by (simp add: complex_subfield_iff_subfield)
  have algR: "\<And>r. r \<in> poly_root_set q \<Longrightarrow> algebraic_over F r"
    by (rule splitting_field_root_algebraic[OF split])
  have algK: "\<And>x. x \<in> generate_field (F \<union> poly_root_set q) \<Longrightarrow> algebraic_over F x"
    by (rule generated_algebraic[OF sfF' algR])
  have Kdef: "K = generate_field (F \<union> poly_root_set q)"
    using splitting_fieldD[OF split] gen_subfield_eq_generate_field by simp
  show "algebraic_over F x"
    using algK xK by (simp add: Kdef)
qed

theorem splitting_field_normal_separable:
  fixes F K :: "complex set" and q :: "complex poly"
  assumes split: "splitting_field F q K" and sfF: "complex_subfield F"
  shows "normal_extension K F \<and> separable_extension K F"
proof (intro conjI)
  show "normal_extension K F"
    by (rule splitting_field_normal[OF split sfF])
  show "separable_extension K F"
    by (rule complex_extension_separable[OF sfF])
qed

text \<open>With the finite-generation bridge in place, the closure theorem no longer needs an
explicit algebraicity premise for an intermediate field of a complex splitting field.
\<close>
theorem fixed_field_eq_of_complex_splitting_field:
  fixes F E K :: "complex set" and q :: "complex poly"
  assumes split: "splitting_field F q K"
    and sfF: "complex_subfield F"
    and E: "E \<in> inter_fields K F"
  shows "fixed_field K (field_auto K E) = E"
proof -
  have FE: "F \<subseteq> E"
    using E by (simp add: inter_fields_iff)
  have algKF: "algebraic_extension K F"
    by (rule splitting_field_algebraic_extension[OF split sfF])
  have algKE: "algebraic_extension K E"
  proof (rule algebraic_extensionI)
    fix x assume xK: "x \<in> K"
    have algx: "algebraic_over F x"
      by (rule algebraic_extensionD[OF algKF xK])
    show "algebraic_over E x"
      by (rule algebraic_over_mono[OF algx FE])
  qed
  show ?thesis
    by (rule fixed_field_eq_of_splitting_field[OF split E algKE])
qed

text \<open>
  The simple normal case is the degree-bearing part of the field-side correspondence.  The
  existing Galois-degree theorem counts the automorphisms; this theory connects its hypotheses to
  the splitting-field presentation used by the fixed-field closure theorem.
\<close>

lemma splitting_field_finite_galois_group:
  fixes F K :: "complex set" and q :: "complex poly"
  assumes split: "splitting_field F q K" and sfF: "complex_subfield F"
  shows "finite (field_auto K F)"
proof -
  have sfF': "Subfield F"
    using sfF by (simp add: complex_subfield_iff_subfield)
  have sfK': "Subfield K"
    using splitting_field_subfield[OF split]
    by (simp add: complex_subfield_iff_subfield)
  have FK: "F \<subseteq> K"
    by (rule splitting_field_base_subset[OF split])
  have qF: "q \<in> poly_over F"
    using split by (auto simp: splitting_fieldD)
  have pnz: "q \<noteq> 0"
    using split by (auto simp: splitting_fieldD)
  have Xdef: "poly_root_set q = {r. poly q r = 0}"
    by (simp add: poly_root_set_def)
  have XK: "poly_root_set q \<subseteq> K"
    by (rule splitting_field_roots_subset[OF split])
  have finX: "finite (poly_root_set q)"
    by (rule finite_poly_root_set[OF pnz])
  have Kgen: "K = gen_subfield (F \<union> poly_root_set q)"
    using split by (auto simp: splitting_fieldD gen_subfield_eq_generate_field)
  show "finite (field_auto K F)"
    by (rule finite_field_auto[OF sfK' sfF' FK qF Xdef XK finX Kgen])
qed

lemma simple_normal_splitting_field:
  fixes F :: "complex set" and a :: complex
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
    and normal: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
  shows "splitting_field F (minpoly F a) (eval_img F a)"
proof -
  define R where "R = {r. poly (minpoly F a) r = 0}"
  have sfE: "Subfield (eval_img F a)"
    by (rule Subfield.subfield_eval_img[OF sfF alg])
  have FE: "F \<subseteq> eval_img F a"
    using Subfield.eval_img_base[OF sfF] by blast
  have pF: "minpoly F a \<in> poly_over F"
    by (rule Subfield.minpoly_over[OF sfF alg])
  have pnz: "minpoly F a \<noteq> 0"
    by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have mroot: "poly (minpoly F a) a = 0"
    by (rule Subfield.minpoly_root[OF sfF alg])
  have aR: "a \<in> R"
    using mroot by (simp add: R_def)
  have RE: "R \<subseteq> eval_img F a"
    using normal by (simp add: R_def)
  have Egen: "eval_img F a = generate_field (F \<union> R)"
  proof (rule antisym)
    have "F \<union> {a} \<subseteq> F \<union> R" using aR by blast
    then have "generate_field (F \<union> {a}) \<subseteq> generate_field (F \<union> R)"
      by (rule generate_field_mono)
    then show "eval_img F a \<subseteq> generate_field (F \<union> R)"
      using Subfield.eval_img_eq_generate_field[OF sfF alg] by simp
    show "generate_field (F \<union> R) \<subseteq> eval_img F a"
      using FE RE by (intro generate_field_least[OF sfE]) auto
  qed
  show ?thesis
    unfolding splitting_field_def
    using pF pnz Egen gen_subfield_eq_generate_field
    by (simp add: R_def poly_root_set_def)
qed

text \<open>For a simple normal complex extension, the field-side inverse law and the exact order
formula can be consumed together.  The subgroup-side inverse law is deliberately not reproved
here; it is the separate Artin theorem.
\<close>
theorem simple_normal_field_inverse_and_degree:
  fixes F :: "complex set" and a :: complex
  assumes sfF: "complex_subfield F" and alg: "algebraic_over F a"
    and normal: "{r. poly (minpoly F a) r = 0} \<subseteq> eval_img F a"
  shows "fixed_field (eval_img F a) (field_auto (eval_img F a) F) = F \<and>
    card (field_auto (eval_img F a) F) = ext_degree F a"
proof -
  have sfF': "Subfield F"
    using sfF by (simp add: complex_subfield_iff_subfield)
  have split: "splitting_field F (minpoly F a) (eval_img F a)"
    by (rule simple_normal_splitting_field[OF sfF' alg normal])
  have FE: "F \<subseteq> eval_img F a"
    using Subfield.eval_img_base[OF sfF'] by blast
  have Eint: "F \<in> inter_fields (eval_img F a) F"
    by (rule base_in_inter_fields[OF sfF' FE])
  have fixed:
    "fixed_field (eval_img F a) (field_auto (eval_img F a) F) = F"
    by (rule fixed_field_eq_of_complex_splitting_field[OF split sfF Eint])
  have degree:
    "card (field_auto (eval_img F a) F) = ext_degree F a"
    by (rule galois_simple_normal_degree[OF sfF' alg normal])
  show ?thesis using fixed degree by blast
qed

end
