section \<open>Normal and separable complex field extensions\<close>

theory Galois_Normality
  imports Iso_Extension_Tower Extension_Properties
begin

text \<open>
  The generic extension predicates and their root-set API live in
  \<open>Extension_Properties\<close>.  This theory supplies the complex-specific
  characteristic-zero and algebraically-closed-field arguments needed by the Galois development:
  normality is witnessed by root transfer, while separability follows from the nonvanishing
  characteristic.

  The root-transfer theorem below is the useful bridge: an isomorphism between two simple
  subextensions extends across the finite root set, and therefore becomes an automorphism of the
  complex splitting field.
\<close>

text \<open>In characteristic zero every algebraic element is separable.  This is the only
  separability input needed here; keeping the Bezout argument local avoids importing the
  Galois-degree and symmetric-generation developments into the normality layer.\<close>
lemma (in Subfield) galois_normality_poly_over_pderiv:
  assumes "p \<in> poly_over K"
  shows "pderiv p \<in> poly_over K"
proof (rule poly_overI)
  fix i
  have "coeff (pderiv p) i = of_nat (Suc i) * coeff p (Suc i)"
    by (rule coeff_pderiv)
  moreover have "of_nat (Suc i) \<in> K" by (rule of_nat_closed)
  moreover have "coeff p (Suc i) \<in> K" using assms by (rule poly_over_coeff)
  ultimately show "coeff (pderiv p) i \<in> K" by (simp add: mult_closed)
qed

lemma rsquarefree_minpoly_char_0:
  fixes F :: "'a :: field_char_0 set" and a :: 'a
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
  shows "rsquarefree (minpoly F a)"
proof -
  define m where "m = minpoly F a"
  have ism: "is_minpoly F a m"
    unfolding m_def by (rule Subfield.is_minpoly_minpoly[OF sfF alg])
  have mF: "m \<in> poly_over F"
    unfolding m_def by (rule Subfield.minpoly_over[OF sfF alg])
  have mnz: "m \<noteq> 0"
    unfolding m_def by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have mdeg: "degree m > 0"
    unfolding m_def
    by (rule Subfield.minpoly_degree_pos[OF sfF
      Subfield.is_minpoly_minpoly[OF sfF alg]])
  have pmF: "pderiv m \<in> poly_over F"
    using Subfield.galois_normality_poly_over_pderiv[OF sfF mF] .
  have pmnz: "pderiv m \<noteq> 0"
    using mdeg by (simp add: pderiv_eq_0_iff)
  have pmdeg: "degree (pderiv m) < degree m"
    using mdeg by (simp add: degree_pderiv)
  have ndvd: "\<not> m dvd pderiv m"
  proof
    assume "m dvd pderiv m"
    then have "degree m \<le> degree (pderiv m)"
      using pmnz by (rule dvd_imp_degree_le)
    then show False using pmdeg by simp
  qed
  obtain u v where u: "u \<in> poly_over F" and v: "v \<in> poly_over F"
    and bez: "u * m + v * pderiv m = 1"
    using Subfield.minpoly_bezout[OF sfF ism pmF ndvd] by blast
  have "\<not> (poly m r = 0 \<and> poly (pderiv m) r = 0)" for r
  proof
    assume "poly m r = 0 \<and> poly (pderiv m) r = 0"
    then have "poly (u * m + v * pderiv m) r = 0"
      by simp
    then have "(1 :: 'a) = 0" using bez by simp
    then show False by simp
  qed
  then show ?thesis unfolding m_def [symmetric]
    using mnz by (simp add: rsquarefree_roots)
qed

text \<open>In characteristic zero, the distinct complex roots of an algebraic element's minimal
polynomial are counted by its simple extension degree.  This elementary root-count bridge is kept
with the separability API so later Galois results need not import the Galois-action machinery.\<close>
lemma card_minpoly_roots_eq_ext_degree:
  fixes F :: "complex set" and a :: complex
  assumes sfF: "Subfield F" and alg: "algebraic_over F a"
  shows "card {r. poly (minpoly F a) r = 0} = ext_degree F a"
proof -
  define m where "m = minpoly F a"
  have mnz: "m \<noteq> 0"
    unfolding m_def by (rule Subfield.minpoly_nonzero[OF sfF alg])
  have monic: "lead_coeff m = 1"
    unfolding m_def by (rule Subfield.minpoly_monic[OF sfF alg])
  have rsf: "rsquarefree m"
    unfolding m_def by (rule rsquarefree_minpoly_char_0[OF sfF alg])
  have finR: "finite {z. poly m z = 0}"
    using mnz by (rule poly_roots_finite)
  have decomp: "smult (lead_coeff m) (\<Prod>z | poly m z = 0. [:- z, 1:]) = m"
    using rsf by (rule complex_poly_decompose_rsquarefree)
  have "degree m = degree (\<Prod>z | poly m z = 0. [:- z, 1:])"
    using decomp monic by (metis smult_1_left)
  also have "\<dots> = (\<Sum>z | poly m z = 0. degree [:- z, 1:])"
    using finR by (subst degree_prod_eq_sum_degree) auto
  also have "\<dots> = card {z. poly m z = 0}" by simp
  finally show ?thesis by (simp add: ext_degree_def m_def)
qed

text \<open>Every complex extension is separable whenever the element under consideration is algebraic.\<close>
theorem complex_extension_separable:
  assumes sfF: "complex_subfield F"
  shows "separable_extension K F"
proof (rule separable_extensionI)
  fix a assume aK: "a \<in> K" and alg: "algebraic_over F a"
  have sfF': "Subfield F" using sfF
    by (simp add: complex_subfield_iff_subfield)
  show "rsquarefree (minpoly F a)"
    by (rule rsquarefree_minpoly_char_0[OF sfF' alg])
qed

text \<open>The root-transfer argument needs only the elementary homomorphism facts from the
  transitivity development.  They are kept here as a small local interface so that this
  normality layer does not depend on the later Galois-action theory.\<close>
lemma normality_field_hom_on_id:
  assumes "Subfield K"
  shows "field_hom_on K (\<lambda>x. x)"
proof -
  interpret Subfield K by fact
  show ?thesis by unfold_locales auto
qed

lemma normality_map_poly_fix:
  fixes f :: "'a :: field \<Rightarrow> 'a"
  assumes hom: "field_hom_on K f" and sfF: "Subfield F"
    and p: "p \<in> poly_over F" and fixF: "\<And>x. x \<in> F \<Longrightarrow> f x = x"
  shows "map_poly f p = p"
proof (rule poly_eqI)
  fix n
  have cF: "coeff p n \<in> F" using p by (rule Subfield.poly_over_coeff[OF sfF])
  have "coeff (map_poly f p) n = f (coeff p n)"
    by (rule field_hom_on.coeff_map_poly_f[OF hom])
  also have "\<dots> = coeff p n" using cF by (rule fixF)
  finally show "coeff (map_poly f p) n = coeff p n" .
qed

lemma normality_hom_preserves_roots:
  fixes f :: "'a :: field \<Rightarrow> 'a"
  assumes hom: "field_hom_on K f" and sfF: "Subfield F" and FK: "F \<subseteq> K"
    and fixF: "\<And>x. x \<in> F \<Longrightarrow> f x = x"
    and Phi: "Phi \<in> poly_over F" and r: "r \<in> K" and root: "poly Phi r = 0"
  shows "poly Phi (f r) = 0"
proof -
  have PhiK: "Phi \<in> poly_over K"
    using Phi poly_over_mono[OF FK] by blast
  have "poly Phi (f r) = poly (map_poly f Phi) (f r)"
    using normality_map_poly_fix[OF hom sfF Phi fixF] by simp
  also have "\<dots> = f (poly Phi r)"
    by (rule field_hom_on.poly_map_poly_hom[OF hom PhiK r])
  also have "\<dots> = 0" using root field_hom_on.hom_0[OF hom] by simp
  finally show ?thesis .
qed

text \<open>Extend a conjugacy between two simple subextensions across the root set of a splitting field.
  The resulting map permutes that finite root set, hence maps the generated field onto itself.\<close>
theorem splitting_field_root_transfer:
  fixes F K :: "complex set" and p m :: "complex poly" and a b :: complex
  assumes split: "splitting_field F p K"
    and sfF: "Subfield F"
    and alg: "algebraic_over F a"
    and aK: "a \<in> K"
    and minp: "is_minpoly F a m"
    and root: "poly m b = 0"
  shows "\<exists>\<sigma> \<in> field_auto K F. \<sigma> a = b"
proof -
  have pF: "p \<in> poly_over F" and pnz: "p \<noteq> 0"
    and Kgen: "K = generate_field (F \<union> poly_root_set p)"
    using split by (auto simp: splitting_fieldD)
  have Kdef: "K = gen_subfield (F \<union> poly_root_set p)"
    using Kgen by (simp add: gen_subfield_eq_generate_field)
  have sfKc: "complex_subfield K"
  proof -
    have sfKc0: "complex_subfield (gen_subfield (F \<union> poly_root_set p))"
      by (rule gen_subfield_is_subfield)
    then show ?thesis using Kdef by blast
  qed
  have sfK: "Subfield K" using sfKc by (simp add: complex_subfield_iff_subfield)
  have FK: "F \<subseteq> K"
    using Kdef gen_subfield_subset by blast
  have Rfin: "finite (poly_root_set p)"
    using pnz by (rule finite_poly_root_set)
  have Ralg: "\<And>r. r \<in> poly_root_set p \<Longrightarrow> algebraic_over F r"
    by (intro splitting_field_root_algebraic[OF split])
  interpret F: field_hom_on F "(\<lambda>x. x)"
    by (rule normality_field_hom_on_id[OF sfF])
  have map_minp: "map_poly (\<lambda>x. x) m = m"
    by (rule poly_eqI) simp
  have root_image: "poly (map_poly (\<lambda>x. x) m) b = 0"
    using root by (simp only: map_minp)
  obtain g0 where g0: "field_hom_on (eval_img F a) g0"
    and g0a: "g0 a = b" and g0F: "\<forall>x \<in> F. g0 x = x"
    using F.iso_extension[OF alg minp root_image] by blast
  define E where "E = eval_img F a"
  have sfE: "Subfield E"
    unfolding E_def by (rule Subfield.subfield_eval_img[OF sfF alg])
  have FE: "F \<subseteq> E"
    unfolding E_def using Subfield.eval_img_base[OF sfF] by blast
  have g0E: "field_hom_on E g0" using g0 by (simp add: E_def)
  have RalgE: "\<And>r. r \<in> poly_root_set p \<Longrightarrow> algebraic_over E r"
    using Ralg FE by (blast intro: algebraic_over_mono)
  have closed: "\<And>q :: complex poly. 0 < degree q \<Longrightarrow> \<exists>c. poly q c = 0"
    by (intro allI impI fundamental_theorem_of_algebra) (simp add: constant_degree)
  obtain g where g: "field_hom_on (generate_field (E \<union> poly_root_set p)) g"
    and gE: "\<forall>x \<in> E. g x = g0 x"
    using field_hom_on_extend_finite[OF closed Rfin g0E RalgE] by blast
  have Egen: "E = generate_field (F \<union> {a})"
    unfolding E_def by (rule Subfield.eval_img_eq_generate_field[OF sfF alg])
  have EsubK: "E \<subseteq> K"
  proof -
    have FKa: "F \<union> {a} \<subseteq> K" using FK aK by blast
    have "generate_field (F \<union> {a}) \<subseteq> K"
      by (rule generate_field_least[OF sfK FKa])
    then show ?thesis using Egen by simp
  qed
  have LsubK: "generate_field (E \<union> poly_root_set p) \<subseteq> K"
  proof -
    have EL: "E \<union> poly_root_set p \<subseteq> K"
      using EsubK splitting_field_roots_subset[OF split] by blast
    show ?thesis by (rule generate_field_least[OF sfK EL])
  qed
  have KsubL: "K \<subseteq> generate_field (E \<union> poly_root_set p)"
  proof -
    have FRsub: "F \<union> poly_root_set p \<subseteq> generate_field (E \<union> poly_root_set p)"
      using FE subset_generate_field[of "E \<union> poly_root_set p"] by blast
    have sfL0: "Subfield (generate_field (E \<union> poly_root_set p))"
      by (rule subfield_generate_field)
    have sfL: "complex_subfield (generate_field (E \<union> poly_root_set p))"
      using sfL0 by (simp add: complex_subfield_iff_subfield)
    have geninc: "gen_subfield (F \<union> poly_root_set p) \<subseteq>
        generate_field (E \<union> poly_root_set p)"
      by (rule gen_subfield_minimal[OF sfL FRsub])
    show ?thesis
    proof
      fix x assume xK: "x \<in> K"
      have xgen: "x \<in> gen_subfield (F \<union> poly_root_set p)"
        using xK Kdef by (simp only: Kdef)
      then show "x \<in> generate_field (E \<union> poly_root_set p)"
        by (rule geninc[THEN subsetD])
    qed
  qed
  have dom_eq: "generate_field (E \<union> poly_root_set p) = K"
    using LsubK KsubL by (rule antisym)
  have homK: "field_hom_on K g" using g dom_eq by simp
  interpret G: field_hom_on K g by (rule homK)
  have gfixF: "\<And>x. x \<in> F \<Longrightarrow> g x = x"
  proof -
    fix x assume xF: "x \<in> F"
    have xE: "x \<in> E" using FE xF by blast
    have "g x = g0 x" using gE xE by blast
    also have "g0 x = x" using g0F xF by blast
    finally show "g x = x" .
  qed
  have RsubK: "poly_root_set p \<subseteq> K"
    using splitting_field_roots_subset[OF split] .
  have pK: "p \<in> poly_over K"
    using pF poly_over_mono[OF FK] by blast
  have p_fix: "map_poly g p = p"
    by (rule normality_map_poly_fix[OF homK sfF pF gfixF])
  have gRsub: "g ` poly_root_set p \<subseteq> poly_root_set p"
  proof
    fix y assume "y \<in> g ` poly_root_set p"
    then obtain r where rR: "r \<in> poly_root_set p" and y: "y = g r" by blast
    have rK: "r \<in> K" using RsubK rR by blast
    have rroot: "poly p r = 0" using rR by (simp only: poly_root_set_iff)
    have groot: "poly p (g r) = 0"
    proof -
      have "poly p (g r) = poly (map_poly g p) (g r)"
        using p_fix by simp
      also have "\<dots> = g (poly p r)"
        by (rule field_hom_on.poly_map_poly_hom[OF homK pK rK])
      also have "g (poly p r) = g 0" by (simp only: rroot)
      also have "\<dots> = 0" by (rule field_hom_on.hom_0[OF homK])
      finally show ?thesis .
    qed
    show "y \<in> poly_root_set p" using y groot by (simp only: poly_root_set_iff)
  qed
  have gReq: "g ` poly_root_set p = poly_root_set p"
  proof -
    have inj: "inj_on g (poly_root_set p)"
      using G.inj_on RsubK by (rule inj_on_subset)
    show ?thesis by (rule endo_inj_surj[OF Rfin gRsub inj])
  qed
  have gF_eq: "g ` F = F"
  proof (rule subset_antisym)
    show "g ` F \<subseteq> F"
      using gfixF by (auto intro: image_eqI[where x=x])
    show "F \<subseteq> g ` F"
      using gfixF by (auto intro: image_eqI[where x=x])
  qed
  have FRK: "F \<union> poly_root_set p \<subseteq> K" using FK RsubK by blast
  have Kgen: "K = generate_field (F \<union> poly_root_set p)"
    using Kdef gen_subfield_eq_generate_field by simp
  have gK: "g ` K = K"
  proof -
    have gUn: "g ` (F \<union> poly_root_set p) = F \<union> poly_root_set p"
      by (simp only: image_Un gF_eq gReq)
    have "g ` K = g ` generate_field (F \<union> poly_root_set p)" by (simp add: Kgen)
    also have "\<dots> = generate_field (g ` (F \<union> poly_root_set p))"
      by (rule G.image_generate_field_eq[OF FRK])
    also have "\<dots> = generate_field (F \<union> poly_root_set p)"
      by (rule arg_cong[OF gUn])
    also have "generate_field (F \<union> poly_root_set p) = K"
      using Kgen by simp
    finally show ?thesis .
  qed
  have aut: "restrict g K \<in> field_auto K F"
    using field_hom_on_imp_field_auto[OF homK gK gfixF FK] .
  have aE: "a \<in> E" unfolding E_def by (rule Subfield.eval_img_self[OF sfF])
  have "restrict g K a = b"
    using aK aE g gE g0a by simp
  then show ?thesis using aut by blast
qed

text \<open>A splitting field is normal in the root-theoretic sense.  The proof does not assume that the
  polynomial used to construct the splitting field is irreducible: the finite root set is only the
  carrier across which the simple conjugacy is extended.
\<close>
theorem splitting_field_normal:
  assumes split: "splitting_field F p K" and sfF: "complex_subfield F"
  shows "normal_extension K F"
proof (rule normal_extensionI)
  fix q a
  assume qF: "q \<in> poly_over F" and irr: "irreducible_over F q"
    and aK: "a \<in> K" and qa: "poly q a = 0"
  have sfF': "Subfield F" using sfF by (simp add: complex_subfield_iff_subfield)
  have alg: "algebraic_over F a"
    unfolding algebraic_over_def using qF qa irr by (auto simp: irreducible_over_def)
  obtain m where minp: "is_minpoly F a m"
    using Subfield.minpoly_exists[OF sfF' alg] by blast
  have mroot: "poly m b = 0" if "b \<in> poly_root_set q" for b
  proof -
    have qb: "poly q b = 0" using that by (simp add: poly_root_set_def)
    show ?thesis
      by (rule Subfield.irreducible_over_root_is_minpoly_root[OF sfF' irr qF minp qa qb])
  qed
  show "poly_root_set q \<subseteq> K"
  proof
    fix b assume bq: "b \<in> poly_root_set q"
    obtain \<sigma> where s: "\<sigma> \<in> field_auto K F" and sab: "\<sigma> a = b"
      using splitting_field_root_transfer[OF split sfF' alg aK minp mroot[OF bq]] by blast
    have "\<sigma> a \<in> K" using s aK by (auto simp: field_auto_mem_iff)
    then show "b \<in> K" using sab by simp
  qed
qed

end
