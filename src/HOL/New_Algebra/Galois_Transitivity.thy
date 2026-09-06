section \<open>Transitivity of the Galois Action on the Roots\<close>

theory Galois_Transitivity
  imports Iso_Extension_Tower
begin

text \<open>
  The capstone of the iso-extension development: for a polynomial @{term Phi} over a base
  subfield @{term F} whose root set @{term R} is finite and consists of elements algebraic
  over @{term F}, any two roots related by the minimal polynomial of one of them are connected
  by an @{term F}-fixing automorphism of the splitting field @{term "K = generate_field (F \<union> R)"}.
  This is \<^emph>\<open>transitivity\<close> of the Galois action on the roots, the key input to identifying the
  Galois group of an irreducible quintic with @{text "S\<^sub>5"}.

  The construction has three parts: a base isomorphism \<open>F(a) \<cong> F(b)\<close> sending @{term a} to
  @{term b} (the single-step @{thm [source] field_hom_on.iso_extension}); its extension across
  the remaining roots (@{thm [source] field_hom_on_extend_finite}); and the observation that the
  resulting embedding permutes the finite root set and therefore maps the splitting field onto
  itself (@{thm [source] field_hom_on.image_generate_field_eq}), i.e.\ is an automorphism.
\<close>

text \<open>The identity is a homomorphism of any subfield --- the starting point of the tower.\<close>
lemma field_hom_on_id:
  assumes "Subfield K" shows "field_hom_on K (\<lambda>x. x)"
proof -
  interpret Subfield K by fact
  show ?thesis by unfold_locales auto
qed

text \<open>An endomorphism fixing @{term F} pointwise leaves every polynomial over @{term F}
  unchanged under @{term map_poly}.\<close>
lemma map_poly_fix:
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

text \<open>Hence such an endomorphism sends a root of @{term Phi} to a root of @{term Phi}.\<close>
lemma hom_preserves_roots:
  fixes f :: "'a :: field \<Rightarrow> 'a"
  assumes hom: "field_hom_on K f" and sfF: "Subfield F" and FK: "F \<subseteq> K"
    and fixF: "\<And>x. x \<in> F \<Longrightarrow> f x = x"
    and Phi: "Phi \<in> poly_over F" and r: "r \<in> K" and root: "poly Phi r = 0"
  shows "poly Phi (f r) = 0"
proof -
  have PhiK: "Phi \<in> poly_over K"
    using Phi poly_over_mono[OF FK] by blast
  have "poly Phi (f r) = poly (map_poly f Phi) (f r)"
    using map_poly_fix[OF hom sfF Phi fixF] by simp
  also have "\<dots> = f (poly Phi r)"
    by (rule field_hom_on.poly_map_poly_hom[OF hom PhiK r])
  also have "\<dots> = 0" using root field_hom_on.hom_0[OF hom] by simp
  finally show ?thesis .
qed

theorem galois_transitive:
  fixes F :: "'a :: field set"
  assumes sfF: "Subfield F"
    and finR: "finite R"
    and algR: "\<And>r. r \<in> R \<Longrightarrow> algebraic_over F r"
    and Phi: "Phi \<in> poly_over F"
    and rootsR: "R = {r. poly Phi r = 0}"
    and closed: "\<And>q :: 'a poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
    and a: "a \<in> R" and b: "b \<in> R"
    and m: "is_minpoly F a m" and mb: "poly m b = 0"
  defines "K \<equiv> generate_field (F \<union> R)"
  shows "\<exists>\<sigma>. field_hom_on K \<sigma> \<and> \<sigma> a = b \<and> (\<forall>x\<in>F. \<sigma> x = x) \<and> \<sigma> ` K = K"
proof -
  \<comment> \<open>Step 1: the base isomorphism on \<open>F(a)\<close> sending \<open>a\<close> to \<open>b\<close>.\<close>
  interpret F: field_hom_on F "\<lambda>x. x" by (rule field_hom_on_id[OF sfF])
  have alga: "algebraic_over F a" using a by (rule algR)
  have mapm: "map_poly (\<lambda>x. x) m = m" by (intro poly_eqI) (simp add: coeff_map_poly)
  have rootb: "poly (map_poly (\<lambda>x. x) m) b = 0" unfolding mapm by (rule mb)
  obtain g0 where g0: "field_hom_on (eval_img F a) g0" "g0 a = b" "\<forall>x\<in>F. g0 x = x"
    using F.iso_extension[OF alga m rootb] by blast

  \<comment> \<open>Step 2: extend the base isomorphism over the remaining roots.\<close>
  define E where "E = eval_img F a"
  have sfE: "Subfield E" unfolding E_def by (rule Subfield.subfield_eval_img[OF sfF alga])
  have FsubE: "F \<subseteq> E" unfolding E_def using Subfield.eval_img_base[OF sfF] by auto
  have algRE: "\<And>r. r \<in> R - {a} \<Longrightarrow> algebraic_over E r"
    using algR FsubE by (auto intro: algebraic_over_mono)
  have finRa: "finite (R - {a})" using finR by simp
  obtain g where g: "field_hom_on (generate_field (E \<union> (R - {a}))) g" "\<forall>x\<in>E. g x = g0 x"
    using field_hom_on_extend_finite[OF closed finRa g0(1)[folded E_def] algRE] by blast

  \<comment> \<open>Step 3: the extended domain is exactly the splitting field \<open>K\<close>.\<close>
  have Edef: "E = generate_field (F \<union> {a})"
    unfolding E_def by (rule Subfield.eval_img_eq_generate_field[OF sfF alga])
  have domK: "generate_field (E \<union> (R - {a})) = K"
  proof -
    have "generate_field (E \<union> (R - {a})) = generate_field (generate_field (F \<union> {a}) \<union> (R - {a}))"
      by (simp add: Edef)
    also have "\<dots> = generate_field ((F \<union> {a}) \<union> (R - {a}))"
      by (rule generate_field_Un_collapse1)
    also have "(F \<union> {a}) \<union> (R - {a}) = F \<union> R" using a by auto
    finally show ?thesis by (simp add: K_def)
  qed
  have homg: "field_hom_on K g" using g(1) domK by simp
  interpret G: field_hom_on K g by (rule homg)

  \<comment> \<open>\<open>g\<close> fixes \<open>F\<close> and sends \<open>a\<close> to \<open>b\<close>.\<close>
  have gfixF: "\<And>x. x \<in> F \<Longrightarrow> g x = x"
    using g(2) g0(3) FsubE by auto
  have gab: "g a = b"
  proof -
    have "a \<in> E" unfolding E_def using Subfield.eval_img_self[OF sfF] by auto
    then have "g a = g0 a" using g(2) by simp
    then show ?thesis using g0(2) by simp
  qed

  \<comment> \<open>Step 4: \<open>g\<close> permutes the root set, hence maps \<open>K\<close> onto itself.\<close>
  have RsubK: "R \<subseteq> K"
    unfolding K_def using subset_generate_field by blast
  have FsubK: "F \<subseteq> K"
    unfolding K_def using subset_generate_field by blast
  have gR_sub: "g ` R \<subseteq> R"
  proof
    fix y assume "y \<in> g ` R"
    then obtain r where r: "r \<in> R" "y = g r" by blast
    have rK: "r \<in> K" using r(1) RsubK by blast
    have "poly Phi r = 0" using r(1) unfolding rootsR by blast
    then have "poly Phi (g r) = 0"
      using hom_preserves_roots[OF homg sfF FsubK gfixF Phi rK] by blast
    then have "g r \<in> R" unfolding rootsR by blast
    then show "y \<in> R" using r(2) by simp
  qed
  have gR_eq: "g ` R = R"
  proof -
    have "inj_on g R" using G.inj_on RsubK by (rule inj_on_subset)
    then show ?thesis using gR_sub finR by (simp add: endo_inj_surj)
  qed
  have gF_eq: "g ` F = F"
  proof
    show "g ` F \<subseteq> F" using gfixF by auto
    show "F \<subseteq> g ` F" using gfixF by force
  qed
  have FRsubK: "F \<union> R \<subseteq> K" using FsubK RsubK by blast
  have "g ` K = g ` generate_field (F \<union> R)" by (simp add: K_def)
  also have "\<dots> = generate_field (g ` (F \<union> R))"
    by (rule G.image_generate_field_eq[OF FRsubK])
  also have "g ` (F \<union> R) = F \<union> R" using gF_eq gR_eq by (simp add: image_Un)
  also have "generate_field (F \<union> R) = K" by (simp add: K_def)
  finally have gK: "g ` K = K" .

  show ?thesis using homg gab gfixF gK by blast
qed

text \<open>For an \<^emph>\<open>irreducible\<close> polynomial the minimal-polynomial hypothesis is automatic, so the
  Galois action is transitive on its roots: any two roots are related by an @{term F}-fixing
  automorphism of the splitting field.\<close>
corollary galois_transitive_irreducible:
  fixes F :: "'a :: field set"
  assumes sfF: "Subfield F"
    and finR: "finite R"
    and algR: "\<And>r. r \<in> R \<Longrightarrow> algebraic_over F r"
    and Phi: "Phi \<in> poly_over F"
    and irr: "irreducible_over F Phi"
    and rootsR: "R = {r. poly Phi r = 0}"
    and closed: "\<And>q :: 'a poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
    and a: "a \<in> R" and b: "b \<in> R"
  defines "K \<equiv> generate_field (F \<union> R)"
  shows "\<exists>\<sigma>. field_hom_on K \<sigma> \<and> \<sigma> a = b \<and> (\<forall>x\<in>F. \<sigma> x = x) \<and> \<sigma> ` K = K"
proof -
  have alga: "algebraic_over F a" using a by (rule algR)
  obtain m where m: "is_minpoly F a m" using Subfield.minpoly_exists[OF sfF alga] by blast
  have pa: "poly Phi a = 0" using a unfolding rootsR by blast
  have pb: "poly Phi b = 0" using b unfolding rootsR by blast
  have mb: "poly m b = 0"
    by (rule Subfield.irreducible_over_root_is_minpoly_root[OF sfF irr Phi m pa pb])
  show ?thesis
    unfolding K_def
    by (rule galois_transitive[OF sfF finR algR Phi rootsR closed a b m mb])
qed

end
