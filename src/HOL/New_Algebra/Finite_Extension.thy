section \<open>Finite field extensions and their degree\<close>

theory Finite_Extension
  imports Extension_Degree
begin

text \<open>
  A finite extension is a finitely spanned field tower in the native set-based representation.  The
  underlying vector space already supplies the basis and dimension machinery; this theory gives that
  machinery a field-theoretic name and keeps the extension degree independent of a choice of basis.
\<close>

locale finite_subfield_tower = subfield_tower +
  assumes finite_basis: "\<exists>B. vs.basis B"
begin

definition extension_degree :: nat
  where "extension_degree = vs.dimension"

lemma extension_degree_eq_dimension:
  "extension_degree = vs.dimension"
  by (simp add: extension_degree_def)

lemma extension_degree_eq_card_basis:
  assumes "vs.basis B"
  shows "extension_degree = card B"
  using vs.dimension_eq_any_field[OF assms]
  by (simp add: extension_degree_def)

lemma finite_basis_exists:
  "\<exists>B. vs.basis B"
  by (rule finite_basis)

text \<open>
  The degree is positive because the ambient field contains distinct zero and one.  This proof does
  not require the carrier of the extension to be finite: finite-dimensionality is exactly the basis
  premise of the locale.
\<close>
lemma extension_degree_pos:
  "extension_degree > 0"
proof -
  obtain B where B: "vs.basis B"
    using finite_basis by blast
  show ?thesis
  proof (rule ccontr)
    assume "\<not> extension_degree > 0"
    then have degree0: "extension_degree = 0" by simp
    have cardB0: "card B = 0"
      using extension_degree_eq_card_basis[OF B] degree0 by simp
    have Bempty_or_infinite: "B = {} \<or> infinite B"
      using cardB0 by (simp add: card_eq_0_iff)
    have Bempty: "B = {}"
      using Bempty_or_infinite B by (simp add: vs.basis_def)
    have oneL: "1 \<in> L" by (rule ext.one_closed)
    obtain c where c: "c \<in> {} \<rightarrow>\<^sub>E K" and one_eq: "1 = vs.lincomb c {}"
      using vs.basis_spanning[OF B, unfolded Bempty] oneL
      unfolding vs.spanning_def by blast
    then have "(1 :: 'a) = 0" by simp
    then show False by simp
  qed
qed

text \<open>
  A simple algebraic extension is finite, and its vector-space dimension is the degree of the minimal
  polynomial.  The substantive basis argument lives in the extension-degree theory; this corollary is
  the stable finite-extension-facing entry point.
\<close>
lemma extension_degree_eq_ext_degree:
  assumes alg: "algebraic_over K a" and L_def: "L = eval_img K a"
  shows "extension_degree = ext_degree K a"
  using simple_extension_dimension_eq_ext_degree[OF alg L_def]
  by (simp add: extension_degree_def)

lemma finite_extension_cardinality:
  assumes "finite L"
  shows "card L = card K ^ extension_degree"
proof -
  have card: "card L = card K ^ vs.dimension"
    by (rule finite_subfield_tower_cardinality[OF assms])
  then show ?thesis by (simp add: extension_degree_def)
qed

text \<open>A finite-dimensional extension of a finite carrier field again has finite carrier.
  A basis identifies the extension bijectively with the finitely supported coordinate functions
  on that basis; when both the basis and coefficient carrier are finite, so is that function
  space.\<close>
lemma finite_carrier_of_finite_base:
  assumes finK: "finite K"
  shows "finite L"
proof -
  obtain B where basis: "vs.basis B"
    using finite_basis_exists by blast
  have finB: "finite B"
    using basis by (simp add: vs.basis_def)
  have fin_coords: "finite (B \<rightarrow>\<^sub>E K)"
    by (rule finite_PiE[OF finB]) (use finK in auto)
  have bij: "bij_betw (\<lambda>c. vs.lincomb c B) (B \<rightarrow>\<^sub>E K) L"
    using basis by (simp add: vs.basis_def)
  have image: "(\<lambda>c. vs.lincomb c B) ` (B \<rightarrow>\<^sub>E K) = L"
    using bij by (simp add: bij_betw_def)
  show ?thesis
    using finite_imageI[OF fin_coords, of "\<lambda>c. vs.lincomb c B"] image by simp
qed

text \<open>Every vector-space basis is also a field-generating set.  One inclusion is minimality of
  @{const generate_field}; the other expands an arbitrary vector in its basis coordinates.\<close>
lemma generate_field_basis:
  assumes basis: "vs.basis B"
  shows "L = generate_field (K \<union> B)"
proof -
  have spanning: "vs.spanning B" by (rule vs.basis_spanning[OF basis])
  have finB: "finite B"
    using spanning unfolding vs.spanning_def by blast
  have BL: "B \<subseteq> L"
    using spanning unfolding vs.spanning_def by blast
  have gen_subset: "generate_field (K \<union> B) \<subseteq> L"
    by (rule generate_field_least[OF ext.Subfield_axioms]) (use base_subset BL in auto)
  have L_subset: "L \<subseteq> generate_field (K \<union> B)"
  proof
    fix x assume xL: "x \<in> L"
    obtain c where c: "c \<in> B \<rightarrow>\<^sub>E K" "x = vs.lincomb c B"
      using vs.basis_spanning[OF basis] xL unfolding vs.spanning_def by blast
    have cK: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> K" using c(1) by auto
    have lincomb_sum: "vs.lincomb c B = (\<Sum>v\<in>B. c v * v)"
      by (rule vs_lincomb_eq_sum[OF finB BL cK])
    interpret G: Subfield "generate_field (K \<union> B)" by (rule subfield_generate_field)
    have sumG: "(\<Sum>v\<in>B. c v * v) \<in> generate_field (K \<union> B)"
      by (rule G.sum_closed, rule G.mult_closed) (use cK in auto)
    show "x \<in> generate_field (K \<union> B)"
      using c(2) lincomb_sum sumG by simp
  qed
  show ?thesis by (rule subset_antisym[OF L_subset gen_subset])
qed

end (* finite_subfield_tower *)

context subfield_tower
begin

text \<open>
  Finite spanning is the representation-independent introduction rule for the finite-extension
  locale.  It is deliberately phrased using the existing span API, so callers need not manufacture a
  basis merely to establish finite-dimensionality.
\<close>
lemma finite_subfield_tower_of_finite_spanning:
  assumes finB: "finite B" and BL: "B \<subseteq> L" and span: "L \<subseteq> vs.span B"
  shows "finite_subfield_tower K L"
proof -
  obtain C where C: "C \<subseteq> B" and basisC: "vs.basis C"
    using subfield_tower_basis_exists_of_finite_spanning[OF finB BL span] by blast
  show ?thesis
  proof (rule finite_subfield_tower.intro)
    show "subfield_tower K L"
      by unfold_locales (rule base_subset)
    show "finite_subfield_tower_axioms K L"
      by (rule finite_subfield_tower_axioms.intro) (rule exI[of _ C], rule basisC)
  qed
qed

lemma finite_subfield_tower_iff_finite_spanning:
  "finite_subfield_tower K L \<longleftrightarrow>
     (\<exists>B. finite B \<and> B \<subseteq> L \<and> L \<subseteq> vs.span B)"
proof
  assume T: "finite_subfield_tower K L"
  interpret T: finite_subfield_tower K L by (rule T)
  obtain B where B: "vs.basis B" using T.finite_basis by blast
  have finB: "finite B" and BL: "B \<subseteq> L"
    using B by (auto simp: vs.basis_def)
  have mod_span: "vs.mod.spanning B"
    using vs.spanning_iff_mod_spanning[OF finB BL]
      vs.basis_spanning[OF B] by blast
  have "L \<subseteq> vs.span B"
  proof
    fix x assume xL: "x \<in> L"
    show "x \<in> vs.span B"
      using vs.mod.spanningD[OF mod_span xL] by (simp add: vs.span_def)
  qed
  then show "\<exists>B. finite B \<and> B \<subseteq> L \<and> L \<subseteq> vs.span B"
    using finB BL by blast
next
  assume "\<exists>B. finite B \<and> B \<subseteq> L \<and> L \<subseteq> vs.span B"
  then obtain B where "finite B" and "B \<subseteq> L" and "L \<subseteq> vs.span B" by blast
  then show "finite_subfield_tower K L"
    by (rule finite_subfield_tower_of_finite_spanning)
qed

end (* subfield_tower *)

subsection \<open>Finite intermediate extensions\<close>

text \<open>A subfield between the endpoints of a finite extension is finite-dimensional over the
  base.  It is a vector subspace of the ambient finite-dimensional extension, so the subspace basis
  theorem supplies a finite basis.\<close>
theorem finite_subfield_tower_intermediate_left:
  fixes F E K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K"
    and sfE: "Subfield E" and FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
  shows "finite_subfield_tower F E"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  interpret FE: subfield_tower F E
  proof (rule subfield_tower.intro)
    show "Subfield F" by (rule T.base.Subfield_axioms)
    show "Subfield E" by (rule sfE)
    show "subfield_tower_axioms F E" by unfold_locales (rule FE)
  qed
  have E_submodule: "T.vs.mod.submodule E"
  proof (rule T.vs.mod.submoduleI)
    show "E \<subseteq> K" by (rule EK)
    show "0 \<in> E" by (rule Subfield.zero_closed[OF sfE])
    show "\<And>x y. x \<in> E \<Longrightarrow> y \<in> E \<Longrightarrow> x + y \<in> E"
      by (rule Subfield.add_closed[OF sfE])
    show "\<And>c x. c \<in> F \<Longrightarrow> x \<in> E \<Longrightarrow> c * x \<in> E"
      using FE by (blast intro: Subfield.mult_closed[OF sfE])
  qed
  interpret S: vector_subspace F "(+)" "(*)" "0" "1" "(+)" "0" K "(*)" E
  proof (rule vector_subspace.intro)
    show "Vector_Space.Vector_Space F (+) (*) 0 1 (+) 0 K (*)"
      by (rule T.vs.Vector_Space_axioms)
    show "vector_subspace_axioms F (+) 0 K (*) E"
      by unfold_locales (rule E_submodule)
  qed
  obtain B where B: "T.vs.basis B" using T.finite_basis by blast
  obtain A where basis_FE: "FE.vs.basis A"
    using S.subspace_basis_exists[OF B] by blast
  show ?thesis
  proof (rule finite_subfield_tower.intro)
    show "subfield_tower F E" by (rule FE.subfield_tower_axioms)
    show "finite_subfield_tower_axioms F E"
      by unfold_locales (rule exI[of _ A], rule basis_FE)
  qed
qed

text \<open>The upper part of the same tower is finite-dimensional as well.  An ambient basis over
  the smaller base still spans after scalars are enlarged to the intermediate field.\<close>
theorem finite_subfield_tower_intermediate_right:
  fixes F E K :: "'a :: field set"
  assumes T: "finite_subfield_tower F K"
    and sfE: "Subfield E" and FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
  shows "finite_subfield_tower E K"
proof -
  interpret T: finite_subfield_tower F K by (rule T)
  interpret EK: subfield_tower E K
  proof (rule subfield_tower.intro)
    show "Subfield E" by (rule sfE)
    show "Subfield K" by (rule T.ext.Subfield_axioms)
    show "subfield_tower_axioms E K" by unfold_locales (rule EK)
  qed
  obtain B where B: "T.vs.basis B" using T.finite_basis by blast
  have finB: "finite B" and BK: "B \<subseteq> K"
    using B by (auto simp: T.vs.basis_def)
  have K_span: "K \<subseteq> EK.vs.span B"
  proof
    fix x assume xK: "x \<in> K"
    obtain c where c: "c \<in> B \<rightarrow>\<^sub>E F" "x = T.vs.lincomb c B"
      using T.vs.basis_spanning[OF B] xK unfolding T.vs.spanning_def by blast
    have cF: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> F" using c(1) by auto
    have cE: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> E" using cF FE by blast
    have xsum: "x = (\<Sum>v\<in>B. c v * v)"
      using c(2) T.vs_lincomb_eq_sum[OF finB BK cF] by simp
    have "(\<Sum>v\<in>B. c v * id v) \<in> EK.vs.span (id ` B)"
      by (rule EK.sum_scale_in_span[OF finB]) (use BK cE in auto)
    then show "x \<in> EK.vs.span B" using xsum by simp
  qed
  show ?thesis by (rule EK.finite_subfield_tower_of_finite_spanning[OF finB BK K_span])
qed

end
