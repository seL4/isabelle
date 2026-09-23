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
  where "extension_degree \<equiv> vs.dimension"

lemma extension_degree_eq_dimension:
  "extension_degree = vs.dimension"
  by (simp add: extension_degree_def)

lemma extension_degree_eq_card_basis:
  assumes "vs.basis B"
  shows "extension_degree = card B"
  using vs.dimension_eq_any_field[OF assms]
  by (simp add: extension_degree_def)

lemma finite_basis_exists: "\<exists>B. vs.basis B"
  by (rule finite_basis)

text \<open>
  The degree is positive because the ambient field contains distinct zero and one.  This proof does
  not require the carrier of the extension to be finite: finite-dimensionality is exactly the basis
  premise of the locale.
\<close>
lemma extension_degree_pos: "extension_degree > 0"
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
    obtain c where c: "c \<in> {} \<rightarrow>\<^sub>E K" and one_eq: "1 = vs.lincomb c {}"
      using vs.basis_spanning[OF B, unfolded Bempty] ext.one_closed
      unfolding vs.spanning_def by blast
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
  by (simp add: assms extension_degree_eq_dimension finite_subfield_tower_cardinality)

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
  have fin_coords: "finite (B \<rightarrow>\<^sub>E K)"
    using basis finK unfolding vs.basis_def by (meson finite_PiE)
  have image: "(\<lambda>c. vs.lincomb c B) ` (B \<rightarrow>\<^sub>E K) = L"
    using basis by (simp add: vs.basis_def bij_betw_def)
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
  show ?thesis
  proof
    show "generate_field (K \<union> B) \<subseteq> L"
      by (rule generate_field_least[OF ext.Subfield_axioms]) (use base_subset BL in auto)
    show "L \<subseteq> generate_field (K \<union> B)"
    proof
      fix x assume xL: "x \<in> L"
      obtain c where c: "c \<in> B \<rightarrow>\<^sub>E K" "x = vs.lincomb c B"
        using vs.basis_spanning[OF basis] xL unfolding vs.spanning_def by blast
      have cK: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> K" using c(1) by auto
      have lincomb_sum: "vs.lincomb c B = (\<Sum>v\<in>B. c v * v)"
        by (rule vs_lincomb_eq_sum[OF finB BL cK])
      interpret G: Subfield "generate_field (K \<union> B)" by (rule subfield_generate_field)
      have sumG: "(\<Sum>v\<in>B. c v * v) \<in> generate_field (K \<union> B)"
        by (simp add: G.mult_closed G.sum_closed cK generate_field.generate_field_base)
      show "x \<in> generate_field (K \<union> B)"
        using c(2) lincomb_sum sumG by simp
    qed
  qed
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
    using basisC finite_subfield_tower_axioms.intro finite_subfield_tower_def subfield_tower_axioms
    by blast
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
  have "L \<subseteq> vs.span B"
    using B BL finB vs.basis_spanning vs.mod.spanning_def vs.spanning_iff_mod_spanning by blast
  then show "\<exists>B. finite B \<and> B \<subseteq> L \<and> L \<subseteq> vs.span B"
    using finB BL by blast
next
  assume "\<exists>B. finite B \<and> B \<subseteq> L \<and> L \<subseteq> vs.span B"
  then show "finite_subfield_tower K L"
    using finite_subfield_tower_of_finite_spanning by force
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
    by (simp add: FE T.base.Subfield_axioms sfE subfield_tower.intro subfield_tower_axioms.intro)
  have E_submodule: "T.vs.mod.submodule E"
    by (simp add: EK FE.vs.scale_closed T.vs.mod.submoduleI)
  interpret S: vector_subspace F "(+)" "(*)" "0" "1" "(+)" "0" K "(*)" E
    by (simp add: E_submodule T.vs.Vector_Space_axioms vector_subspace_axioms_def
        vector_subspace_def)
  obtain B where B: "T.vs.basis B" using T.finite_basis by blast
  obtain A where basis_FE: "FE.vs.basis A"
    using S.subspace_basis_exists[OF B] by blast
  show ?thesis
    unfolding finite_subfield_tower_def
    using FE.subfield_tower_axioms basis_FE finite_subfield_tower_axioms.intro 
    by blast
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
    using EK T.ext.Subfield_axioms sfE subfield_tower.intro subfield_tower_axioms_def by blast
  obtain B where B: "T.vs.basis B" using T.finite_basis by blast
  have finB: "finite B" and BK: "B \<subseteq> K"
    using B by (auto simp: T.vs.basis_def)
  have K_span: "K \<subseteq> EK.vs.span B"
  proof
    fix x assume xK: "x \<in> K"
    obtain c where c: "c \<in> B \<rightarrow>\<^sub>E F" "x = T.vs.lincomb c B"
      using T.vs.basis_spanning[OF B] xK unfolding T.vs.spanning_def by blast
    have xsum: "x = (\<Sum>v\<in>B. c v * v)"
      using c(2) T.vs_lincomb_eq_sum[OF finB BK] c by auto
    have "(\<Sum>v\<in>B. c v * id v) \<in> EK.vs.span (id ` B)"
      using BK EK.sum_scale_in_span[of B id c] c FE by fastforce
    then show "x \<in> EK.vs.span B" using xsum by simp
  qed
  show ?thesis by (rule EK.finite_subfield_tower_of_finite_spanning[OF finB BK K_span])
qed

end
