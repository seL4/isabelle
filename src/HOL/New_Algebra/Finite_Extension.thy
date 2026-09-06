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

end
