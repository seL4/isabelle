section \<open>Complements in finite-dimensional vector spaces\<close>

theory Finite_Dimensional_Splitting
  imports Quotient_Dimension Module_Iso_Theorems
begin

no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

context vector_subspace
begin

text \<open>Every subspace of a finite-dimensional vector space has a complementary subspace.
  Extend a basis of the subspace to an ambient basis and take the span of the added basis vectors.
  Independence gives the trivial intersection, while span minimality gives the full sum.\<close>
theorem complementary_subspace_exists:
  assumes B: "basis B"
  shows "\<exists>U. mod.submodule U \<and> W \<inter> U = {\<zero>\<^sub>V} \<and>
    mod.submodule_sum W U = V"
proof -
  obtain A where A: "sub.basis A" and AW: "A \<subseteq> W"
    using subspace_basis_exists[OF B] sub.basis_def by blast
  then obtain C where AC: "A \<subseteq> C" and C: "basis C"
    using B basis_extension sub.basis_lin_indep sub_lin_indep_iff by meson
  define D where "D = C \<setminus> A"
  define U where "U = span D"
  have CV: "C \<subseteq> V" using C by (simp add: basis_def)
  have DV: "D \<subseteq> V" using CV D_def by blast
  have U_submodule: "mod.submodule U"
    unfolding U_def by (rule mod.span_submodule[OF DV])

  have "sub.mod.spanning A"
    using sub.basis_module_basis[OF A] by (rule sub.mod.module_basis_spanning)
  then have W_span: "W = span A"
    using sub.mod.spanning_def sub_span_eq by force
  have "mod.lin_indep C"
    using basis_module_basis[OF C] by (rule mod.module_basis_lin_indep)
  then have trivial_intersection: "W \<inter> U = {\<zero>\<^sub>V}"
    using AC D_def U_def W_span mod.span_inter_eq_trivial by force
  have sum_submodule: "mod.submodule (mod.submodule_sum W U)"
    by (rule mod.submodule_sum_submodule[OF W_submodule U_submodule])
  have A_sum: "A \<subseteq> mod.submodule_sum W U"
    using AW mod.submodule_sum_incl_left[OF W_submodule U_submodule] by blast
  have D_U: "D \<subseteq> U"
    unfolding U_def by (rule mod.span_incl[OF DV])
  have D_sum: "D \<subseteq> mod.submodule_sum W U"
    using D_U mod.submodule_sum_incl_right[OF W_submodule U_submodule] by blast
  have C_sum: "C \<subseteq> mod.submodule_sum W U"
    using A_sum D_def D_sum by auto
  have span_subset_sum: "span C \<subseteq> mod.submodule_sum W U"
    by (rule mod.span_minimal[OF sum_submodule C_sum])
  have "span C = V"
    using C CV basis_spanning mod.spanningI mod.spanning_def spanning_span_all by force
  then have "mod.submodule_sum W U = V"
    using mod.submodule_def span_subset_sum sum_submodule by force
  then show ?thesis using U_submodule trivial_intersection by blast
qed

end

context vector_quotient
begin

text \<open>Consequently every quotient of a finite-dimensional vector space is represented by a
  complementary subspace of the ambient space.  The isomorphism is not merely existential: it is
  the natural quotient projection restricted to that complement.\<close>
theorem complementary_quotient_isomorphism_exists:
  assumes B: "basis B"
  shows "\<exists>U. mod.submodule U
      \<and> W \<inter> U = {\<zero>\<^sub>V}
      \<and> mod.submodule_sum W U = V
      \<and> module_homomorphism R (+) (\<cdot>) \<zero> \<one>
            U (\<oplus>) \<zero>\<^sub>V (\<odot>)
            factor.Qcarrier factor.qadd (factor.Qclass \<zero>\<^sub>V) factor.qscale
            (mod.proj_res U W)
      \<and> bij_betw (mod.proj_res U W) U factor.Qcarrier"
proof -
  obtain U where U: "mod.submodule U"
    and disjoint: "W \<inter> U = {\<zero>\<^sub>V}"
    and full: "mod.submodule_sum W U = V"
    using complementary_subspace_exists[OF B] by blast
  have "mod.submodule_sum U W = V"
    using full mod.submodule_sum_commute[OF U W_submodule] by simp
  then show ?thesis using U disjoint full
    using W_submodule mod.complement_quotient_isomorphism by blast
qed

end

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

end
