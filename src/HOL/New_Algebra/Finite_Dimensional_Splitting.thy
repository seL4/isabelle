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
  obtain A where A: "sub.basis A"
    using subspace_basis_exists[OF B] by blast
  have AW: "A \<subseteq> W" using A by (simp add: sub.basis_def)
  have ambient_independent: "lin_indep A"
    using sub.basis_lin_indep[OF A] sub_lin_indep_iff[OF AW] by simp
  obtain C where AC: "A \<subseteq> C" and C: "basis C"
    using basis_extension[OF ambient_independent B] by blast

  define D where "D = C \<setminus> A"
  define U where "U = span D"
  have C_split: "C = A \<union> D" using AC by (auto simp: D_def)
  have CV: "C \<subseteq> V" using C by (simp add: basis_def)
  have DC: "D \<subseteq> C" by (simp add: D_def)
  have DV: "D \<subseteq> V" using DC CV by blast
  have U_submodule: "mod.submodule U"
    unfolding U_def by (rule mod.span_submodule[OF DV])

  have W_span: "W = span A"
  proof -
    have "sub.mod.spanning A"
      using sub.basis_module_basis[OF A] by (rule sub.mod.module_basis_spanning)
    then have "sub.span A = W" by (simp add: sub.mod.spanning_def)
    moreover have "sub.span A = span A" by (rule sub_span_eq[OF AW])
    ultimately show ?thesis by simp
  qed

  have trivial_intersection: "W \<inter> U = {\<zero>\<^sub>V}"
  proof -
    have C_independent: "mod.lin_indep C"
      using basis_module_basis[OF C] by (rule mod.module_basis_lin_indep)
    have "span A \<inter> span D = {\<zero>\<^sub>V}"
      by (rule mod.span_inter_eq_trivial
          [OF C_independent AC DC]) (simp add: D_def)
    then show ?thesis by (simp add: W_span U_def)
  qed

  have sum_submodule: "mod.submodule (mod.submodule_sum W U)"
    by (rule mod.submodule_sum_submodule[OF W_submodule U_submodule])
  have A_sum: "A \<subseteq> mod.submodule_sum W U"
    using AW mod.submodule_sum_incl_left[OF W_submodule U_submodule] by blast
  have D_U: "D \<subseteq> U"
    unfolding U_def by (rule mod.span_incl[OF DV])
  have D_sum: "D \<subseteq> mod.submodule_sum W U"
    using D_U mod.submodule_sum_incl_right[OF W_submodule U_submodule] by blast
  have C_sum: "C \<subseteq> mod.submodule_sum W U"
    using C_split A_sum D_sum by blast
  have span_subset_sum: "span C \<subseteq> mod.submodule_sum W U"
    by (rule mod.span_minimal[OF sum_submodule C_sum])
  have C_span: "span C = V"
  proof -
    have C_module_basis: "mod.module_basis C" by (rule basis_module_basis[OF C])
    have "mod.spanning C" by (rule mod.module_basis_spanning[OF C_module_basis])
    then show ?thesis by (simp add: mod.spanning_def)
  qed
  have full_sum: "mod.submodule_sum W U = V"
  proof
    show "mod.submodule_sum W U \<subseteq> V"
      by (rule mod.submodule_subset[OF sum_submodule])
    show "V \<subseteq> mod.submodule_sum W U" using C_span span_subset_sum by simp
  qed

  show ?thesis using U_submodule trivial_intersection full_sum by blast
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
  have disjoint': "U \<inter> W = {\<zero>\<^sub>V}"
    using disjoint by (simp add: Int_commute)
  have full': "mod.submodule_sum U W = V"
    using full mod.submodule_sum_commute[OF U W_submodule] by simp
  have iso: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
          U (\<oplus>) \<zero>\<^sub>V (\<odot>)
          factor.Qcarrier factor.qadd (factor.Qclass \<zero>\<^sub>V) factor.qscale
          (mod.proj_res U W)
      \<and> bij_betw (mod.proj_res U W) U factor.Qcarrier"
    by (rule mod.complement_quotient_isomorphism[OF U W_submodule disjoint' full'])
  show ?thesis using U disjoint full iso by blast
qed

end

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

end
