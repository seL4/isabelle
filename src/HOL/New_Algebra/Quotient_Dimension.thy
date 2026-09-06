section \<open>Dimension of quotient spaces\<close>

theory Quotient_Dimension
  imports Rank_Nullity Quotient_Module
begin

no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

text \<open>A quotient of a vector space by a subspace inherits the vector-space structure already
  constructed at the module level.  The natural projection is therefore a linear map.\<close>

locale vector_quotient = vector_subspace
begin

sublocale factor: submodule_in_module
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>)" "\<zero>\<^sub>V" V "(\<odot>)" W
proof
  show "mod.submodule W" by (rule W_submodule)
qed

lemma quotient_vector_space:
  "Vector_Space R (+) (\<cdot>) \<zero> \<one>
    factor.qadd (factor.Qclass \<zero>\<^sub>V) factor.Qcarrier factor.qscale"
proof (intro Vector_Space.intro Vector_Space_axioms.intro)
  show "Field R (+) (\<cdot>) \<zero> \<one>" by unfold_locales
  show "Abelian_Group factor.Qcarrier factor.qadd (factor.Qclass \<zero>\<^sub>V)"
    by (rule factor.quotient.madd_group)
  show "\<And>a X. \<lbrakk>a \<in> R; X \<in> factor.Qcarrier\<rbrakk> \<Longrightarrow>
      factor.qscale a X \<in> factor.Qcarrier"
    by (rule factor.quotient.scale_closed)
  show "\<And>a X Y. \<lbrakk>a \<in> R; X \<in> factor.Qcarrier; Y \<in> factor.Qcarrier\<rbrakk> \<Longrightarrow>
      factor.qscale a (factor.qadd X Y) = factor.qadd (factor.qscale a X) (factor.qscale a Y)"
    by (rule factor.quotient.scale_distrib_madd)
  show "\<And>a b X. \<lbrakk>a \<in> R; b \<in> R; X \<in> factor.Qcarrier\<rbrakk> \<Longrightarrow>
      factor.qscale (a + b) X = factor.qadd (factor.qscale a X) (factor.qscale b X)"
    by (rule factor.quotient.scale_distrib_add)
  show "\<And>a b X. \<lbrakk>a \<in> R; b \<in> R; X \<in> factor.Qcarrier\<rbrakk> \<Longrightarrow>
      factor.qscale (a \<cdot> b) X = factor.qscale a (factor.qscale b X)"
    by (rule factor.quotient.scale_scale)
  show "\<And>X. X \<in> factor.Qcarrier \<Longrightarrow> factor.qscale \<one> X = X"
    by (rule factor.quotient.scale_one)
qed

sublocale quotient: Vector_Space
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>"
  factor.qadd "factor.Qclass \<zero>\<^sub>V" factor.Qcarrier factor.qscale
  by (rule quotient_vector_space)

sublocale projection: linear_map
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>"
  V "(\<oplus>)" "\<zero>\<^sub>V" "(\<odot>)"
  factor.Qcarrier factor.qadd "factor.Qclass \<zero>\<^sub>V" factor.qscale factor.nat_proj
  by unfold_locales

text \<open>The dimension of a subspace plus the dimension of its quotient is the dimension of the
  ambient space.  This is rank--nullity for the natural quotient projection.\<close>

theorem quotient_dimension:
  assumes B: "basis B"
  shows "plus sub.dimension quotient.dimension = dimension"
  using projection.rank_nullity[OF B] factor.nat_proj_Ker factor.nat_proj_image by simp

lemma quotient_basis_exists:
  assumes B: "basis B"
  shows "\<exists>C. quotient.basis C"
proof -
  obtain A where A: "projection.kernel.sub.basis A"
    using projection.kernel.subspace_basis_exists[OF B] by blast
  have AKer: "A \<subseteq> factor.nat_proj.Ker"
    using A by (simp add: projection.kernel.sub.basis_def)
  have indA: "lin_indep A"
    using projection.kernel.sub.basis_lin_indep[OF A]
      projection.kernel.sub_lin_indep_iff[OF AKer] by simp
  obtain C where AC: "A \<subseteq> C" and C: "basis C"
    using basis_extension[OF indA B] by blast
  have "projection.image.sub.basis (factor.nat_proj ` (C \<setminus> A))"
    by (rule projection.image_basis_complement[OF A C AC])
  then have "quotient.basis (factor.nat_proj ` (C \<setminus> A))"
    using factor.nat_proj_image by simp
  then show ?thesis by blast
qed

end

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

end
