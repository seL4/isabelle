section \<open>Complementary submodules and projections\<close>

theory Module_Complements
  imports Module_Iso_Theorems
begin

text \<open>An idempotent module endomorphism is a projection onto its image.  The
  image and kernel therefore recover the two internal summands without any
  finite-dimensional assumption or choice of bases.\<close>
locale idempotent_module_endomorphism =
  module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
    M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
    M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" p
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70)
    and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
    and M and madd (infixl \<open>\<oplus>\<close> 65) and mzero (\<open>\<zero>\<^sub>M\<close>)
    and scale (infixr \<open>\<odot>\<close> 75) and p +
  assumes idempotent: "\<And>x. x \<in> M \<Longrightarrow> p (p x) = p x"
begin

theorem image_kernel_complementary:
  "p ` M \<inter> Ker = {\<zero>\<^sub>M}"
  "p ` M \<oplus>\<^sub>S Ker = M"
proof -
  have image_sub: "source.submodule (p ` M)"
    using image_submodule .
  show disjoint: "p ` M \<inter> Ker = {\<zero>\<^sub>M}"
  proof (rule set_eqI, rule iffI)
    fix x assume x: "x \<in> p ` M \<inter> Ker"
    then obtain y where y: "y \<in> M" "x = p y" by auto
    have "x = p x" using y idempotent[OF y(1)] by simp
    also have "... = \<zero>\<^sub>M" using x by (simp add: Ker_image)
    finally show "x \<in> {\<zero>\<^sub>M}" by simp
  next
    fix x assume x: "x \<in> {\<zero>\<^sub>M}"
    have xeq: "x = \<zero>\<^sub>M" using x by simp
    have zero_image: "\<zero>\<^sub>M \<in> p ` M"
    proof -
      have "p \<zero>\<^sub>M \<in> p ` M"
        by (rule imageI[OF source.mzero_closed])
      then show ?thesis using hom_zero by simp
    qed
    have zero_kernel: "\<zero>\<^sub>M \<in> Ker"
      by (rule source.submodule_zero[OF Ker_submodule])
    have image_x: "x \<in> p ` M" using xeq zero_image by simp
    have kernel_x: "x \<in> Ker" using xeq zero_kernel by simp
    show "x \<in> p ` M \<inter> Ker" by (rule IntI[OF image_x kernel_x])
  qed
  show "p ` M \<oplus>\<^sub>S Ker = M"
  proof
    have sum_sub: "source.submodule (p ` M \<oplus>\<^sub>S Ker)"
      by (rule source.submodule_sum_submodule[OF image_sub Ker_submodule])
    show "p ` M \<oplus>\<^sub>S Ker \<subseteq> M"
      by (rule source.submodule_subset[OF sum_sub])
    show "M \<subseteq> p ` M \<oplus>\<^sub>S Ker"
    proof
      fix x assume x: "x \<in> M"
      have px: "p x \<in> M" by (rule hom_closed[OF x])
      have remainder: "x \<oplus> source.madd.inverse (p x) \<in> Ker"
      proof (rule Ker_memI)
        show "p (x \<oplus> source.madd.inverse (p x)) = \<zero>\<^sub>M"
          using x px idempotent[OF x]
          by (simp add: hom_add hom_neg)
        show "x \<oplus> source.madd.inverse (p x) \<in> M" using x px by simp
      qed
      have image: "p x \<in> p ` M" by (rule imageI[OF x])
      have decomposition:
        "x = p x \<oplus> (x \<oplus> source.madd.inverse (p x))"
        using x px by (simp add: source.madd.ac)
      have "p x \<oplus> (x \<oplus> source.madd.inverse (p x))
          \<in> p ` M \<oplus>\<^sub>S Ker"
        by (rule source.submodule_sum_memI[OF image remainder])
      show "x \<in> p ` M \<oplus>\<^sub>S Ker"
        using decomposition \<open>p x \<oplus> (x \<oplus> source.madd.inverse (p x))
          \<in> p ` M \<oplus>\<^sub>S Ker\<close> by simp
    qed
  qed
qed

end

context Module
begin

text \<open>The projection onto @{term N} along @{term K} is obtained canonically from the quotient:
  first map an element of @{term M} to its class in @{text "M/K"}, then use the inverse of the
  restricted quotient isomorphism from @{term N}.  Both maps are restricted to their carriers, so
  the resulting projection follows the extensional-map convention of the module hierarchy.\<close>
definition complement_projection :: "'b set \<Rightarrow> 'b set \<Rightarrow> 'b \<Rightarrow> 'b"
  where "complement_projection N K =
    compose M
      (restrict (inv_into N (proj_res N K))
        (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K))
      (submodule_in_module.nat_proj (\<oplus>) \<zero>\<^sub>M M K)"

text \<open>The construction is a module homomorphism whenever the two submodules are complementary.
  This packages the quotient projection, the complement--quotient isomorphism, and its
  carrier-restricted inverse.\<close>
theorem complement_projection_hom:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
  shows "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
    M (\<oplus>) \<zero>\<^sub>M (\<odot>) N (\<oplus>) \<zero>\<^sub>M (\<odot>)
    (complement_projection N K)"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one>
      "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      K.Qcarrier K.qadd "K.Qclass \<zero>\<^sub>M" K.qscale "proj_res N K"
    by (rule proj_res_hom[OF N K])
  have bij: "bij_betw (proj_res N K) N K.Qcarrier"
    using complement_quotient_isomorphism[OF N K disjoint full] by blast
  have inverse_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      K.Qcarrier K.qadd (K.Qclass \<zero>\<^sub>M) K.qscale
      N (\<oplus>) \<zero>\<^sub>M (\<odot>)
      (restrict (inv_into N (proj_res N K)) K.Qcarrier)"
    by (rule P.inverse_module_homomorphism[OF bij])
  show ?thesis
    unfolding complement_projection_def
    by (rule K.nat_proj.compose_module_homomorphism[OF inverse_hom])
qed

text \<open>The projection fixes the chosen summand.\<close>
lemma complement_projection_apply_left:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
    and x: "x \<in> N"
  shows "complement_projection N K x = x"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one>
      "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      K.Qcarrier K.qadd "K.Qclass \<zero>\<^sub>M" K.qscale "proj_res N K"
    by (rule proj_res_hom[OF N K])
  have bij: "bij_betw (proj_res N K) N K.Qcarrier"
    using complement_quotient_isomorphism[OF N K disjoint full] by blast
  have xM: "x \<in> M" using x submodule_subset[OF N] by blast
  show ?thesis
    unfolding complement_projection_def compose_def
    using P.inverse_module_homomorphism_left[OF bij x] x xM by simp
qed

text \<open>The complementary summand is annihilated.\<close>
lemma complement_projection_apply_right:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
    and x: "x \<in> K"
  shows "complement_projection N K x = \<zero>\<^sub>M"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one>
      "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      K.Qcarrier K.qadd "K.Qclass \<zero>\<^sub>M" K.qscale "proj_res N K"
    by (rule proj_res_hom[OF N K])
  have bij: "bij_betw (proj_res N K) N K.Qcarrier"
    using complement_quotient_isomorphism[OF N K disjoint full] by blast
  interpret I: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      K.Qcarrier K.qadd "K.Qclass \<zero>\<^sub>M" K.qscale
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      "restrict (inv_into N (proj_res N K)) K.Qcarrier"
    by (rule P.inverse_module_homomorphism[OF bij])
  have xM: "x \<in> M" using x submodule_subset[OF K] by blast
  have xKer: "x \<in> K.nat_proj.Ker" using x K.nat_proj_Ker by simp
  have quotient_zero: "K.nat_proj x = K.Qclass \<zero>\<^sub>M"
    by (rule K.nat_proj.Ker_image[OF xKer])
  show ?thesis
    unfolding complement_projection_def compose_def
    using xM quotient_zero I.hom_zero by simp
qed

text \<open>On an explicitly decomposed element, the projection selects its left component.\<close>
lemma complement_projection_apply_sum:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
    and u: "u \<in> N" and v: "v \<in> K"
  shows "complement_projection N K (u \<oplus> v) = u"
proof -
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" "complement_projection N K"
    by (rule complement_projection_hom[OF N K disjoint full])
  have uM: "u \<in> M" using u submodule_subset[OF N] by blast
  have vM: "v \<in> M" using v submodule_subset[OF K] by blast
  have "complement_projection N K (u \<oplus> v) =
      complement_projection N K u \<oplus> complement_projection N K v"
    by (rule P.hom_add[OF uM vM])
  also have "... = u \<oplus> \<zero>\<^sub>M"
    using complement_projection_apply_left[OF N K disjoint full u]
      complement_projection_apply_right[OF N K disjoint full v]
    by simp
  also have "... = u" using uM by simp
  finally show ?thesis .
qed

text \<open>Every element of a full, disjoint submodule sum has exactly one ordered pair of
  components.  Pairing the witnesses makes the uniqueness quantifier directly usable by clients.\<close>
theorem complementary_decomposition_exists_unique:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
    and x: "x \<in> M"
  shows "\<exists>!uv. fst uv \<in> N \<and> snd uv \<in> K \<and> x = fst uv \<oplus> snd uv"
proof -
  have xsum: "x \<in> N \<oplus>\<^sub>S K" using x full by simp
  then obtain u v where u: "u \<in> N" and v: "v \<in> K" and xeq: "x = u \<oplus> v"
    by (rule submodule_sum_memE)
  show ?thesis
  proof (rule ex1I[of _ "(u, v)"])
    show "fst (u, v) \<in> N \<and> snd (u, v) \<in> K \<and> x = fst (u, v) \<oplus> snd (u, v)"
      using u v xeq by simp
  next
    fix uv assume uv: "fst uv \<in> N \<and> snd uv \<in> K \<and>
      x = fst uv \<oplus> snd uv"
    have components: "u = fst uv \<and> v = snd uv"
      by (rule submodule_sum_decomposition_unique[OF N K disjoint u v])
        (use uv xeq in auto)
    then show "uv = (u, v)" by (cases uv) auto
  qed
qed

text \<open>The image is precisely the summand onto which the map projects.\<close>
theorem complement_projection_image:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
  shows "complement_projection N K ` M = N"
proof -
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" "complement_projection N K"
    by (rule complement_projection_hom[OF N K disjoint full])
  show ?thesis
  proof
    show "complement_projection N K ` M \<subseteq> N" using P.hom_closed by blast
    show "N \<subseteq> complement_projection N K ` M"
    proof
      fix x assume x: "x \<in> N"
      have xM: "x \<in> M" using x submodule_subset[OF N] by blast
      have "complement_projection N K x = x"
        by (rule complement_projection_apply_left[OF N K disjoint full x])
      moreover have "complement_projection N K x \<in> complement_projection N K ` M"
        by (rule imageI[OF xM])
      ultimately show "x \<in> complement_projection N K ` M" by simp
    qed
  qed
qed

text \<open>The kernel is precisely the complementary summand.\<close>
theorem complement_projection_Ker:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
  shows "{x \<in> M. complement_projection N K x = \<zero>\<^sub>M} = K"
proof -
  have decompose: "\<And>x. x \<in> M \<Longrightarrow>
      \<exists>u \<in> N. \<exists>v \<in> K. x = u \<oplus> v"
  proof -
    fix x assume x: "x \<in> M"
    have "x \<in> N \<oplus>\<^sub>S K" using x full by simp
    then show "\<exists>u \<in> N. \<exists>v \<in> K. x = u \<oplus> v"
      by (rule submodule_sum_memE) blast
  qed
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" "complement_projection N K"
    by (rule complement_projection_hom[OF N K disjoint full])
  have kernel: "P.Ker = K"
  proof
    show "P.Ker \<subseteq> K"
    proof
      fix x assume xKer: "x \<in> P.Ker"
      then have xM: "x \<in> M" and px: "complement_projection N K x = \<zero>\<^sub>M"
        using P.Ker_mem P.Ker_image by auto
      obtain u v where u: "u \<in> N" and v: "v \<in> K" and xeq: "x = u \<oplus> v"
        using decompose[OF xM] by blast
      have "complement_projection N K x = u"
        using xeq complement_projection_apply_sum[OF N K disjoint full u v] by simp
      then have "u = \<zero>\<^sub>M" using px by simp
      moreover have vM: "v \<in> M" using v submodule_subset[OF K] by blast
      ultimately have "x = v" using xeq by (simp add: madd.left_unit)
      then show "x \<in> K" using v by simp
    qed
    show "K \<subseteq> P.Ker"
    proof
      fix x assume x: "x \<in> K"
      have xM: "x \<in> M" using x submodule_subset[OF K] by blast
      have "complement_projection N K x = \<zero>\<^sub>M"
        by (rule complement_projection_apply_right[OF N K disjoint full x])
      then show "x \<in> P.Ker" by (rule P.Ker_memI[OF _ xM])
    qed
  qed
  show ?thesis using kernel by (simp add: P.Ker_def)
qed

text \<open>Applying a complementary projection twice has no further effect.\<close>
lemma complement_projection_idempotent:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
    and x: "x \<in> M"
  shows "complement_projection N K (complement_projection N K x) =
    complement_projection N K x"
proof -
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" "complement_projection N K"
    by (rule complement_projection_hom[OF N K disjoint full])
  have "complement_projection N K x \<in> N" by (rule P.hom_closed[OF x])
  then show ?thesis by (rule complement_projection_apply_left[OF N K disjoint full])
qed

text \<open>The two complementary projections recover the original element.  This also cross-checks
  the orientation of the construction: the first map selects the @{term N}-component and the
  swapped map selects the @{term K}-component.\<close>
theorem complement_projections_sum:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
    and x: "x \<in> M"
  shows "complement_projection N K x \<oplus> complement_projection K N x = x"
proof -
  have disjoint': "K \<inter> N = {\<zero>\<^sub>M}" using disjoint by (simp add: Int_commute)
  have full': "K \<oplus>\<^sub>S N = M"
    using full submodule_sum_commute[OF K N] by simp
  have xsum: "x \<in> N \<oplus>\<^sub>S K" using x full by simp
  then obtain u v where u: "u \<in> N" and v: "v \<in> K" and xeq: "x = u \<oplus> v"
    by (rule submodule_sum_memE)
  have first: "complement_projection N K x = u"
    using xeq complement_projection_apply_sum[OF N K disjoint full u v] by simp
  have uM: "u \<in> M" using u submodule_subset[OF N] by blast
  have vM: "v \<in> M" using v submodule_subset[OF K] by blast
  have xeq': "x = v \<oplus> u" using xeq uM vM by (simp add: madd.commutative)
  have second: "complement_projection K N x = v"
    using xeq' complement_projection_apply_sum[OF K N disjoint' full' v u] by simp
  show ?thesis using first second xeq by simp
qed

end


end
