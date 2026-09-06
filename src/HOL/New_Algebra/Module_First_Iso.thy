section \<open>The first isomorphism theorem for modules\<close>

theory Module_First_Iso
  imports Quotient_Module
begin

text \<open>Given a module homomorphism @{term "\<eta>: M \<rightarrow> M'"}, its kernel is a submodule of @{term M}, and
  the induced map on the quotient @{text "M/Ker \<eta>"} onto @{term "\<eta> ` M"} is a module isomorphism.

  The natural way to organise this development inside @{locale module_homomorphism} is to prove
  once and for all that the kernel gives rise to a @{locale submodule_in_module} instance, and
  then use the operations \<open>K.Qcarrier\<close>, \<open>K.Qclass\<close>, \<open>K.qadd\<close>, \<open>K.qscale\<close> supplied by that
  instance in the theorems below.  We do this via
  @{command interpretation}@{text " K: submodule_in_module ... Ker"} at the head of the
  @{command context} block, discharged by the lemma \<open>Ker_submodule_in_module\<close> below.\<close>

context module_homomorphism
begin

subsection \<open>The kernel-quotient and the induced map\<close>

text \<open>The kernel is a submodule (@{thm [source] Ker_submodule}), so the
  @{locale submodule_in_module} locale holds on it.  This lemma is the witness fed to the
  @{command interpretation} below.\<close>
lemma Ker_submodule_in_module:
  "submodule_in_module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>) Ker"
proof
  show "source.submodule Ker" by (rule Ker_submodule)
qed

text \<open>Install @{locale submodule_in_module} on the kernel with prefix @{text K}.  The theorems
  below then use @{text K.Qcarrier}, @{text K.Qclass}, @{text K.qadd}, @{text K.qscale}, and other
  facts derived from the locale (@{text K.Class_eq_iff_diff_in_N}, @{text K.qscale_Class},
  @{text K.quotient.Module_axioms}, @{text K.madd_sub.representant_exists},
  @{text K.madd_sub.Class_commutes_with_composition}).\<close>
interpretation K: submodule_in_module
  R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" Ker
  by (rule Ker_submodule_in_module)

text \<open>The induced map on cosets.  Made extensional on \<open>K.Qcarrier\<close> so that it fits the
  @{locale map} locale in the @{const module_homomorphism} obligation.\<close>
definition ind :: "'b set \<Rightarrow> 'c"
  where "ind = (\<lambda>X \<in> K.Qcarrier. THE y. \<exists>v \<in> M. X = K.Qclass v \<and> y = \<eta> v)"

lemma ind_Class:
  assumes v: "v \<in> M" shows "ind (K.Qclass v) = \<eta> v"
proof -
  have "(THE y. \<exists>u \<in> M. K.Qclass v = K.Qclass u \<and> y = \<eta> u) = \<eta> v"
  proof (rule the_equality)
    show "\<exists>u \<in> M. K.Qclass v = K.Qclass u \<and> \<eta> v = \<eta> u" using v by blast
  next
    fix y assume "\<exists>u \<in> M. K.Qclass v = K.Qclass u \<and> y = \<eta> u"
    then obtain u where u: "u \<in> M" "K.Qclass v = K.Qclass u" "y = \<eta> u" by blast
    have "v \<oplus> source.madd.inverse u \<in> Ker"
      using u(2) v u(1) by (subst K.Class_eq_iff_diff_in_N[symmetric]) simp_all
    then have "\<eta> (v \<oplus> source.madd.inverse u) = \<zero>\<^sub>2"
      using Ker_image by blast
    moreover have iuM: "source.madd.inverse u \<in> M" using u(1) by simp
    ultimately have "\<eta> v \<oplus>\<^sub>2 \<eta> (source.madd.inverse u) = \<zero>\<^sub>2"
      using v u(1) by (simp add: hom_add)
    then have eq: "\<eta> v \<oplus>\<^sub>2 target.madd.inverse (\<eta> u) = \<zero>\<^sub>2"
      using u(1) by (simp add: hom_neg)
    have "\<eta> u \<oplus>\<^sub>2 target.madd.inverse (\<eta> u) = \<zero>\<^sub>2"
      using hom_closed[OF u(1)] by (simp add: target.madd.invertible_right_inverse)
    with eq have "\<eta> v \<oplus>\<^sub>2 target.madd.inverse (\<eta> u) = \<eta> u \<oplus>\<^sub>2 target.madd.inverse (\<eta> u)"
      by simp
    then have "\<eta> v = \<eta> u"
      using hom_closed[OF v] hom_closed[OF u(1)] target.madd.invertible_right_cancel
      by (metis target.madd.invertible target.madd.invertible_inverse_closed)
    then show "y = \<eta> v" using u(3) by simp
  qed
  moreover have "K.Qclass v \<in> K.Qcarrier" using v by simp
  ultimately show ?thesis unfolding ind_def by simp
qed

lemma ind_closed:
  assumes "X \<in> K.Qcarrier" shows "ind X \<in> \<eta> ` M"
proof -
  from assms obtain v where "v \<in> M" "X = K.Qclass v"
    using K.madd_sub.representant_exists by auto
  then show ?thesis by (simp add: ind_Class)
qed


subsection \<open>The image \<open>\<eta> ` M\<close> is a submodule of the target\<close>

lemma image_abelian_group: "Abelian_Group (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2"
proof -
  have sub: "Subgroup (\<eta> ` M) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2"
  proof (rule target.madd.subgroupI)
    show "\<eta> ` M \<subseteq> M'" using hom_closed by auto
    show "\<zero>\<^sub>2 \<in> \<eta> ` M" using hom_zero source.mzero_closed by (metis image_eqI)
  next
    fix u v assume "u \<in> \<eta> ` M" "v \<in> \<eta> ` M"
    then obtain a b where ab: "a \<in> M" "b \<in> M" "u = \<eta> a" "v = \<eta> b" by auto
    then have "u \<oplus>\<^sub>2 v = \<eta> (a \<oplus> b)" by (simp add: hom_add)
    then show "u \<oplus>\<^sub>2 v \<in> \<eta> ` M" using ab by auto
  next
    fix u assume "u \<in> \<eta> ` M" then obtain a where a: "a \<in> M" "u = \<eta> a" by auto
    then have "u \<in> M'" using hom_closed by auto
    then show "target.madd.invertible u" by simp
    have "target.madd.inverse u = \<eta> (source.madd.inverse a)"
      using a by (simp add: hom_neg source.madd.invertible)
    then show "target.madd.inverse u \<in> \<eta> ` M" using a by auto
  qed
  interpret Sub: Subgroup "\<eta> ` M" M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" by (rule sub)
  show ?thesis
  proof (rule Abelian_Group.intro)
    show "Group (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2" by (rule Sub.sub.Group_axioms)
    show "commutative_monoid (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2"
      by unfold_locales (auto simp: target.madd.commutative)
  qed
qed

lemma image_module_axioms:
  "Module_axioms R (+) (\<cdot>) \<one> (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<eta> ` M) (\<odot>\<^sub>2)"
proof (rule Module_axioms.intro)
  show "Abelian_Group (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2" by (rule image_abelian_group)
next
  fix a v assume a: "a \<in> R" and v: "v \<in> \<eta> ` M"
  then obtain x where x: "x \<in> M" "v = \<eta> x" by auto
  have "a \<odot>\<^sub>2 v = \<eta> (a \<odot> x)" using a x by (simp add: hom_scale)
  then show "a \<odot>\<^sub>2 v \<in> \<eta> ` M" using a x by (auto intro: source.scale_closed)
next
  fix a u v assume a: "a \<in> R" and "u \<in> \<eta> ` M" and "v \<in> \<eta> ` M"
  then obtain x y where "x \<in> M" "y \<in> M" "u = \<eta> x" "v = \<eta> y" by auto
  with a show "a \<odot>\<^sub>2 (u \<oplus>\<^sub>2 v) = (a \<odot>\<^sub>2 u) \<oplus>\<^sub>2 (a \<odot>\<^sub>2 v)"
    by (simp add: target.scale_distrib_madd hom_closed)
next
  fix a b v assume a: "a \<in> R" and b: "b \<in> R" and v: "v \<in> \<eta> ` M"
  then obtain x where "x \<in> M" "v = \<eta> x" by auto
  with a b show "(a + b) \<odot>\<^sub>2 v = (a \<odot>\<^sub>2 v) \<oplus>\<^sub>2 (b \<odot>\<^sub>2 v)"
    by (simp add: target.scale_distrib_add hom_closed)
next
  fix a b v assume a: "a \<in> R" and b: "b \<in> R" and v: "v \<in> \<eta> ` M"
  then obtain x where "x \<in> M" "v = \<eta> x" by auto
  with a b show "(a \<cdot> b) \<odot>\<^sub>2 v = a \<odot>\<^sub>2 b \<odot>\<^sub>2 v"
    by (simp add: target.scale_scale hom_closed)
next
  fix v assume "v \<in> \<eta> ` M"
  then obtain x where "x \<in> M" "v = \<eta> x" by auto
  then show "\<one> \<odot>\<^sub>2 v = v" by (simp add: target.scale_one hom_closed)
qed

lemma image_is_module: "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<eta> ` M) (\<odot>\<^sub>2)"
  by (rule Module.intro[OF source.Ring_axioms image_module_axioms])


subsection \<open>The induced map is a module homomorphism, injective, surjective\<close>

text \<open>The quotient module on the kernel is a module (specialisation of the quotient's own
  \<open>Module_axioms\<close> to the kernel-as-submodule).\<close>
lemma quotient_is_module:
  "Module R (+) (\<cdot>) \<zero> \<one> K.qadd (K.Qclass \<zero>\<^sub>M) K.Qcarrier K.qscale"
  by (rule K.quotient.Module_axioms)

theorem ind_module_homomorphism:
  "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
     K.Qcarrier K.qadd (K.Qclass \<zero>\<^sub>M) K.qscale
     (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) ind"
proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
  show "Module R (+) (\<cdot>) \<zero> \<one> K.qadd (K.Qclass \<zero>\<^sub>M) K.Qcarrier K.qscale"
    by (rule quotient_is_module)
  show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<eta> ` M) (\<odot>\<^sub>2)"
    by (rule image_is_module)
  show "ind \<in> K.Qcarrier \<rightarrow>\<^sub>E \<eta> ` M"
    using ind_closed by (auto simp: ind_def PiE_iff extensional_def)
next
  fix U V assume "U \<in> K.Qcarrier" and "V \<in> K.Qcarrier"
  then obtain u v where uv: "u \<in> M" "v \<in> M"
    "U = K.Qclass u" "V = K.Qclass v"
    using K.madd_sub.representant_exists by (metis (mono_tags, lifting))
  have "ind (K.qadd U V) = ind (K.Qclass (u \<oplus> v))"
    using uv by (simp add: K.madd_sub.Class_commutes_with_composition)
  also have "\<dots> = \<eta> (u \<oplus> v)" using uv by (simp add: ind_Class)
  also have "\<dots> = \<eta> u \<oplus>\<^sub>2 \<eta> v" using uv by (simp add: hom_add)
  also have "\<dots> = (ind U) \<oplus>\<^sub>2 (ind V)" using uv by (simp add: ind_Class)
  finally show "ind (K.qadd U V) = (ind U) \<oplus>\<^sub>2 (ind V)" .
next
  fix a V assume a: "a \<in> R" and "V \<in> K.Qcarrier"
  then obtain v where v: "v \<in> M" "V = K.Qclass v"
    using K.madd_sub.representant_exists by (metis (mono_tags, lifting))
  have "ind (K.qscale a V) = ind (K.Qclass (a \<odot> v))"
    using a v by (simp add: K.qscale_Class)
  also have "\<dots> = \<eta> (a \<odot> v)" using a v by (simp add: ind_Class source.scale_closed)
  also have "\<dots> = a \<odot>\<^sub>2 \<eta> v" using a v by (simp add: hom_scale)
  also have "\<dots> = a \<odot>\<^sub>2 ind V" using v by (simp add: ind_Class)
  finally show "ind (K.qscale a V) = a \<odot>\<^sub>2 ind V" .
qed


theorem ind_inj: "inj_on ind K.Qcarrier"
proof (rule inj_onI)
  fix U V assume U: "U \<in> K.Qcarrier" and V: "V \<in> K.Qcarrier" and eq: "ind U = ind V"
  from U obtain u where u: "u \<in> M" "U = K.Qclass u"
    using K.madd_sub.representant_exists by (metis (mono_tags, lifting))
  from V obtain v where v: "v \<in> M" "V = K.Qclass v"
    using K.madd_sub.representant_exists by (metis (mono_tags, lifting))
  from eq u v have h: "\<eta> u = \<eta> v" by (simp add: ind_Class)
  have "\<eta> (u \<oplus> source.madd.inverse v) = \<eta> u \<oplus>\<^sub>2 \<eta> (source.madd.inverse v)"
    using u v by (simp add: hom_add)
  also have "\<dots> = \<eta> v \<oplus>\<^sub>2 target.madd.inverse (\<eta> v)" using u v h by (simp add: hom_neg)
  also have "\<dots> = \<zero>\<^sub>2"
    using hom_closed[OF v(1)] by (simp add: target.madd.invertible_right_inverse)
  finally have "\<eta> (u \<oplus> source.madd.inverse v) = \<zero>\<^sub>2" .
  moreover have "u \<oplus> source.madd.inverse v \<in> M" using u v by simp
  ultimately have "u \<oplus> source.madd.inverse v \<in> Ker" by (rule Ker_memI)
  then have "K.Qclass u = K.Qclass v"
    using u v by (simp add: K.Class_eq_iff_diff_in_N)
  then show "U = V" using u v by simp
qed


theorem ind_surj: "ind ` K.Qcarrier = \<eta> ` M"
proof
  show "ind ` K.Qcarrier \<subseteq> \<eta> ` M" using ind_closed by auto
  show "\<eta> ` M \<subseteq> ind ` K.Qcarrier"
  proof
    fix y assume "y \<in> \<eta> ` M"
    then obtain v where v: "v \<in> M" "y = \<eta> v" by auto
    then have "y = ind (K.Qclass v)" by (simp add: ind_Class)
    moreover have "K.Qclass v \<in> K.Qcarrier" using v by simp
    ultimately show "y \<in> ind ` K.Qcarrier" by auto
  qed
qed

text \<open>\<^emph>\<open>The first isomorphism theorem\<close>: the induced map @{term ind} is a bijective module
  homomorphism from @{text "M/Ker \<eta>"} onto @{term "\<eta> ` M"}.\<close>
theorem first_isomorphism:
  "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
     K.Qcarrier K.qadd (K.Qclass \<zero>\<^sub>M) K.qscale
     (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) ind
   \<and> bij_betw ind K.Qcarrier (\<eta> ` M)"
  using ind_module_homomorphism ind_inj ind_surj by (auto simp: bij_betw_def)

end (* module_homomorphism *)

end
