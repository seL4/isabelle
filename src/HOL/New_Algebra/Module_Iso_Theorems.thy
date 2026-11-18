section \<open>Isomorphism Theorems for Modules\<close>

theory Module_Iso_Theorems
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

subsection \<open>The second and third isomorphism theorems\<close>

text \<open>Building on the first isomorphism theorem above, we derive
  the third: given submodules \<open>K \<subseteq> N \<subseteq> M\<close>, the natural map \<open>v + K \<mapsto> v + N\<close> is a surjective
  module homomorphism from @{text "M/K"} onto @{text "M/N"} with kernel @{text "N/K"}; by the first
  iso, @{text "(M/K) / (N/K) \<cong> M/N"}.

  \<^emph>\<open>Note on the two @{command interpret}s.\<close>  Each theorem below interprets
  @{locale submodule_in_module} twice inside its own proof, once for @{term K} and once for
  @{term N}.  This is cheap and needs no refactoring.  A previous version of this note asserted
  that the alternative --- two @{command interpretation}s at the head of the enclosing
  @{command context} @{locale Module} block --- triggers a non-terminating locale roundup.  That
  claim was never soundly established (it shares an origin with the contention misdiagnosis
  above) and should be re-measured before being repeated or acted upon.\<close>

context Module
begin

text \<open>The natural map \<open>v + K \<mapsto> v + N\<close> from @{text "M/K"} to @{text "M/N"}.  Made extensional on
  \<open>M/K\<close> by construction so that the @{term map} obligation of @{locale module_homomorphism} is
  directly discharged.\<close>
definition proj_KN :: "'b set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> 'b set"
  where "proj_KN K N =
    (\<lambda>A \<in> submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K.
       THE B. \<exists>v \<in> M. A = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K v
                    \<and> B = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M N v)"

text \<open>Well-definedness of the projection: two representatives in the same \<open>K\<close>-coset lie in the same
  \<open>N\<close>-coset, because @{term "K \<subseteq> N"}.  This is the workhorse fact for everything below, so we prove
  it once here rather than inside each theorem.\<close>
lemma proj_KN_Class:
  assumes N_sub: "submodule N" and K_sub: "submodule K" and K_in_N: "K \<subseteq> N" and v: "v \<in> M"
  shows "proj_KN K N (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K v)
       = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M N v"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K_sub by unfold_locales
  interpret N: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" N
    using N_sub by unfold_locales
  have "(THE B. \<exists>u \<in> M. K.Qclass v = K.Qclass u \<and> B = N.Qclass u) = N.Qclass v"
  proof (rule the_equality)
    show "\<exists>u \<in> M. K.Qclass v = K.Qclass u \<and> N.Qclass v = N.Qclass u" using v by blast
  next
    fix B assume "\<exists>u \<in> M. K.Qclass v = K.Qclass u \<and> B = N.Qclass u"
    then obtain u where u: "u \<in> M" "K.Qclass v = K.Qclass u" "B = N.Qclass u" by blast
    from u(2) v u(1) have "v \<oplus> madd.inverse u \<in> K"
      by (simp add: K.Class_eq_iff_diff_in_N)
    with K_in_N have "v \<oplus> madd.inverse u \<in> N" by blast
    then have "N.Qclass v = N.Qclass u" using v u(1) by (simp add: N.Class_eq_iff_diff_in_N)
    with u(3) show "B = N.Qclass v" by simp
  qed
  moreover have "K.Qclass v \<in> K.Qcarrier" using v by simp
  ultimately show ?thesis unfolding proj_KN_def by simp
qed

text \<open>The main theorem: for submodules @{term K}, @{term N} of @{term M} with @{term "K \<subseteq> N"},
  the map @{term "proj_KN K N"} is a surjective module homomorphism from @{text "M/K"} onto
  @{text "M/N"} whose kernel is @{text "K.Qclass ` N"} (which is @{text "N/K"} viewed inside
  @{text "M/K"}).\<close>
theorem third_isomorphism_setup:
  assumes N_sub: "submodule N"
    and K_sub: "submodule K"
    and K_in_N: "K \<subseteq> N"
  shows "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
          (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
          (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
          (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
          (submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) K)
          (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M N)
          (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M N)
          (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M N \<zero>\<^sub>M)
          (submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) N)
          (proj_KN K N)"
        (is "module_homomorphism _ _ _ _ _ ?QK ?qaddK ?zK ?qscaleK ?QN ?qaddN ?zN ?qscaleN _")
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K_sub by unfold_locales
  interpret N: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" N
    using N_sub by unfold_locales

  note proj_Class = proj_KN_Class[OF N_sub K_sub K_in_N]

  have proj_closed: "proj_KN K N \<in> K.Qcarrier \<rightarrow>\<^sub>E N.Qcarrier"
  proof (rule PiE_I)
    fix A assume "A \<in> K.Qcarrier"
    then obtain v where v: "v \<in> M" "A = K.Qclass v" using K.madd_sub.representant_exists by auto
    then have "proj_KN K N A = N.Qclass v" using proj_Class by simp
    moreover have "N.Qclass v \<in> N.Qcarrier" using v by simp
    ultimately show "proj_KN K N A \<in> N.Qcarrier" by simp
  qed (auto simp: proj_KN_def)

  show ?thesis
  proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
    show "Module R (+) (\<cdot>) \<zero> \<one> ?qaddK ?zK ?QK ?qscaleK" by (rule K.quotient.Module_axioms)
    show "Module R (+) (\<cdot>) \<zero> \<one> ?qaddN ?zN ?QN ?qscaleN" by (rule N.quotient.Module_axioms)
    show "proj_KN K N \<in> ?QK \<rightarrow>\<^sub>E ?QN" by (rule proj_closed)
  next
    fix A B assume "A \<in> ?QK" and "B \<in> ?QK"
    then obtain a b where ab: "a \<in> M" "b \<in> M" "A = K.Qclass a" "B = K.Qclass b"
      using K.madd_sub.representant_exists by (metis (mono_tags, lifting))
    have "proj_KN K N (K.qadd A B) = proj_KN K N (K.Qclass (a \<oplus> b))"
      using ab by (simp add: K.madd_sub.Class_commutes_with_composition)
    also have "\<dots> = N.Qclass (a \<oplus> b)" using ab by (simp add: proj_Class)
    also have "\<dots> = N.qadd (N.Qclass a) (N.Qclass b)"
      using ab by (simp add: N.madd_sub.Class_commutes_with_composition)
    also have "\<dots> = N.qadd (proj_KN K N A) (proj_KN K N B)" using ab by (simp add: proj_Class)
    finally show "proj_KN K N (K.qadd A B) = N.qadd (proj_KN K N A) (proj_KN K N B)" .
  next
    fix a A assume a: "a \<in> R" and "A \<in> ?QK"
    then obtain v where v: "v \<in> M" "A = K.Qclass v" using K.madd_sub.representant_exists
      by (metis (mono_tags, lifting))
    have "proj_KN K N (K.qscale a A) = proj_KN K N (K.Qclass (a \<odot> v))"
      using a v by (simp add: K.qscale_Class)
    also have "\<dots> = N.Qclass (a \<odot> v)" using a v by (simp add: proj_Class scale_closed)
    also have "\<dots> = N.qscale a (N.Qclass v)" using a v by (simp add: N.qscale_Class)
    also have "\<dots> = N.qscale a (proj_KN K N A)" using v by (simp add: proj_Class)
    finally show "proj_KN K N (K.qscale a A) = N.qscale a (proj_KN K N A)" .
  qed
qed

theorem third_isomorphism_surj:
  assumes N_sub: "submodule N"
    and K_sub: "submodule K"
    and K_in_N: "K \<subseteq> N"
  shows "proj_KN K N ` (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
       = submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M N"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K_sub by unfold_locales
  interpret N: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" N
    using N_sub by unfold_locales
  note proj_Class = proj_KN_Class[OF N_sub K_sub K_in_N]
  show ?thesis
  proof
    show "proj_KN K N ` K.Qcarrier \<subseteq> N.Qcarrier"
    proof
      fix Y assume "Y \<in> proj_KN K N ` K.Qcarrier"
      then obtain A where A: "A \<in> K.Qcarrier" "Y = proj_KN K N A" by auto
      from A(1) obtain v where v: "v \<in> M" "A = K.Qclass v" using K.madd_sub.representant_exists by auto
      with A(2) proj_Class[OF v(1)] have "Y = N.Qclass v" by simp
      then show "Y \<in> N.Qcarrier" using v(1) by simp
    qed
    show "N.Qcarrier \<subseteq> proj_KN K N ` K.Qcarrier"
    proof
      fix Y assume "Y \<in> N.Qcarrier"
      then obtain v where v: "v \<in> M" "Y = N.Qclass v" using N.madd_sub.representant_exists by auto
      then have "Y = proj_KN K N (K.Qclass v)" using proj_Class by simp
      moreover have "K.Qclass v \<in> K.Qcarrier" using v(1) by simp
      ultimately show "Y \<in> proj_KN K N ` K.Qcarrier" by auto
    qed
  qed
qed


subsection \<open>The kernel of the projection is \<open>N/K\<close>\<close>

text \<open>The kernel of @{term "proj_KN K N"} consists of exactly those \<open>K\<close>-cosets whose representatives
  lie in @{term N} --- that is, of @{text "N/K"} viewed as a subset of @{text "M/K"}.  Note the
  kernel is computed with respect to the zero of @{text "M/N"}, namely @{text "N.Qclass \<zero>\<^sub>M"}.\<close>
theorem phi_Ker:
  assumes N_sub: "submodule N"
    and K_sub: "submodule K"
    and K_in_N: "K \<subseteq> N"
  shows "{A \<in> submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K.
            proj_KN K N A = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M N \<zero>\<^sub>M}
       = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` N"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K_sub by unfold_locales
  interpret N: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" N
    using N_sub by unfold_locales
  note proj_Class = proj_KN_Class[OF N_sub K_sub K_in_N]
  have N_in_M: "N \<subseteq> M" using submodule_subset[OF N_sub] .
  show ?thesis
  proof
    show "{A \<in> K.Qcarrier. proj_KN K N A = N.Qclass \<zero>\<^sub>M} \<subseteq> K.Qclass ` N"
    proof
      fix A assume A: "A \<in> {A \<in> K.Qcarrier. proj_KN K N A = N.Qclass \<zero>\<^sub>M}"
      then obtain v where v: "v \<in> M" "A = K.Qclass v"
        using K.madd_sub.representant_exists by auto
      from A have "proj_KN K N A = N.Qclass \<zero>\<^sub>M" by simp
      with v proj_Class have "N.Qclass v = N.Qclass \<zero>\<^sub>M" by simp
      \<comment> \<open>A coset equals the zero coset exactly when its representative lies in the submodule ---
        this is @{thm [source] submodule_in_module.Class_eq_iff_diff_in_N} with @{term "\<zero>\<^sub>M"},
        whose inverse is itself.\<close>
      then have "v \<oplus> madd.inverse \<zero>\<^sub>M \<in> N"
        using v(1) by (simp add: N.Class_eq_iff_diff_in_N)
      then have "v \<in> N" using v(1) by (simp add: madd.inverse_unit)
      with v(2) show "A \<in> K.Qclass ` N" by blast
    qed
    show "K.Qclass ` N \<subseteq> {A \<in> K.Qcarrier. proj_KN K N A = N.Qclass \<zero>\<^sub>M}"
    proof
      fix A assume "A \<in> K.Qclass ` N"
      then obtain v where v: "v \<in> N" "A = K.Qclass v" by blast
      then have vM: "v \<in> M" using N_in_M by blast
      have "A \<in> K.Qcarrier" using v(2) vM by simp
      moreover have "proj_KN K N A = N.Qclass \<zero>\<^sub>M"
      proof -
        have "v \<oplus> madd.inverse \<zero>\<^sub>M \<in> N" using v(1) vM by (simp add: madd.inverse_unit)
        then have "N.Qclass v = N.Qclass \<zero>\<^sub>M" using vM by (simp add: N.Class_eq_iff_diff_in_N)
        with v(2) vM proj_Class show ?thesis by simp
      qed
      ultimately show "A \<in> {A \<in> K.Qcarrier. proj_KN K N A = N.Qclass \<zero>\<^sub>M}" by simp
    qed
  qed
qed


subsection \<open>The third isomorphism theorem\<close>

text \<open>Assembling the pieces: @{term "proj_KN K N"} is a module homomorphism
  (@{thm [source] third_isomorphism_setup}) from @{text "M/K"} onto @{text "M/N"}
  (@{thm [source] third_isomorphism_surj}) with kernel @{text "N/K"} (@{thm [source] phi_Ker}).
  Applying the first isomorphism theorem to it yields
  @{text "(M/K)/(N/K) \<cong> M/N"}.

  We state the conclusion as the \<^emph>\<open>existence\<close> of an isomorphism rather than by naming the induced
  map explicitly.  Naming it would mean writing out @{const module_homomorphism.ind} applied to the
  iterated-quotient operations, which is a long and fragile parameter list; existence is the
  standard textbook phrasing and is what consumers actually use.\<close>
theorem third_isomorphism:
  assumes N_sub: "submodule N"
    and K_sub: "submodule K"
    and K_in_N: "K \<subseteq> N"
  shows "\<exists>\<phi>. module_homomorphism R (+) (\<cdot>) \<zero> \<one>
                (submodule_in_module.Qcarrier
                   (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
                   (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` N))
                (submodule_in_module.qadd
                   (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
                   (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` N))
                (submodule_in_module.Qclass
                   (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
                   (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` N)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M))
                (submodule_in_module.qscale
                   (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
                   (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` N))
                (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M N)
                (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M N)
                (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M N \<zero>\<^sub>M)
                (submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) N)
                \<phi>
           \<and> bij_betw \<phi>
                (submodule_in_module.Qcarrier
                   (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
                   (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
                   (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` N))
                (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M N)"
proof -
  \<comment> \<open>Interpret the projection as a module homomorphism; its own first isomorphism theorem then
    supplies the induced map, once we rewrite its kernel to \<open>N/K\<close> and its image to \<open>M/N\<close>.\<close>
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      "submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K"
      "submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K"
      "submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M"
      "submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) K"
      "submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M N"
      "submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M N"
      "submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M N \<zero>\<^sub>M"
      "submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) N"
      "proj_KN K N"
    by (rule third_isomorphism_setup[OF N_sub K_sub K_in_N])
  have Ker_eq: "P.Ker = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` N"
    unfolding P.Ker_def using phi_Ker[OF N_sub K_sub K_in_N] by simp
  have image_eq: "proj_KN K N ` submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K
                = submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M N"
    by (rule third_isomorphism_surj[OF N_sub K_sub K_in_N])
  show ?thesis
    using P.first_isomorphism unfolding Ker_eq image_eq by blast
qed


subsection \<open>The second isomorphism theorem\<close>

text \<open>For submodules @{term N} and @{term K}, the second isomorphism theorem states
  @{text "(N \<oplus>\<^sub>S K)/K \<cong> N/(N \<inter> K)"}.

  The proof restricts the natural projection @{text "M \<rightarrow> M/K"} to @{term N}.  A submodule is itself
  a module, so the restriction is a module homomorphism from @{term N} to @{text "M/K"}; its image is
  @{text "(N \<oplus>\<^sub>S K)/K"} and its kernel is @{term "N \<inter> K"}.  The first isomorphism theorem applied to
  it then gives the result.

  As with the third isomorphism theorem, the conclusion is stated as the \<^emph>\<open>existence\<close> of an
  isomorphism rather than by naming the induced map, whose argument list would otherwise have to be
  written out in full.\<close>

text \<open>A submodule, viewed as a module in its own right.\<close>
lemma submodule_is_module:
  assumes N: "submodule N" shows "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M N (\<odot>)"
proof (rule Module.intro[OF Ring_axioms], rule Module_axioms.intro)
  show "Abelian_Group N (\<oplus>) \<zero>\<^sub>M"
  proof (rule Abelian_Group.intro)
    interpret S: Subgroup N M "(\<oplus>)" "\<zero>\<^sub>M"
    proof (rule madd.subgroupI)
      show "N \<subseteq> M" using submodule_subset[OF N] .
      show "\<zero>\<^sub>M \<in> N" using submodule_zero[OF N] .
      show "\<And>g h. \<lbrakk> g \<in> N; h \<in> N \<rbrakk> \<Longrightarrow> g \<oplus> h \<in> N" using submodule_add[OF N] by blast
      show "\<And>g. g \<in> N \<Longrightarrow> madd.invertible g"
        using submodule_subset[OF N] by auto
      show "\<And>g. g \<in> N \<Longrightarrow> madd.inverse g \<in> N" using submodule_neg[OF N] by blast
    qed
    show "Group N (\<oplus>) \<zero>\<^sub>M" by (rule S.sub.Group_axioms)
    show "commutative_monoid N (\<oplus>) \<zero>\<^sub>M"
      using submodule_subset[OF N] by unfold_locales (auto simp: madd.commutative)
  qed
next
  show "\<And>a v. \<lbrakk> a \<in> R; v \<in> N \<rbrakk> \<Longrightarrow> a \<odot> v \<in> N" using submodule_scale[OF N] by blast
next
  fix a u v assume "a \<in> R" "u \<in> N" "v \<in> N"
  then show "a \<odot> (u \<oplus> v) = (a \<odot> u) \<oplus> (a \<odot> v)"
    using submodule_subset[OF N] by (auto intro: scale_distrib_madd)
next
  fix a b v assume "a \<in> R" "b \<in> R" "v \<in> N"
  then show "(a + b) \<odot> v = (a \<odot> v) \<oplus> (b \<odot> v)"
    using submodule_subset[OF N] by (auto intro: scale_distrib_add)
next
  fix a b v assume "a \<in> R" "b \<in> R" "v \<in> N"
  then show "(a \<cdot> b) \<odot> v = a \<odot> (b \<odot> v)"
    using submodule_subset[OF N] by (auto intro: scale_scale)
next
  fix v assume "v \<in> N"
  then show "\<one> \<odot> v = v" using submodule_subset[OF N] by (auto intro: scale_one)
qed

text \<open>The natural projection @{text "M \<rightarrow> M/K"} restricted to @{term N}.\<close>
definition proj_res :: "'b set \<Rightarrow> 'b set \<Rightarrow> 'b \<Rightarrow> 'b set"
  where "proj_res N K = (\<lambda>v \<in> N. submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K v)"

lemma proj_res_apply [simp]:
  "v \<in> N \<Longrightarrow> proj_res N K v = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K v"
  unfolding proj_res_def by simp

text \<open>The restricted projection is a module homomorphism from @{term N} to @{text "M/K"}.\<close>
lemma proj_res_hom:
  assumes N: "submodule N" and K: "submodule K"
  shows "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
           N (\<oplus>) \<zero>\<^sub>M (\<odot>)
           (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
           (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
           (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
           (submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) K)
           (proj_res N K)"
proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  have NM: "N \<subseteq> M" using submodule_subset[OF N] .
  show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M N (\<odot>)" by (rule submodule_is_module[OF N])
  show "Module R (+) (\<cdot>) \<zero> \<one> K.qadd (K.Qclass \<zero>\<^sub>M) K.Qcarrier K.qscale"
    by (rule K.quotient.Module_axioms)
  show "proj_res N K \<in> N \<rightarrow>\<^sub>E K.Qcarrier"
    unfolding proj_res_def using NM by (rule_tac PiE_I) (auto simp: extensional_def)
next
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  fix u v assume uv: "u \<in> N" "v \<in> N"
  then have uvM: "u \<in> M" "v \<in> M" using submodule_subset[OF N] by auto
  have "u \<oplus> v \<in> N" using submodule_add[OF N uv(1) uv(2)] .
  then show "proj_res N K (u \<oplus> v) = K.qadd (proj_res N K u) (proj_res N K v)"
    using uv uvM by (simp add: K.madd_sub.Class_commutes_with_composition)
next
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  fix a v assume av: "a \<in> R" "v \<in> N"
  then have vM: "v \<in> M" using submodule_subset[OF N] by blast
  have "a \<odot> v \<in> N" using submodule_scale[OF N av(1) av(2)] .
  then show "proj_res N K (a \<odot> v) = K.qscale a (proj_res N K v)"
    using av vM by (simp add: K.qscale_Class)
qed

text \<open>Its kernel is @{term "N \<inter> K"}: a coset @{text "v + K"} with @{term "v \<in> N"} is zero exactly
  when @{term "v \<in> K"}.\<close>
lemma proj_res_Ker:
  assumes N: "submodule N" and K: "submodule K"
  shows "{v \<in> N. proj_res N K v = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M} = N \<inter> K"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  have NM: "N \<subseteq> M" using submodule_subset[OF N] .
  show ?thesis
  proof
    show "{v \<in> N. proj_res N K v = K.Qclass \<zero>\<^sub>M} \<subseteq> N \<inter> K"
    proof
      fix v assume v: "v \<in> {v \<in> N. proj_res N K v = K.Qclass \<zero>\<^sub>M}"
      \<comment> \<open>Extract the two conjuncts explicitly; \<open>auto\<close> here also unfolds @{const proj_res} and
        times out.\<close>
      from v have vN: "v \<in> N" by blast
      from v have "proj_res N K v = K.Qclass \<zero>\<^sub>M" by blast
      then have eq: "K.Qclass v = K.Qclass \<zero>\<^sub>M" using vN by simp
      from vN have vM: "v \<in> M" using NM by blast
      have "v \<oplus> madd.inverse \<zero>\<^sub>M \<in> K"
        by (rule K.Class_eq_iff_diff_in_N[OF vM mzero_closed, THEN iffD1, OF eq])
      then have "v \<in> K" using vM by (simp add: madd.inverse_unit)
      with vN show "v \<in> N \<inter> K" by blast
    qed
    show "N \<inter> K \<subseteq> {v \<in> N. proj_res N K v = K.Qclass \<zero>\<^sub>M}"
    proof
      fix v assume v: "v \<in> N \<inter> K"
      then have vN: "v \<in> N" and vK: "v \<in> K" by auto
      from vN have vM: "v \<in> M" using NM by blast
      have "v \<oplus> madd.inverse \<zero>\<^sub>M \<in> K" using vK vM by (simp add: madd.inverse_unit)
      then have "K.Qclass v = K.Qclass \<zero>\<^sub>M"
        by (rule K.Class_eq_iff_diff_in_N[OF vM mzero_closed, THEN iffD2])
      with vN show "v \<in> {v \<in> N. proj_res N K v = K.Qclass \<zero>\<^sub>M}" by simp
    qed
  qed
qed

text \<open>Its image is @{text "(N \<oplus>\<^sub>S K)/K"}: the \<open>K\<close>-cosets of elements of @{term N} are exactly the
  \<open>K\<close>-cosets of elements of @{term "N \<oplus>\<^sub>S K"}, since adding an element of @{term K} to a
  representative does not change its coset.\<close>
lemma proj_res_image:
  assumes N: "submodule N" and K: "submodule K"
  shows "proj_res N K ` N
       = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` (N \<oplus>\<^sub>S K)"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  have NM: "N \<subseteq> M" using submodule_subset[OF N] .
  have KM: "K \<subseteq> M" using submodule_subset[OF K] .
  show ?thesis
  proof
    show "proj_res N K ` N \<subseteq> K.Qclass ` (N \<oplus>\<^sub>S K)"
    proof
      fix X assume "X \<in> proj_res N K ` N"
      then obtain v where v: "v \<in> N" "X = proj_res N K v" by blast
      then have "X = K.Qclass v" by simp
      moreover have "v \<in> N \<oplus>\<^sub>S K" using submodule_sum_incl_left[OF N K] v(1) by blast
      ultimately show "X \<in> K.Qclass ` (N \<oplus>\<^sub>S K)" by blast
    qed
    show "K.Qclass ` (N \<oplus>\<^sub>S K) \<subseteq> proj_res N K ` N"
    proof
      fix X assume "X \<in> K.Qclass ` (N \<oplus>\<^sub>S K)"
      then obtain x where x: "x \<in> N \<oplus>\<^sub>S K" "X = K.Qclass x" by blast
      from x(1) obtain u w where uw: "u \<in> N" "w \<in> K" "x = u \<oplus> w"
        by (rule submodule_sum_memE)
      have uM: "u \<in> M" using uw(1) NM by blast
      have wM: "w \<in> M" using uw(2) KM by blast
      \<comment> \<open>The representative may be taken in @{term N}: the @{term K}-part is absorbed.\<close>
      have "x \<oplus> madd.inverse u = (w \<oplus> u) \<oplus> madd.inverse u"
        using uw(3) uM wM by (simp add: madd.commutative)
      also have "\<dots> = w \<oplus> (u \<oplus> madd.inverse u)"
        using uM wM by (simp add: madd.associative)
      also have "\<dots> = w" using uM wM by simp
      finally have "x \<oplus> madd.inverse u = w" .
      then have "x \<oplus> madd.inverse u \<in> K" using uw(2) by simp
      moreover have xM: "x \<in> M" using uw(3) uM wM by simp
      ultimately have "K.Qclass x = K.Qclass u"
        using xM uM by (simp add: K.Class_eq_iff_diff_in_N)
      with x(2) have "X = proj_res N K u" using uw(1) by simp
      then show "X \<in> proj_res N K ` N" using uw(1) by blast
    qed
  qed
qed

text \<open>If @{term N} complements @{term K}, the restricted natural projection identifies
  @{term N} with the whole quotient @{text "M/K"}.  The two complement conditions have separate
  roles: trivial intersection gives injectivity through the kernel calculation, while the full
  submodule sum gives surjectivity through the image calculation.\<close>
theorem complement_quotient_isomorphism:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
  shows "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
           N (\<oplus>) \<zero>\<^sub>M (\<odot>)
           (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)
           (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
           (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
           (submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) K)
           (proj_res N K)
       \<and> bij_betw (proj_res N K) N
           (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K)"
proof -
  interpret K: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one>
      "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" K
    using K by unfold_locales
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      K.Qcarrier K.qadd "K.Qclass \<zero>\<^sub>M" K.qscale "proj_res N K"
    by (rule proj_res_hom[OF N K])

  have kernel: "P.Ker = N \<inter> K"
    unfolding P.Ker_def using proj_res_Ker[OF N K] by simp
  have injective: "inj_on (proj_res N K) N"
    using P.injective_iff_kernel_trivial kernel disjoint by simp

  have class_image: "K.Qclass ` M = K.Qcarrier"
  proof -
    have "K.Qclass ` M = K.nat_proj ` M"
    proof (rule image_cong)
      show "M = M" by simp
    next
      fix x assume x: "x \<in> M"
      show "K.Qclass x = K.nat_proj x"
        by (rule sym, rule K.nat_proj_apply[OF x])
    qed
    also have "... = K.Qcarrier" by (rule K.nat_proj_image)
    finally show ?thesis .
  qed
  have surjective: "proj_res N K ` N = K.Qcarrier"
    using proj_res_image[OF N K] full class_image by simp

  show ?thesis
    using P.module_homomorphism_axioms injective surjective
    by (simp add: bij_betw_def)
qed

text \<open>\<^emph>\<open>The second isomorphism theorem.\<close>\<close>
theorem second_isomorphism:
  assumes N: "submodule N" and K: "submodule K"
  shows "\<exists>\<phi>. module_homomorphism R (+) (\<cdot>) \<zero> \<one>
                (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M N (N \<inter> K))
                (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M N (N \<inter> K))
                (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M N (N \<inter> K) \<zero>\<^sub>M)
                (submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M N (\<odot>) (N \<inter> K))
                (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` (N \<oplus>\<^sub>S K))
                (submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K)
                (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M)
                (submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) K)
                \<phi>
           \<and> bij_betw \<phi>
                (submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M N (N \<inter> K))
                (submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` (N \<oplus>\<^sub>S K))"
proof -
  \<comment> \<open>Interpret the restricted projection as a homomorphism out of @{term N}, then quote its own
    first isomorphism theorem, rewriting the kernel to @{term "N \<inter> K"} and the image to
    \<open>(N \<oplus>\<^sub>S K)/K\<close>.\<close>
  \<comment> \<open>Established BEFORE the interpretation below: once \<open>P\<close> is interpreted, its \<open>source\<close> module
    supplies a second \<open>submodule_sum\<close> and the \<open>\<oplus>\<^sub>S\<close> notation becomes ambiguous.\<close>
  have image_eq: "proj_res N K ` N
                = submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K ` (N \<oplus>\<^sub>S K)"
    by (rule proj_res_image[OF N K])
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      "submodule_in_module.Qcarrier (\<oplus>) \<zero>\<^sub>M M K"
      "submodule_in_module.qadd (\<oplus>) \<zero>\<^sub>M M K"
      "submodule_in_module.Qclass (\<oplus>) \<zero>\<^sub>M M K \<zero>\<^sub>M"
      "submodule_in_module.qscale (\<oplus>) \<zero>\<^sub>M M (\<odot>) K"
      "proj_res N K"
    by (rule proj_res_hom[OF N K])
  have Ker_eq: "P.Ker = N \<inter> K"
    unfolding P.Ker_def using proj_res_Ker[OF N K] by simp
  show ?thesis
    using P.first_isomorphism unfolding Ker_eq image_eq by blast
qed

end (* context module *)

end
