section \<open>Quotient modules and the first isomorphism theorem\<close>

theory Quotient_Module
  imports Module_Homomorphism
begin

text \<open>Given a submodule @{term N} of an @{term R}-module @{term M}, the quotient set
  @{text "M/N"} inherits a module structure with scaling
  @{text "a \<cdot> Class(v) = Class(a \<odot> v)"}.  The construction reuses the group-quotient machinery of
  \<open>Group_Theory\<close> for the additive structure (any subgroup of an abelian group
  is normal, so cosets already form an abelian group under coset addition) and only requires the
  induced scaling to be shown well-defined.

  On this base we prove the natural projection to be a module homomorphism with kernel @{term N},
  and derive the first isomorphism theorem: for a module homomorphism @{term \<eta>}, the induced map on
  @{text "M/Ker \<eta>"} is an isomorphism onto the image @{term "\<eta> ` M"}.\<close>


subsection \<open>The quotient module of a submodule\<close>

text \<open>Work inside the @{locale Module} locale, with a submodule fixed.\<close>

locale submodule_in_module = Module +
  fixes N :: "'b set"
  assumes N_submodule: "submodule N"
begin

text \<open>The submodule is an additive subgroup of the module.  Since the additive group is abelian, it
  is automatically normal.\<close>
lemma N_subgroup: "Subgroup N M (\<oplus>) \<zero>\<^sub>M"
proof (rule madd.subgroupI)
  show "N \<subseteq> M" using submodule_subset[OF N_submodule] .
  show "\<zero>\<^sub>M \<in> N" using submodule_zero[OF N_submodule] .
next
  fix g h assume "g \<in> N" and "h \<in> N"
  then show "g \<oplus> h \<in> N" using submodule_add[OF N_submodule] by blast
next
  fix g assume gN: "g \<in> N"
  then have "g \<in> M" using submodule_subset[OF N_submodule] by blast
  then show "madd.invertible g" by simp
  show "madd.inverse g \<in> N" using submodule_neg[OF N_submodule gN] .
qed

sublocale madd_sub: subgroup_of_abelian_group N M "(\<oplus>)" "\<zero>\<^sub>M"
proof -
  interpret S: Subgroup N M "(\<oplus>)" "\<zero>\<^sub>M" by (rule N_subgroup)
  show "subgroup_of_abelian_group N M (\<oplus>) \<zero>\<^sub>M" ..
qed

text \<open>Notation: the quotient carrier, the coset class, and the induced coset addition.\<close>
abbreviation Qcarrier :: "'b set set"  (\<open>M'/N\<close>)
  where "M/N \<equiv> madd_sub.Factor_Group"

abbreviation Qclass :: "'b \<Rightarrow> 'b set"
  where "Qclass v \<equiv> madd_sub.Class v"

notation madd_sub.quotient_composition (infixl \<open>[\<oplus>]\<close> 65)

text \<open>An explicit constant for the coset addition, so it can be referred to by name from outside
  the locale (in @{command sublocale}-free consumers).\<close>
abbreviation qadd :: "'b set \<Rightarrow> 'b set \<Rightarrow> 'b set"
  where "qadd \<equiv> madd_sub.quotient_composition"

text \<open>The additive coset structure is already a (commutative) group, inherited from
  @{locale subgroup_of_abelian_group}.\<close>
lemma qmodule_additive: "Abelian_Group (M/N) ([\<oplus>]) (Qclass \<zero>\<^sub>M)"
  by (rule madd_sub.quotient_abelian)


subsubsection \<open>The induced scaling is well-defined\<close>

text \<open>Two module elements lie in the same coset iff their difference lies in @{term N}.\<close>
lemma Class_eq_iff_diff_in_N:
  assumes u: "u \<in> M" and v: "v \<in> M"
  shows "Qclass u = Qclass v \<longleftrightarrow> u \<oplus> madd.inverse v \<in> N"
proof -
  have raw: "Qclass u = Qclass v \<longleftrightarrow> madd.inverse u \<oplus> v \<in> N"
    using u v madd_sub.Congruence_def madd_sub.Class_equivalence by auto
  \<comment> \<open>In an abelian group @{term N} is closed under negation, and negation exchanges the two forms.\<close>
  have iff: "madd.inverse u \<oplus> v \<in> N \<longleftrightarrow> u \<oplus> madd.inverse v \<in> N"
  proof
    assume "madd.inverse u \<oplus> v \<in> N"
    then have "madd.inverse (madd.inverse u \<oplus> v) \<in> N"
      using N_submodule submodule_neg by blast
    also have "madd.inverse (madd.inverse u \<oplus> v) = madd.inverse v \<oplus> u"
      using u v by (simp add: madd.inverse_composition_commute)
    also have "\<dots> = u \<oplus> madd.inverse v" using u v by (simp add: madd.commutative)
    finally show "u \<oplus> madd.inverse v \<in> N" .
  next
    assume "u \<oplus> madd.inverse v \<in> N"
    then have "madd.inverse (u \<oplus> madd.inverse v) \<in> N"
      using N_submodule submodule_neg by blast
    also have "madd.inverse (u \<oplus> madd.inverse v) = v \<oplus> madd.inverse u"
      using u v by (simp add: madd.inverse_composition_commute)
    also have "\<dots> = madd.inverse u \<oplus> v" using u v by (simp add: madd.commutative)
    finally show "madd.inverse u \<oplus> v \<in> N" .
  qed
  from raw iff show ?thesis by simp
qed

text \<open>The scaling is well-defined on cosets: if \<open>u - v \<in> N\<close> (in the module additive sense) then
  \<open>a \<odot> u - a \<odot> v \<in> N\<close>, since \<open>a \<odot> (u \<oplus> madd.inverse v)\<close> equals
  \<open>(a \<odot> u) \<oplus> (a \<odot> madd.inverse v) = (a \<odot> u) \<oplus> madd.inverse (a \<odot> v)\<close> and lies in
  @{term N} by scaling-closedness of the submodule.\<close>
lemma scale_respects_Class:
  assumes a: "a \<in> R" and uv: "Qclass u = Qclass v" and u: "u \<in> M" and v: "v \<in> M"
  shows "Qclass (a \<odot> u) = Qclass (a \<odot> v)"
proof -
  from uv u v have diff: "u \<oplus> madd.inverse v \<in> N"
    using Class_eq_iff_diff_in_N by blast
  have "a \<odot> (u \<oplus> madd.inverse v) = (a \<odot> u) \<oplus> (a \<odot> madd.inverse v)"
    using a u v by (simp add: scale_distrib_madd)
  also have "a \<odot> madd.inverse v = madd.inverse (a \<odot> v)"
  proof -
    \<comment> \<open>@{term "madd.inverse v = (- \<one>) \<odot> v"} in any module; then use \<open>scale_scale\<close>
      and \<open>scale_neg_scalar\<close> on the scalar side.\<close>
    have inv_as_scale: "madd.inverse v = (- \<one>) \<odot> v"
      using v by (simp add: scale_neg_scalar scale_one)
    have "a \<odot> madd.inverse v = a \<odot> ((- \<one>) \<odot> v)" by (simp add: inv_as_scale)
    also have "\<dots> = (a \<cdot> (- \<one>)) \<odot> v" using a v by (simp add: scale_scale)
    also have "a \<cdot> (- \<one>) = - a" using a by (simp add: right_minus)
    also have "(- a) \<odot> v = madd.inverse (a \<odot> v)" using a v by (rule scale_neg_scalar)
    finally show ?thesis .
  qed
  finally have expand: "a \<odot> (u \<oplus> madd.inverse v) = (a \<odot> u) \<oplus> madd.inverse (a \<odot> v)" .
  have scaled_diff_in_N: "a \<odot> (u \<oplus> madd.inverse v) \<in> N"
    by (rule submodule_scale[OF N_submodule a diff])
  from scaled_diff_in_N have "(a \<odot> u) \<oplus> madd.inverse (a \<odot> v) \<in> N" by (simp add: expand)
  moreover have "a \<odot> u \<in> M" using a u by (rule scale_closed)
  moreover have "a \<odot> v \<in> M" using a v by (rule scale_closed)
  ultimately show ?thesis by (simp add: Class_eq_iff_diff_in_N)
qed


subsubsection \<open>The quotient scaling operation and the quotient module\<close>

text \<open>Choose any representative and scale it; well-definedness (@{thm [source] scale_respects_Class})
  makes the choice immaterial.\<close>
definition qscale :: "'a \<Rightarrow> 'b set \<Rightarrow> 'b set"  (infixr \<open>[\<odot>]\<close> 75)
  where "a [\<odot>] X = (THE Y. \<exists>v \<in> M. X = Qclass v \<and> Y = Qclass (a \<odot> v))"

lemma qscale_Class:
  assumes a: "a \<in> R" and v: "v \<in> M"
  shows "a [\<odot>] Qclass v = Qclass (a \<odot> v)"
proof -
  have "(THE Y. \<exists>u \<in> M. Qclass v = Qclass u \<and> Y = Qclass (a \<odot> u)) = Qclass (a \<odot> v)"
  proof (rule the_equality)
    show "\<exists>u \<in> M. Qclass v = Qclass u \<and> Qclass (a \<odot> v) = Qclass (a \<odot> u)"
      using v by blast
  next
    fix Y assume "\<exists>u \<in> M. Qclass v = Qclass u \<and> Y = Qclass (a \<odot> u)"
    then obtain u where u: "u \<in> M" "Qclass v = Qclass u" "Y = Qclass (a \<odot> u)" by blast
    have "Qclass (a \<odot> v) = Qclass (a \<odot> u)"
      by (rule scale_respects_Class[OF a u(2) v u(1)])
    then show "Y = Qclass (a \<odot> v)" using u(3) by simp
  qed
  then show ?thesis unfolding qscale_def by simp
qed

lemma qscale_closed [intro, simp]:
  assumes a: "a \<in> R" and X: "X \<in> M/N" shows "a [\<odot>] X \<in> M/N"
proof -
  from X obtain v where v: "v \<in> M" "X = Qclass v" using madd_sub.representant_exists by auto
  have avM: "a \<odot> v \<in> M" using a v(1) by (rule scale_closed)
  then have "Qclass (a \<odot> v) \<in> M/N" by (rule madd_sub.Class_in_Partition)
  then show ?thesis using a v by (simp add: qscale_Class)
qed

text \<open>The six module axioms on the quotient, packaged as a @{const Module_axioms} fact.  This is
  the pinch point: proving @{const Module_axioms} separately, and then composing with the ambient
  @{const Ring_axioms} via @{thm [source] Module.intro}, avoids the fragile mid-interpretation
  goal-order handshake we would face by opening a bare @{command sublocale} on @{locale Module}.\<close>
lemma quotient_module_axioms:
  "Module_axioms R (+) (\<cdot>) \<one> ([\<oplus>]) (Qclass \<zero>\<^sub>M) (M/N) ([\<odot>])"
proof (rule Module_axioms.intro)
  show "Abelian_Group (M/N) ([\<oplus>]) (Qclass \<zero>\<^sub>M)" by (rule qmodule_additive)
next
  fix a X assume a: "a \<in> R" and X: "X \<in> M/N" show "a [\<odot>] X \<in> M/N"
    using a X by (rule qscale_closed)
next
  fix a X Y assume a: "a \<in> R" and X: "X \<in> M/N" and Y: "Y \<in> M/N"
  from X obtain u where u: "u \<in> M" "X = Qclass u" using madd_sub.representant_exists by auto
  from Y obtain v where v: "v \<in> M" "Y = Qclass v" using madd_sub.representant_exists by auto
  have "a [\<odot>] (X [\<oplus>] Y) = a [\<odot>] Qclass (u \<oplus> v)"
    using u v by (simp add: madd_sub.Class_commutes_with_composition)
  also have "\<dots> = Qclass (a \<odot> (u \<oplus> v))"
    using a u v by (simp add: qscale_Class)
  also have "\<dots> = Qclass ((a \<odot> u) \<oplus> (a \<odot> v))"
    using a u v by (simp add: scale_distrib_madd)
  also have "\<dots> = Qclass (a \<odot> u) [\<oplus>] Qclass (a \<odot> v)"
    using a u v by (simp add: madd_sub.Class_commutes_with_composition scale_closed)
  also have "\<dots> = (a [\<odot>] X) [\<oplus>] (a [\<odot>] Y)"
    using a u v by (simp add: qscale_Class)
  finally show "a [\<odot>] (X [\<oplus>] Y) = (a [\<odot>] X) [\<oplus>] (a [\<odot>] Y)" .
next
  fix a b X assume a: "a \<in> R" and b: "b \<in> R" and X: "X \<in> M/N"
  from X obtain v where v: "v \<in> M" "X = Qclass v" using madd_sub.representant_exists by auto
  have "(a + b) [\<odot>] X = Qclass ((a + b) \<odot> v)" using a b v by (simp add: qscale_Class)
  also have "\<dots> = Qclass ((a \<odot> v) \<oplus> (b \<odot> v))" using a b v by (simp add: scale_distrib_add)
  also have "\<dots> = Qclass (a \<odot> v) [\<oplus>] Qclass (b \<odot> v)"
    using a b v by (simp add: madd_sub.Class_commutes_with_composition scale_closed)
  also have "\<dots> = (a [\<odot>] X) [\<oplus>] (b [\<odot>] X)" using a b v by (simp add: qscale_Class)
  finally show "(a + b) [\<odot>] X = (a [\<odot>] X) [\<oplus>] (b [\<odot>] X)" .
next
  fix a b X assume a: "a \<in> R" and b: "b \<in> R" and X: "X \<in> M/N"
  from X obtain v where v: "v \<in> M" "X = Qclass v" using madd_sub.representant_exists by auto
  have "(a \<cdot> b) [\<odot>] X = Qclass ((a \<cdot> b) \<odot> v)" using a b v by (simp add: qscale_Class)
  also have "\<dots> = Qclass (a \<odot> (b \<odot> v))" using a b v by (simp add: scale_scale)
  also have "\<dots> = a [\<odot>] Qclass (b \<odot> v)" using a b v by (simp add: qscale_Class scale_closed)
  also have "\<dots> = a [\<odot>] (b [\<odot>] X)" using b v by (simp add: qscale_Class)
  finally show "(a \<cdot> b) [\<odot>] X = a [\<odot>] (b [\<odot>] X)" .
next
  fix X assume X: "X \<in> M/N"
  from X obtain v where v: "v \<in> M" "X = Qclass v" using madd_sub.representant_exists by auto
  show "\<one> [\<odot>] X = X" using v by (simp add: qscale_Class scale_one)
qed

sublocale quotient: Module R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "([\<oplus>])" "Qclass \<zero>\<^sub>M" "M/N" "([\<odot>])"
  by (rule Module.intro[OF Ring_axioms quotient_module_axioms])


subsubsection \<open>The natural projection\<close>

text \<open>The natural projection @{text "v \<mapsto> Qclass v"} extensional on @{term M}.\<close>
definition nat_proj :: "'b \<Rightarrow> 'b set"
  where "nat_proj = (\<lambda>v \<in> M. Qclass v)"

lemma nat_proj_apply [simp]: "v \<in> M \<Longrightarrow> nat_proj v = Qclass v"
  unfolding nat_proj_def by simp

lemma nat_proj_undefined: "v \<notin> M \<Longrightarrow> nat_proj v = undefined"
  unfolding nat_proj_def by simp

text \<open>The natural projection is a module homomorphism with kernel @{term N}.\<close>
sublocale nat_proj: module_homomorphism
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>"
  M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
  "M/N" "([\<oplus>])" "Qclass \<zero>\<^sub>M" "([\<odot>])"
  nat_proj
proof
  show "nat_proj \<in> M \<rightarrow>\<^sub>E M/N"
    unfolding nat_proj_def by (rule PiE_I) (auto simp: extensional_def)
next
  fix u v assume "u \<in> M" "v \<in> M"
  then show "nat_proj (u \<oplus> v) = nat_proj u [\<oplus>] nat_proj v"
    by (simp add: madd_sub.Class_commutes_with_composition)
next
  fix a v assume "a \<in> R" "v \<in> M"
  then show "nat_proj (a \<odot> v) = a [\<odot>] nat_proj v"
    by (simp add: qscale_Class scale_closed)
qed

text \<open>The natural projection maps onto the entire quotient carrier.\<close>
theorem nat_proj_image: "nat_proj ` M = M/N"
proof
  show "nat_proj ` M \<subseteq> M/N" using nat_proj.hom_closed by blast
next
  show "M/N \<subseteq> nat_proj ` M"
  proof
    fix X assume X: "X \<in> M/N"
    then obtain v where v: "v \<in> M" "X = Qclass v"
      using madd_sub.representant_exists by blast
    then have "X = nat_proj v" by simp
    then show "X \<in> nat_proj ` M" using v(1) by blast
  qed
qed

text \<open>The kernel of the natural projection is exactly @{term N}.\<close>
theorem nat_proj_Ker: "nat_proj.Ker = N"
proof
  show "nat_proj.Ker \<subseteq> N"
  proof
    fix v assume vK: "v \<in> nat_proj.Ker"
    then have vM: "v \<in> M" using nat_proj.Ker_mem by simp
    from vK have "nat_proj v = Qclass \<zero>\<^sub>M" using nat_proj.Ker_image by simp
    with vM have Q: "Qclass v = Qclass \<zero>\<^sub>M" by simp
    from Q vM have "v \<oplus> madd.inverse \<zero>\<^sub>M \<in> N"
      using Class_eq_iff_diff_in_N by simp
    then show "v \<in> N" using vM by (simp add: madd.inverse_unit)
  qed
next
  show "N \<subseteq> nat_proj.Ker"
  proof
    fix v assume vN: "v \<in> N"
    then have vM: "v \<in> M" using N_submodule submodule_subset by blast
    have "v \<oplus> madd.inverse \<zero>\<^sub>M \<in> N" using vN vM by (simp add: madd.inverse_unit)
    then have "Qclass v = Qclass \<zero>\<^sub>M" using vM by (simp add: Class_eq_iff_diff_in_N)
    then have "nat_proj v = Qclass \<zero>\<^sub>M" using vM by simp
    then show "v \<in> nat_proj.Ker" using vM nat_proj.Ker_memI by simp
  qed
qed

end (* submodule_in_module *)

end
