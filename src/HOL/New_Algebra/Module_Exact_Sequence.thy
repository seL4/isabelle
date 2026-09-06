section \<open>Exact sequences of modules\<close>

theory Module_Exact_Sequence
  imports Module_Complements
begin

locale composable_module_homomorphisms =
  first: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
    M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" \<eta> +
  second: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
    M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" M'' "(\<oplus>\<^sub>3)" "\<zero>\<^sub>3" "(\<odot>\<^sub>3)" \<theta>
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70)
    and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
    and M and madd (infixl \<open>\<oplus>\<close> 65) and mzero (\<open>\<zero>\<^sub>M\<close>)
      and scale (infixr \<open>\<odot>\<close> 75)
    and M' and madd' (infixl \<open>\<oplus>\<^sub>2\<close> 65) and mzero' (\<open>\<zero>\<^sub>2\<close>)
      and scale' (infixr \<open>\<odot>\<^sub>2\<close> 75)
    and M'' and madd'' (infixl \<open>\<oplus>\<^sub>3\<close> 65) and mzero'' (\<open>\<zero>\<^sub>3\<close>)
      and scale'' (infixr \<open>\<odot>\<^sub>3\<close> 75)
    and \<eta> and \<theta>
begin

definition exact :: bool
  where "exact \<longleftrightarrow> \<eta> ` M = second.Ker"

definition short_exact :: bool
  where "short_exact \<longleftrightarrow> inj_on \<eta> M \<and> exact \<and> \<theta> ` M' = M''"

definition right_split :: bool
  where "right_split \<longleftrightarrow>
    (\<exists>\<sigma>. module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma> \<and>
      (\<forall>x\<in>M''. \<theta> (\<sigma> x) = x))"

definition left_split :: bool
  where "left_split \<longleftrightarrow>
    (\<exists>\<rho>. module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) M (\<oplus>) \<zero>\<^sub>M (\<odot>) \<rho> \<and>
      (\<forall>x\<in>M. \<rho> (\<eta> x) = x))"

lemma exact_iff: "exact \<longleftrightarrow> \<eta> ` M = second.Ker"
  by (rule exact_def)

lemma short_exact_iff:
  "short_exact \<longleftrightarrow> inj_on \<eta> M \<and> \<eta> ` M = second.Ker \<and> \<theta> ` M' = M''"
  by (simp add: short_exact_def exact_def)

lemma exact_imp_composition_zero:
  assumes ex: exact and x: "x \<in> M"
  shows "\<theta> (\<eta> x) = \<zero>\<^sub>3"
proof -
  have "\<eta> x \<in> \<eta> ` M" using x by (rule imageI)
  then have "\<eta> x \<in> second.Ker" using ex by (simp add: exact_def)
  then show ?thesis by (rule second.Ker_image)
qed

lemma right_split_imp_surjective:
  assumes split: right_split
  shows "\<theta> ` M' = M''"
proof
  show "\<theta> ` M' \<subseteq> M''" using second.hom_closed by blast
  show "M'' \<subseteq> \<theta> ` M'"
  proof
    fix x assume x: "x \<in> M''"
    obtain \<sigma> where hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma>"
      and sec: "\<forall>x\<in>M''. \<theta> (\<sigma> x) = x"
      using split unfolding right_split_def by blast
    interpret S: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M'' "(\<oplus>\<^sub>3)" "\<zero>\<^sub>3" "(\<odot>\<^sub>3)" M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" \<sigma>
      by (rule hom)
    have sx: "\<sigma> x \<in> M'" by (rule S.hom_closed[OF x])
    have eq: "\<theta> (\<sigma> x) = x" using sec x by blast
    have "\<theta> (\<sigma> x) \<in> \<theta> ` M'" by (rule imageI[OF sx])
    then show "x \<in> \<theta> ` M'" using eq by simp
  qed
qed

text \<open>The image of an explicit right section is complementary to the
  kernel of the split map.  The composite \<open>\<sigma> \<circ> \<theta>\<close> is the
  corresponding idempotent projection on the middle module.\<close>
theorem right_section_image_kernel_complementary:
  assumes section_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma>"
    and sec_eq: "\<And>x. x \<in> M'' \<Longrightarrow> \<theta> (\<sigma> x) = x"
  shows "\<sigma> ` M'' \<inter> second.Ker = {\<zero>\<^sub>2}"
    and "Module.submodule_sum (\<oplus>\<^sub>2) (\<sigma> ` M'') second.Ker = M'"
proof -
  interpret S: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
    M'' "(\<oplus>\<^sub>3)" "\<zero>\<^sub>3" "(\<odot>\<^sub>3)"
    M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" \<sigma>
    by (rule section_hom)
  define p where "p = compose M' \<sigma> \<theta>"
  have p_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) p"
    unfolding p_def by (rule second.compose_module_homomorphism[OF section_hom])
  interpret P: idempotent_module_endomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
    M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" p
  proof (rule idempotent_module_endomorphism.intro[OF p_hom])
    show "idempotent_module_endomorphism_axioms M' p"
    proof
      fix x assume x: "x \<in> M'"
      have tx: "\<theta> x \<in> M''" by (rule second.hom_closed[OF x])
      have stx: "\<sigma> (\<theta> x) \<in> M'" by (rule S.hom_closed[OF tx])
      show "p (p x) = p x"
        unfolding p_def compose_def
        using x tx stx sec_eq[OF tx] by simp
    qed
  qed
  have image_p: "p ` M' = \<sigma> ` M''"
  proof (rule set_eqI, rule iffI)
    fix y assume y: "y \<in> p ` M'"
    then obtain x where x: "x \<in> M'" "y = p x" by blast
    have tx: "\<theta> x \<in> M''" by (rule second.hom_closed[OF x(1)])
    have value_eq: "y = \<sigma> (\<theta> x)" using x unfolding p_def compose_def by simp
    have "\<sigma> (\<theta> x) \<in> \<sigma> ` M''" by (rule imageI[OF tx])
    then show "y \<in> \<sigma> ` M''" using value_eq by simp
  next
    fix y assume y: "y \<in> \<sigma> ` M''"
    then obtain z where z: "z \<in> M''" "y = \<sigma> z" by blast
    have sz: "\<sigma> z \<in> M'" by (rule S.hom_closed[OF z(1)])
    have value_eq: "p (\<sigma> z) = \<sigma> z"
      unfolding p_def compose_def using z sz sec_eq[OF z(1)] by simp
    have "p (\<sigma> z) \<in> p ` M'" by (rule imageI[OF sz])
    then show "y \<in> p ` M'" using z value_eq by simp
  qed
  have kernel_p: "P.Ker = second.Ker"
  proof (rule set_eqI, rule iffI)
    fix x assume x: "x \<in> P.Ker"
    have xM: "x \<in> M'" by (rule P.Ker_mem[OF x])
    have tx: "\<theta> x \<in> M''" by (rule second.hom_closed[OF xM])
    have theta_p: "\<theta> (p x) = \<theta> x"
      unfolding p_def compose_def using xM tx sec_eq[OF tx] by simp
    have "\<theta> (p x) = \<zero>\<^sub>3"
      using P.Ker_image[OF x] second.hom_zero by simp
    then have "\<theta> x = \<zero>\<^sub>3" using theta_p by simp
    then show "x \<in> second.Ker" by (rule second.Ker_memI[OF _ xM])
  next
    fix x assume x: "x \<in> second.Ker"
    have xM: "x \<in> M'" by (rule second.Ker_mem[OF x])
    have "p x = \<zero>\<^sub>2"
      unfolding p_def compose_def
      using xM second.Ker_image[OF x] S.hom_zero by simp
    then show "x \<in> P.Ker" by (rule P.Ker_memI[OF _ xM])
  qed
  show "\<sigma> ` M'' \<inter> second.Ker = {\<zero>\<^sub>2}"
    using P.image_kernel_complementary(1) image_p kernel_p by simp
  show "Module.submodule_sum (\<oplus>\<^sub>2) (\<sigma> ` M'') second.Ker = M'"
    using P.image_kernel_complementary(2) image_p kernel_p by simp
qed

theorem right_split_obtains_image_kernel_complement:
  assumes split: right_split
  obtains \<sigma> where
    "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma>"
    "\<And>x. x \<in> M'' \<Longrightarrow> \<theta> (\<sigma> x) = x"
    "\<sigma> ` M'' \<inter> second.Ker = {\<zero>\<^sub>2}"
    "Module.submodule_sum (\<oplus>\<^sub>2) (\<sigma> ` M'') second.Ker = M'"
proof -
  obtain \<sigma> where hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma>"
    and sec: "\<forall>x\<in>M''. \<theta> (\<sigma> x) = x"
    using split unfolding right_split_def by blast
  have sec_eq: "\<And>x. x \<in> M'' \<Longrightarrow> \<theta> (\<sigma> x) = x" using sec by blast
  have complementary:
      "\<sigma> ` M'' \<inter> second.Ker = {\<zero>\<^sub>2}"
      "Module.submodule_sum (\<oplus>\<^sub>2) (\<sigma> ` M'') second.Ker = M'"
  proof -
    show "\<sigma> ` M'' \<inter> second.Ker = {\<zero>\<^sub>2}"
      by (rule right_section_image_kernel_complementary(1)[OF hom sec_eq])
    show "Module.submodule_sum (\<oplus>\<^sub>2) (\<sigma> ` M'') second.Ker = M'"
      by (rule right_section_image_kernel_complementary(2)[OF hom sec_eq])
  qed
  show thesis by (rule that[OF hom sec_eq complementary])
qed

theorem short_exact_right_split_obtains_decomposition:
  assumes short: short_exact and split: right_split
  obtains \<sigma> where
    "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma>"
    "\<And>x. x \<in> M'' \<Longrightarrow> \<theta> (\<sigma> x) = x"
    "\<sigma> ` M'' \<inter> \<eta> ` M = {\<zero>\<^sub>2}"
    "Module.submodule_sum (\<oplus>\<^sub>2) (\<sigma> ` M'') (\<eta> ` M) = M'"
proof -
  obtain \<sigma> where hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma>"
    and sec_eq: "\<And>x. x \<in> M'' \<Longrightarrow> \<theta> (\<sigma> x) = x"
    and disjoint: "\<sigma> ` M'' \<inter> second.Ker = {\<zero>\<^sub>2}"
    and full: "Module.submodule_sum (\<oplus>\<^sub>2) (\<sigma> ` M'') second.Ker = M'"
    using right_split_obtains_image_kernel_complement[OF split] by blast
  have exact: "\<eta> ` M = second.Ker" using short by (simp add: short_exact_iff)
  show thesis
    by (rule that[OF hom sec_eq]) (use disjoint full exact in simp_all)
qed

text \<open>A right section yields a retraction of the injection.  The projection onto the image of
  @{term \<eta>} along the section image is followed by the inverse of @{term \<eta>} onto its image.\<close>
theorem short_exact_right_split_imp_left_split:
  assumes short: short_exact and split: right_split
  shows left_split
proof -
  obtain \<sigma> where section_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma>"
    and sec_eq: "\<And>x. x \<in> M'' \<Longrightarrow> \<theta> (\<sigma> x) = x"
    and disjoint: "\<sigma> ` M'' \<inter> second.Ker = {\<zero>\<^sub>2}"
    and full: "Module.submodule_sum (\<oplus>\<^sub>2) (\<sigma> ` M'') second.Ker = M'"
    using right_split_obtains_image_kernel_complement[OF split] by blast
  have exact: "\<eta> ` M = second.Ker" using short by (simp add: short_exact_iff)
  have eta_sub: "first.target.submodule (\<eta> ` M)" using first.image_submodule .
  interpret S: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M'' "(\<oplus>\<^sub>3)" "\<zero>\<^sub>3" "(\<odot>\<^sub>3)"
      M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" \<sigma>
    by (rule section_hom)
  have sigma_sub: "first.target.submodule (\<sigma> ` M'')" using S.image_submodule .
  have eta_sub': "Module.submodule R (\<oplus>\<^sub>2) \<zero>\<^sub>2 M' (\<odot>\<^sub>2) (\<eta> ` M)"
    using eta_sub .
  have sigma_sub': "Module.submodule R (\<oplus>\<^sub>2) \<zero>\<^sub>2 M' (\<odot>\<^sub>2) (\<sigma> ` M'')"
    using sigma_sub .
  have disjoint': "\<eta> ` M \<inter> \<sigma> ` M'' = {\<zero>\<^sub>2}"
    using disjoint exact by (simp add: Int_commute)
  have full': "Module.submodule_sum (\<oplus>\<^sub>2) (\<eta> ` M) (\<sigma> ` M'') = M'"
    using full exact first.target.submodule_sum_commute[OF eta_sub sigma_sub] by simp
  interpret Kq: submodule_in_module R "(+)" "(\<cdot>)" \<zero> \<one>
      "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" M' "(\<odot>\<^sub>2)" "(\<sigma> ` M'')"
    using sigma_sub' by unfold_locales
  interpret Q: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      "(\<eta> ` M)" "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)"
      Kq.Qcarrier Kq.qadd "Kq.Qclass \<zero>\<^sub>2" Kq.qscale
      "first.target.proj_res (\<eta> ` M) (\<sigma> ` M'')"
    by (rule first.target.proj_res_hom[OF eta_sub' sigma_sub'])
  have projection_bij:
      "bij_betw (first.target.proj_res (\<eta> ` M) (\<sigma> ` M''))
        (\<eta> ` M) Kq.Qcarrier"
    using first.target.complement_quotient_isomorphism
      [OF eta_sub' sigma_sub' disjoint' full'] by blast
  have inverse_projection:
      "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        Kq.Qcarrier Kq.qadd (Kq.Qclass \<zero>\<^sub>2) Kq.qscale
        (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
        (restrict (inv_into (\<eta> ` M) (first.target.proj_res (\<eta> ` M) (\<sigma> ` M''))) Kq.Qcarrier)"
    by (rule Q.inverse_module_homomorphism[OF projection_bij])
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)"
      "(\<eta> ` M)" "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)"
      "first.target.complement_projection (\<eta> ` M) (\<sigma> ` M'')"
    by (rule first.target.complement_projection_hom
      [OF eta_sub' sigma_sub' disjoint' full'])
  have eta_image_hom:
      "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M (\<oplus>) \<zero>\<^sub>M (\<odot>)
        (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>"
  proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
    show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)"
      by (rule first.source.Module_axioms)
    show "Module R (+) (\<cdot>) \<zero> \<one>
        (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<eta> ` M) (\<odot>\<^sub>2)"
      by (rule first.image_is_module)
    show "\<eta> \<in> M \<rightarrow>\<^sub>E (\<eta> ` M)"
      using first.hom_closed by (auto simp: PiE_iff extensional_def)
  next
    fix u v assume uv: "u \<in> M" "v \<in> M"
    then show "\<eta> (u \<oplus> v) = \<eta> u \<oplus>\<^sub>2 \<eta> v"
      by (rule first.hom_add)
  next
    fix a v assume av: "a \<in> R" "v \<in> M"
    then show "\<eta> (a \<odot> v) = a \<odot>\<^sub>2 \<eta> v"
      by (rule first.hom_scale)
  qed
  interpret I: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
      "(\<eta> ` M)" "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" \<eta>
    by (rule eta_image_hom)
  have inj_eta: "inj_on \<eta> M" using short by (simp add: short_exact_def)
  have eta_bij: "bij_betw \<eta> M (\<eta> ` M)"
    using inj_eta by (simp add: bij_betw_def)
  have J_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      (\<eta> ` M) (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
      M (\<oplus>) \<zero>\<^sub>M (\<odot>)
      (restrict (inv_into M \<eta>) (\<eta> ` M))"
    by (rule I.inverse_module_homomorphism[OF eta_bij])
  define \<rho> where
    "\<rho> = compose M' (restrict (inv_into M \<eta>) (\<eta> ` M))
      (first.target.complement_projection (\<eta> ` M) (\<sigma> ` M''))"
  have rho_hom:
    "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
        M (\<oplus>) \<zero>\<^sub>M (\<odot>) \<rho>"
    unfolding \<rho>_def
    by (rule P.compose_module_homomorphism[OF J_hom])
  have retract: "\<And>x. x \<in> M \<Longrightarrow> \<rho> (\<eta> x) = x"
  proof -
    fix x assume x: "x \<in> M"
    have eta_x: "\<eta> x \<in> \<eta> ` M" by (rule imageI[OF x])
    have eta_xM': "\<eta> x \<in> M'" by (rule first.hom_closed[OF x])
    have projection: "first.target.complement_projection (\<eta> ` M) (\<sigma> ` M'') (\<eta> x) = \<eta> x"
      by (rule first.target.complement_projection_apply_left
          [OF eta_sub sigma_sub disjoint' full' eta_x])
    have inverse: "restrict (inv_into M \<eta>) (\<eta> ` M) (\<eta> x) = x"
      by (rule I.inverse_module_homomorphism_left[OF eta_bij x])
    show "\<rho> (\<eta> x) = x"
      unfolding \<rho>_def compose_def
      using projection inverse eta_x eta_xM' by (simp add: restrict_apply')
  qed
  show ?thesis unfolding left_split_def using rho_hom retract by blast
qed

text \<open>A retraction of the injection makes its image a direct summand.  Exactness then
  identifies the complementary summand with the quotient, so the second map has a
  carrier-restricted inverse that supplies a right section.\<close>
theorem short_exact_left_split_imp_right_split:
  assumes short: short_exact and split: left_split
  shows right_split
proof -
  obtain \<rho> where rho_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) M (\<oplus>) \<zero>\<^sub>M (\<odot>) \<rho>"
    and retract: "\<And>x. x \<in> M \<Longrightarrow> \<rho> (\<eta> x) = x"
    using split unfolding left_split_def by blast
  interpret Rho: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)"
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" \<rho>
    by (rule rho_hom)
  have eta_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M (\<oplus>) \<zero>\<^sub>M (\<odot>)
      M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>"
    by unfold_locales
  define p where "p = compose M' \<eta> \<rho>"
  have p_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
      M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) p"
    unfolding p_def
    by (rule Rho.compose_module_homomorphism[OF eta_hom])
  interpret P: idempotent_module_endomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" p
  proof (rule idempotent_module_endomorphism.intro[OF p_hom])
    show "idempotent_module_endomorphism_axioms M' p"
    proof
      fix x assume xM': "x \<in> M'"
      have rx: "\<rho> x \<in> M" by (rule Rho.hom_closed[OF xM'])
      have etarx: "\<eta> (\<rho> x) \<in> M'" by (rule first.hom_closed[OF rx])
      show "p (p x) = p x"
        unfolding p_def compose_def
        using xM' rx etarx retract[OF rx] by simp
    qed
  qed
  have inj_eta: "inj_on \<eta> M" using short by (simp add: short_exact_def)
  have image_p: "p ` M' = \<eta> ` M"
  proof (rule set_eqI, rule iffI)
    fix y assume y: "y \<in> p ` M'"
    then obtain x where x: "x \<in> M'" "y = p x" by blast
    have rx: "\<rho> x \<in> M" by (rule Rho.hom_closed[OF x(1)])
    have value_eq: "y = \<eta> (\<rho> x)"
      using x unfolding p_def compose_def by simp
    then show "y \<in> \<eta> ` M" using rx by blast
  next
    fix y assume y: "y \<in> \<eta> ` M"
    then obtain x where x: "x \<in> M" "y = \<eta> x" by blast
    have etax: "\<eta> x \<in> M'" by (rule first.hom_closed[OF x(1)])
    have value_eq: "p (\<eta> x) = \<eta> x"
      unfolding p_def compose_def using x retract[OF x(1)] by simp
    have image_value: "p (\<eta> x) \<in> p ` M'" by (rule imageI[OF etax])
    then show "y \<in> p ` M'" using value_eq x(2) by simp
  qed
  have Pker_sub: "first.target.submodule P.Ker" using P.Ker_submodule .
  have eta_sub: "first.target.submodule (\<eta> ` M)" using first.image_submodule .
  have disjoint_P: "P.Ker \<inter> (\<eta> ` M) = {\<zero>\<^sub>2}"
    using P.image_kernel_complementary(1) image_p by (simp add: Int_commute)
  have full_eta_P: "Module.submodule_sum (\<oplus>\<^sub>2) (\<eta> ` M) P.Ker = M'"
    using P.image_kernel_complementary(2) image_p by simp
  have full_P_eta: "Module.submodule_sum (\<oplus>\<^sub>2) P.Ker (\<eta> ` M) = M'"
    using full_eta_P first.target.submodule_sum_commute[OF Pker_sub eta_sub] by simp
  have exact: "\<eta> ` M = second.Ker" using short by (simp add: short_exact_iff)
  have theta_restrict_hom:
      "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        P.Ker (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
        M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3)
        (restrict \<theta> P.Ker)"
  proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
    show "Module R (+) (\<cdot>) \<zero> \<one>
        (\<oplus>\<^sub>2) \<zero>\<^sub>2 P.Ker (\<odot>\<^sub>2)"
      by (rule first.target.submodule_is_module[OF Pker_sub])
    show "Module R (+) (\<cdot>) \<zero> \<one>
        (\<oplus>\<^sub>3) \<zero>\<^sub>3 M'' (\<odot>\<^sub>3)"
      by (rule second.target.Module_axioms)
    show "restrict \<theta> P.Ker \<in> P.Ker \<rightarrow>\<^sub>E M''"
      using first.target.submodule_subset[OF Pker_sub] second.hom_closed
      by (auto simp: PiE_iff extensional_def)
  next
    fix u v assume uv: "u \<in> P.Ker" "v \<in> P.Ker"
    have uM': "u \<in> M'" and vM': "v \<in> M'"
      using uv first.target.submodule_subset[OF Pker_sub] by auto
    have uvP: "u \<oplus>\<^sub>2 v \<in> P.Ker"
      by (rule first.target.submodule_add[OF Pker_sub uv(1) uv(2)])
    show "restrict \<theta> P.Ker (u \<oplus>\<^sub>2 v) =
        restrict \<theta> P.Ker u \<oplus>\<^sub>3 restrict \<theta> P.Ker v"
      using uv uvP uM' vM' by (simp add: restrict_apply' second.hom_add)
  next
    fix a v assume av: "a \<in> R" "v \<in> P.Ker"
    have vM': "v \<in> M'" using av(2) first.target.submodule_subset[OF Pker_sub] by blast
    have avP: "a \<odot>\<^sub>2 v \<in> P.Ker"
      by (rule first.target.submodule_scale[OF Pker_sub av(1) av(2)])
    show "restrict \<theta> P.Ker (a \<odot>\<^sub>2 v) =
        a \<odot>\<^sub>3 restrict \<theta> P.Ker v"
      using av avP vM' by (simp add: restrict_apply' second.hom_scale)
  qed
  interpret T: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      P.Ker "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)"
      M'' "(\<oplus>\<^sub>3)" "\<zero>\<^sub>3" "(\<odot>\<^sub>3)" "restrict \<theta> P.Ker"
    by (rule theta_restrict_hom)
  have T_kernel: "T.Ker = {\<zero>\<^sub>2}"
  proof (rule set_eqI, rule iffI)
    fix x assume x: "x \<in> T.Ker"
    have xP: "x \<in> P.Ker" by (rule T.Ker_mem[OF x])
    have xM': "x \<in> M'" using xP first.target.submodule_subset[OF Pker_sub] by blast
    have theta_x: "\<theta> x = \<zero>\<^sub>3"
      using T.Ker_image[OF x] xP by (simp add: restrict_apply')
    have xeta: "x \<in> \<eta> ` M"
    proof -
      have xsecond: "x \<in> second.Ker" by (rule second.Ker_memI[OF theta_x xM'])
      then show ?thesis using exact by simp
    qed
    have "x \<in> P.Ker \<inter> (\<eta> ` M)" by (rule IntI[OF xP xeta])
    then show "x \<in> {\<zero>\<^sub>2}" using disjoint_P by simp
  next
    fix x assume x: "x \<in> {\<zero>\<^sub>2}"
    have zeroP: "\<zero>\<^sub>2 \<in> P.Ker" by (rule first.target.submodule_zero[OF Pker_sub])
    have zeroT: "restrict \<theta> P.Ker \<zero>\<^sub>2 = \<zero>\<^sub>3" by (rule T.hom_zero)
    show "x \<in> T.Ker" using x zeroP zeroT by (simp add: T.Ker_def)
  qed
  have T_inj: "inj_on (restrict \<theta> P.Ker) P.Ker"
    using T.injective_iff_kernel_trivial T_kernel by blast
  have T_image: "(restrict \<theta> P.Ker) ` P.Ker = M''"
  proof (rule set_eqI, rule iffI)
    fix z assume z: "z \<in> (restrict \<theta> P.Ker) ` P.Ker"
    then obtain u where u: "u \<in> P.Ker" "z = restrict \<theta> P.Ker u" by blast
    have uM': "u \<in> M'" using u(1) first.target.submodule_subset[OF Pker_sub] by blast
    show "z \<in> M''" using u(1) u(2) second.hom_closed[OF uM'] by (simp add: restrict_apply')
  next
    fix z assume z: "z \<in> M''"
    have theta_surj: "\<theta> ` M' = M''" using short by (simp add: short_exact_iff)
    have zimage: "z \<in> \<theta> ` M'" using z theta_surj by simp
    then obtain y where y: "y \<in> M'" "z = \<theta> y" by blast
    have ysum: "y \<in> Module.submodule_sum (\<oplus>\<^sub>2) P.Ker (\<eta> ` M)"
      using y(1) full_P_eta by simp
    then obtain u v where uv: "u \<in> P.Ker" "v \<in> \<eta> ` M" "y = u \<oplus>\<^sub>2 v"
      by (rule first.target.submodule_sum_memE)
    have uM': "u \<in> M'" using uv(1) first.target.submodule_subset[OF Pker_sub] by blast
    have vM': "v \<in> M'" using uv(2) first.target.submodule_subset[OF eta_sub] by blast
    have theta_v: "\<theta> v = \<zero>\<^sub>3"
    proof -
      have vker: "v \<in> second.Ker" using uv(2) exact by simp
      then show ?thesis by (rule second.Ker_image)
    qed
    have theta_u: "\<theta> u = z"
      using y uv(3) uM' vM' theta_v by (simp add: second.hom_add)
    have image_u: "(restrict \<theta> P.Ker) u \<in>
        (restrict \<theta> P.Ker) ` P.Ker" by (rule imageI[OF uv(1)])
    show "z \<in> (restrict \<theta> P.Ker) ` P.Ker"
      using image_u theta_u uv(1) by (simp add: restrict_apply')
  qed
  have T_bij: "bij_betw (restrict \<theta> P.Ker) P.Ker M''"
    using T_inj T_image by (simp add: bij_betw_def)
  have inverse_hom:
      "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3)
        P.Ker (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
        (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'')"
    by (rule T.inverse_module_homomorphism[OF T_bij])
  interpret U: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
      M'' "(\<oplus>\<^sub>3)" "\<zero>\<^sub>3" "(\<odot>\<^sub>3)"
      P.Ker "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)"
      "restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M''"
    by (rule inverse_hom)
  have inclusion_hom:
      "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        P.Ker (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
        M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) (identity P.Ker)"
  proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
    show "Module R (+) (\<cdot>) \<zero> \<one>
        (\<oplus>\<^sub>2) \<zero>\<^sub>2 P.Ker (\<odot>\<^sub>2)"
      by (rule first.target.submodule_is_module[OF Pker_sub])
    show "Module R (+) (\<cdot>) \<zero> \<one>
        (\<oplus>\<^sub>2) \<zero>\<^sub>2 M' (\<odot>\<^sub>2)"
      by (rule first.target.Module_axioms)
    show "identity P.Ker \<in> P.Ker \<rightarrow>\<^sub>E M'"
      using first.target.submodule_subset[OF Pker_sub] by (auto simp: PiE_iff)
  next
    fix u v assume u: "u \<in> P.Ker" and v: "v \<in> P.Ker"
    have uv: "u \<oplus>\<^sub>2 v \<in> P.Ker"
      by (rule first.target.submodule_add[OF Pker_sub u v])
    then show "identity P.Ker (u \<oplus>\<^sub>2 v) =
        identity P.Ker u \<oplus>\<^sub>2 identity P.Ker v"
      using u v by simp
  next
    fix a v assume a: "a \<in> R" and v: "v \<in> P.Ker"
    have av: "a \<odot>\<^sub>2 v \<in> P.Ker"
      by (rule first.target.submodule_scale[OF Pker_sub a v])
    then show "identity P.Ker (a \<odot>\<^sub>2 v) =
        a \<odot>\<^sub>2 identity P.Ker v"
      using v by simp
  qed
  define \<sigma> where
    "\<sigma> = compose M'' (identity P.Ker)
      (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'')"
  have section_hom:
      "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M'' (\<oplus>\<^sub>3) \<zero>\<^sub>3 (\<odot>\<^sub>3)
        M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<sigma>"
    unfolding \<sigma>_def
    by (rule U.compose_module_homomorphism[OF inclusion_hom])
  have section_eq: "\<And>z. z \<in> M'' \<Longrightarrow> \<theta> (\<sigma> z) = z"
  proof -
    fix z assume z: "z \<in> M''"
    have uz: "restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z \<in> P.Ker"
      by (rule U.hom_closed[OF z])
    have inverse: "restrict \<theta> P.Ker
        (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z) = z"
      by (rule T.inverse_module_homomorphism_right[OF T_bij z])
    have sigma_apply: "\<sigma> z =
        restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z"
      unfolding \<sigma>_def compose_def
      using uz z by (simp add: restrict_apply')
    have inverse_value: "\<theta>
        (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z) =
        restrict \<theta> P.Ker
          (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z)"
      by (rule sym, rule restrict_apply'[OF uz])
    have theta_sigma: "\<theta> (\<sigma> z) = \<theta>
        (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z)"
      by (simp only: sigma_apply)
    have theta_restrict: "\<theta>
        (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z) =
        restrict \<theta> P.Ker
          (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z)"
      by (rule inverse_value)
    have theta_intermediate: "\<theta> (\<sigma> z) =
        restrict \<theta> P.Ker
          (restrict (inv_into P.Ker (restrict \<theta> P.Ker)) M'' z)"
      by (rule trans[OF theta_sigma theta_restrict])
    show "\<theta> (\<sigma> z) = z"
      by (rule trans[OF theta_intermediate inverse])
  qed
  show ?thesis unfolding right_split_def using section_hom section_eq by blast
qed

theorem short_exact_right_split_iff_left_split:
  assumes short: short_exact
  shows "right_split \<longleftrightarrow> left_split"
  using short_exact_right_split_imp_left_split[OF short]
    short_exact_left_split_imp_right_split[OF short] by blast

end

context Module
begin

text \<open>The carrier-restricted identity on a submodule is its inclusion into the
  ambient module.\<close>
theorem submodule_inclusion_hom:
  assumes N: "submodule N"
  shows "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
    N (\<oplus>) \<zero>\<^sub>M (\<odot>) M (\<oplus>) \<zero>\<^sub>M (\<odot>) (identity N)"
proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
  show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M N (\<odot>)"
    by (rule submodule_is_module[OF N])
  show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)"
    by (rule Module_axioms)
  show "identity N \<in> N \<rightarrow>\<^sub>E M"
    using submodule_subset[OF N] by (auto simp: PiE_iff)
next
  fix u v assume u: "u \<in> N" and v: "v \<in> N"
  have uv: "u \<oplus> v \<in> N" using N u v by (rule submodule_add)
  then show "identity N (u \<oplus> v) = identity N u \<oplus> identity N v"
    using u v by simp
next
  fix a v assume a: "a \<in> R" and v: "v \<in> N"
  have av: "a \<odot> v \<in> N" using N a v by (rule submodule_scale)
  then show "identity N (a \<odot> v) = a \<odot> identity N v"
    using v by simp
qed

text \<open>Complementary submodules give the canonical split short exact sequence
  \<open>0 \<longrightarrow> K \<longrightarrow> M \<longrightarrow> N \<longrightarrow> 0\<close>.  The inclusion of \<open>N\<close>
  is a section of the complementary projection.\<close>
theorem complementary_submodules_split_short_exact:
  assumes N: "submodule N" and K: "submodule K"
    and disjoint: "N \<inter> K = {\<zero>\<^sub>M}"
    and full: "N \<oplus>\<^sub>S K = M"
  shows "composable_module_homomorphisms.short_exact
      K M N \<zero>\<^sub>M (identity K) (complement_projection N K)
    \<and> composable_module_homomorphisms.right_split
      R (+) (\<cdot>) \<zero> \<one>
      M (\<oplus>) \<zero>\<^sub>M (\<odot>) N (\<oplus>) \<zero>\<^sub>M (\<odot>)
      (complement_projection N K)"
proof -
  interpret I: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
    K "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" "identity K"
    by (rule submodule_inclusion_hom[OF K])
  interpret P: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
    M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" "complement_projection N K"
    by (rule complement_projection_hom[OF N K disjoint full])
  interpret E: composable_module_homomorphisms R "(+)" "(\<cdot>)" \<zero> \<one>
    K "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
    N "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" "identity K" "complement_projection N K"
    by unfold_locales
  have image_I: "identity K ` K = K" by auto
  have ker_P: "P.Ker = K"
    using complement_projection_Ker[OF N K disjoint full]
    by (simp add: P.Ker_def)
  have image_P: "complement_projection N K ` M = N"
    by (rule complement_projection_image[OF N K disjoint full])
  have short: "E.short_exact"
    by (simp add: E.short_exact_def E.exact_def image_I ker_P image_P)
  have section_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      N (\<oplus>) \<zero>\<^sub>M (\<odot>) M (\<oplus>) \<zero>\<^sub>M (\<odot>) (identity N)"
    by (rule submodule_inclusion_hom[OF N])
  have sec: "\<forall>x\<in>N. complement_projection N K (identity N x) = x"
    using complement_projection_apply_left[OF N K disjoint full] by simp
  have split: "E.right_split"
    unfolding E.right_split_def using section_hom sec by blast
  show ?thesis using short split by simp
qed

end

end
