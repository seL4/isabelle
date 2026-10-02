section \<open>Generic restriction of field automorphisms\<close>

theory Galois_Restriction
  imports Galois_Automorphism Solvable_Transfer Galois_Action 
begin


text \<open>For a base subset \<open>F \<subseteq> E \<subseteq> K\<close>, where \<open>E\<close> and \<open>K\<close> are
  subfields, stability of the intermediate carrier under the base-field automorphisms makes
  restriction a homomorphism between the two corresponding automorphism groups.  This theory
  contains the reusable carrier-set bookkeeping; splitting-field and polynomial-extension
  arguments remain in the theories that consume it.\<close>

definition galois_restriction ::
    "'a :: field set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow>
     (('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a))"
  where "galois_restriction (K :: 'a set) E F = restrict (\<lambda>\<sigma>. restrict \<sigma> E) (field_auto K F)"

lemma galois_restriction_apply [simp]:
  "\<sigma> \<in> field_auto K F \<Longrightarrow>
    galois_restriction K E F \<sigma> = restrict \<sigma> E"
  by (simp add: galois_restriction_def)

context
  fixes K E F :: "'a :: field set"
  assumes K: "Subfield K" and sfE: "Subfield E"
    and FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
    and stable: "\<And>\<sigma>. \<sigma> \<in> field_auto K F \<Longrightarrow> \<sigma> ` E = E"
begin

lemma field_auto_bij: "\<sigma> \<in> field_auto K F \<Longrightarrow> bij_betw \<sigma> E E"
  by (metis EK bij_betw_subset field_auto_mem_iff stable)

text \<open>Restriction inherits the field laws and fixed-base condition, while stability supplies
  the required bijection of the intermediate carrier.\<close>
lemma gal_res_mem:
  assumes s: "\<sigma> \<in> field_auto K F"
  shows "restrict \<sigma> E \<in> field_auto E F"
proof -
  have sE: "\<sigma> ` E = E" using s by (rule stable)
  have addh: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x + y) = \<sigma> x + \<sigma> y"
    and multh: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x * y) = \<sigma> x * \<sigma> y"
    and one: "\<sigma> 1 = 1" and fixF: "\<And>x. x \<in> F \<Longrightarrow> \<sigma> x = x"
    using s by (auto simp: field_auto_mem_iff)
  interpret E: Subfield E by (rule sfE)
  show ?thesis
    unfolding field_auto_mem_iff
  proof (intro conjI ballI)
    fix x y assume xy: "x \<in> E" "y \<in> E"
    have xyK: "x \<in> K" "y \<in> K" using xy EK by auto
    show "restrict \<sigma> E (x + y) = restrict \<sigma> E x + restrict \<sigma> E y"
      using xy xyK E.add_closed addh by simp
    show "restrict \<sigma> E (x * y) = restrict \<sigma> E x * restrict \<sigma> E y"
      using xy xyK E.mult_closed multh by simp
  qed (use field_auto_bij[OF s] sE fixF FE one in auto)
qed

text \<open>Restriction turns composition in @{term K} into composition in @{term E}.\<close>
lemma gal_res_compose:
  assumes s: "\<sigma> \<in> field_auto K F" and t: "\<tau> \<in> field_auto K F"
  shows "restrict (compose K \<sigma> \<tau>) E = compose E (restrict \<sigma> E) (restrict \<tau> E)"
proof (rule ext)
  fix x
  show "restrict (compose K \<sigma> \<tau>) E x = compose E (restrict \<sigma> E) (restrict \<tau> E) x"
  proof (cases "x \<in> E")
    case True
    with EK have xK: "x \<in> K" by blast
    have txE: "\<tau> x \<in> E"
    proof -
      have "\<tau> x \<in> \<tau> ` E" by (rule imageI[OF True])
      then show ?thesis using stable[OF t] by simp
    qed
    show ?thesis by (simp add: compose_def txE xK)
  qed (simp add: compose_def restrict_def)
qed

text \<open>Restriction sends the identity of @{term K} to the identity of @{term E}.\<close>
lemma gal_res_unit: "restrict (identity K) E = identity E"
  using EK by fastforce

theorem galois_restriction_hom:
  "group_homomorphism (restrict (\<lambda>\<sigma>. restrict \<sigma> E) (field_auto K F))
      (field_auto K F) (compose K) (identity K)
      (field_auto E F) (compose E) (identity E)"
proof -
  have FK: "F \<subseteq> K" using FE EK by blast
  interpret GK: Group "field_auto K F" "compose K" "identity K"
    by (rule field_auto_group[OF K FK])
  interpret GE: Group "field_auto E F" "compose E" "identity E"
    by (rule field_auto_group[OF sfE FE])
  show ?thesis
  proof qed (use gal_res_mem gal_res_unit in \<open>auto simp: gal_res_compose\<close>)
qed

theorem galois_restriction_epimorphism:
  assumes onto: "galois_restriction K E F ` field_auto K F = field_auto E F"
  shows "group_epimorphism (galois_restriction K E F)
      (field_auto K F) (compose K) (identity K)
      (field_auto E F) (compose E) (identity E)"
proof -
  have hom: "group_homomorphism (galois_restriction K E F)
      (field_auto K F) (compose K) (identity K)
      (field_auto E F) (compose E) (identity E)"
    by (unfold galois_restriction_def; rule galois_restriction_hom)
  interpret H: group_homomorphism "galois_restriction K E F"
      "field_auto K F" "compose K" "identity K"
      "field_auto E F" "compose E" "identity E"
    by (rule hom)
  interpret S: surjective_map "galois_restriction K E F"
      "field_auto K F" "field_auto E F"
    by unfold_locales (rule onto)
  show ?thesis
  proof (rule group_epimorphism.intro)
    show "group_homomorphism (galois_restriction K E F)
        (field_auto K F) (compose K) (identity K)
        (field_auto E F) (compose E) (identity E)"
      by (rule hom)
    show "Monoid_epimorphism (galois_restriction K E F)
        (field_auto K F) (compose K) (identity K)
        (field_auto E F) (compose E) (identity E)"
      by (rule Monoid_epimorphism.intro[OF H.Monoid_homomorphism_axioms S.surjective_map_axioms])
  qed
qed

theorem galois_restriction_Ker:
  "group_homomorphism.Ker (restrict (\<lambda>\<sigma>. restrict \<sigma> E) (field_auto K F))
      (field_auto K F) (identity E) = field_auto K E"
proof -
  interpret H: group_homomorphism "restrict (\<lambda>\<sigma>. restrict \<sigma> E) (field_auto K F)"
      "field_auto K F" "compose K" "identity K" "field_auto E F" "compose E" "identity E"
    by (rule galois_restriction_hom)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix \<sigma> assume mem: "\<sigma> \<in> H.Ker"
    then have sF: "\<sigma> \<in> field_auto K F" by (rule H.Ker_closed)
    have "restrict (\<lambda>\<sigma>. restrict \<sigma> E) (field_auto K F) \<sigma> = identity E"
      using mem by (rule H.Ker_image)
    then have "restrict \<sigma> E = identity E" using sF by simp
    then show "\<sigma> \<in> field_auto K E"
      using sF unfolding field_auto_mem_iff by (metis restrict_apply')
  next
    fix \<sigma> assume sE: "\<sigma> \<in> field_auto K E"
    have fixE: "\<And>x. x \<in> E \<Longrightarrow> \<sigma> x = x"
      using sE by (auto simp: field_auto_mem_iff)
    have sF: "\<sigma> \<in> field_auto K F"
      using sE FE by (auto simp: field_auto_mem_iff)
    then show "\<sigma> \<in> H.Ker"
      by (metis (no_types, lifting) H.Ker_memI fixE restrict_apply' restrict_ext)
  qed
qed

text \<open>The standard first-isomorphism theorem applies to this generic restriction map.\<close>
interpretation restriction_core: group_homomorphism
    "galois_restriction K E F"
    "field_auto K F" "compose K" "identity K"
    "field_auto E F" "compose E" "identity E"
proof -
  show "group_homomorphism (galois_restriction K E F)
      (field_auto K F) (compose K) (identity K)
      (field_auto E F) (compose E) (identity E)"
    by (unfold galois_restriction_def; rule galois_restriction_hom)
qed

theorem galois_restriction_factor_isomorphism:
  "(restriction_core.kernel.Factor_Group,
     restriction_core.kernel.quotient_composition,
     restriction_core.kernel.Class (identity K)) \<cong>\<^sub>G
    (galois_restriction K E F ` field_auto K F, compose E, identity E)"
  by (rule restriction_core.first_isomorphism)

subsection \<open>The inductive step: solvability climbs the tower\<close>

text \<open>With @{term E} stable, solvability of the relative kernel and the intermediate-field
  automorphism group implies solvability of the full automorphism group.  The restriction map is
  corestricted to its image; the group quotient is handled by the standard first-isomorphism
  machinery.\<close>
theorem galois_solvable_tower_step:
  assumes solvKE: "Group.solvable (field_auto K E) (compose K) (identity K)"
    and solvEF: "Group.solvable (field_auto E F) (compose E) (identity E)"
  shows "Group.solvable (field_auto K F) (compose K) (identity K)"
proof -
  define \<eta> where "\<eta> = galois_restriction K E F"
  interpret H: group_homomorphism \<eta>
      "field_auto K F" "compose K" "identity K" "field_auto E F" "compose E" "identity E"
    unfolding \<eta>_def galois_restriction_def by (rule galois_restriction_hom)
  interpret I: group_epimorphism \<eta>
      "field_auto K F" "compose K" "identity K" "\<eta> ` field_auto K F" "compose E" "identity E"
    by unfold_locales (auto simp: H.commutes_with_composition)
  have Ker_eq: "I.Ker = field_auto K E"
    using galois_restriction_Ker
    unfolding \<eta>_def galois_restriction_def I.Ker_def H.Ker_def by simp
  have solvKer: "Group.solvable I.Ker (compose K) (identity K)"
    using Ker_eq solvKE by simp
  have solvImage: "Group.solvable (\<eta> ` field_auto K F) (compose E) (identity E)"
  proof (rule Group.solvable_subgroup)
    show "Group (field_auto E F) (compose E) (identity E)"
      by (rule field_auto_group[OF sfE FE])
    show "Subgroup (\<eta> ` field_auto K F) (field_auto E F)
        (compose E) (identity E)"
      by (rule H.image.Subgroup_axioms)
    show "Group.solvable (field_auto E F) (compose E) (identity E)"
      by (rule solvEF)
  qed
  show ?thesis
    using I.solvable_extension solvImage solvKer
    by blast
qed

end

subsection \<open>Complex splitting-field extension of generic restriction\<close>

text \<open>Surjectivity of restriction for a generated root field.  Let \<open>F \<subseteq> E \<subseteq> K\<close> with
  @{term K} generated by @{term E} and the roots of an @{term F}-polynomial.  The finite
  homomorphism-extension theorem supplies an extension of every @{term F}-automorphism of @{term E}.
\<close>
theorem galois_restriction_surjective:
  fixes K E F :: "'a :: field set" and Phi :: "'a poly"
  assumes sfE: "Subfield E" and sfF: "Subfield F" and FE: "F \<subseteq> E"
    and Phi: "Phi \<in> poly_over F"
    and Kdef: "K = generate_field (E \<union> {r. poly Phi r = 0})"
    and finR: "finite {r. poly Phi r = 0}"
    and algR: "\<And>r. poly Phi r = 0 \<Longrightarrow> algebraic_over E r"
    and closed: "\<And>q :: 'a poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
    and t: "\<tau> \<in> field_auto E F"
  shows "\<exists>\<sigma> \<in> field_auto K F. \<forall>x \<in> E. \<sigma> x = \<tau> x"
proof -
  define R where "R = {r. poly Phi r = 0}"
  have EK: "E \<subseteq> K" using Kdef by (auto simp: subset_generate_field)
  have sfK: "Subfield K" unfolding Kdef by (rule subfield_generate_field)
  have FK: "F \<subseteq> K" using FE EK by simp
  have homt: "field_hom_on E \<tau>" using sfE t by (rule field_auto_imp_field_hom_on)
  have fixFt: "\<And>x. x \<in> F \<Longrightarrow> \<tau> x = x" using t by (auto simp: field_auto_mem_iff)
  \<comment> \<open>Extend @{term \<tau>} over the finite root set to a homomorphism @{term g} on @{term K}.\<close>
  have algRE: "\<And>r. r \<in> R \<Longrightarrow> algebraic_over E r" using algR by (simp add: R_def)
  obtain g where homg: "field_hom_on (generate_field (E \<union> R)) g"
    and gE: "\<And>x. x \<in> E \<Longrightarrow> g x = \<tau> x"
    using field_hom_on_extend_finite[OF closed finR[folded R_def] homt algRE] by blast
  have homgK: "field_hom_on K g" using homg by (simp add: Kdef R_def)
  have fixFg: "\<And>x. x \<in> F \<Longrightarrow> g x = x" using gE fixFt FE by auto
  have RK: "R \<subseteq> K" using EK unfolding Kdef R_def using subset_generate_field by blast
  have gR_sub: "g ` R \<subseteq> R"
    using hom_preserves_roots[OF homgK sfF FK fixFg Phi] RK
    by (auto simp: R_def)
  have injK: "inj_on g K" by (rule field_hom_on.inj_on[OF homgK])
  have gR: "g ` R = R"
    by (metis RK R_def endo_inj_surj finR gR_sub injK inj_on_subset)
  have gE_onto: "g ` E = E"
    by (metis bij_betw_imp_surj_on field_auto_mem_iff gE image_cong t)
  have gUn: "g ` (E \<union> R) = E \<union> R" using gE_onto gR by (simp add: image_Un)
  have gK: "g ` K = K"
    by (metis EK Kdef RK R_def field_hom_on.image_generate_field_eq gUn homgK sup.boundedI)
  have aut: "restrict g K \<in> field_auto K F"
    by (rule field_hom_on_imp_field_auto[OF homgK gK fixFg FK])
  then show ?thesis using aut
    by (metis EK gE in_mono restrict_def)
qed

subsection \<open>A normal solvable tower has a solvable Galois group\<close>

text \<open>Given a fixed complex splitting field @{term K} and a chain
  of intermediate fields \<open>F = F\<^sub>0 \<subseteq> F\<^sub>1 \<subseteq> \<dots> \<subseteq> F\<^sub>n = K\<close> in which each \<open>F\<^sub>i\<close> is \<^emph>\<open>stable\<close> under
  @{term "field_auto K F"} and each step's relative Galois group \<open>field_auto F\<^sub>i\<^sub>+\<^sub>1 F\<^sub>i\<close> is
  solvable, the whole Galois group @{term "field_auto K F"} is solvable.  This chains the inductive
  step @{thm [source] galois_solvable_tower_step} down the tower, the base case being the trivial
  group @{term "field_auto K K"}.\<close>

subsubsection \<open>The trivial Galois group\<close>

text \<open>An automorphism of @{term K} fixing all of @{term K} is the identity, so @{term "field_auto K K"}
  is trivial.\<close>
lemma field_auto_self_trivial:
  fixes K :: "complex set"
  assumes K: "Subfield K"
  shows "field_auto K K = {identity K}"
proof -
  have cK: "complex_subfield K" using K by (simp add: complex_subfield_iff_subfield)
  have "\<sigma> \<in> {identity K}" if "\<sigma> \<in> field_auto K K" for \<sigma>
    by (metis that PiE_restrict field_auto_mem_iff insertI1 restrict_ext)
  then show ?thesis
    using cK identity_field_auto by auto
qed

lemma solvable_field_auto_self:
  fixes K :: "complex set"
  assumes K: "Subfield K"
  shows "Group.solvable (field_auto K K) (compose K) (identity K)"
proof -
  have cK: "complex_subfield K" using K by (simp add: complex_subfield_iff_subfield)
  interpret G: Group "field_auto K K" "compose K" "identity K"
    by (rule Galois_group_Group[OF cK subset_refl])
  show ?thesis unfolding G.solvable_def
    using G.derivedSeries.simps(1) assms field_auto_self_trivial by blast
qed

subsubsection \<open>Normal solvable towers\<close>

text \<open>@{term "solvable_tower K F Fs"}: the chain starting at @{term F} and following @{term Fs}, with
  fixed top @{term K}, in which every field is a subfield of @{term K}, every intermediate field is
  stable under @{term "field_auto K F"}, and every step has a solvable relative Galois group.  (The
  empty tower requires @{term "F = K"}.)\<close>
fun solvable_tower :: "complex set \<Rightarrow> complex set \<Rightarrow> complex set list \<Rightarrow> bool" where
  "solvable_tower K F [] \<longleftrightarrow> F = K"
| "solvable_tower K F (G # Gs) \<longleftrightarrow>
     Subfield F \<and> Subfield G \<and> F \<subseteq> G \<and> G \<subseteq> K \<and>
     (\<forall>\<sigma> \<in> field_auto K F. \<sigma> ` G = G) \<and>
     Group.solvable (field_auto G F) (compose G) (identity G) \<and>
     solvable_tower K G Gs"

subsubsection \<open>The assembly\<close>

text \<open>\<^emph>\<open>A normal solvable tower has a solvable Galois group.\<close>  By induction down the tower: the top
  @{term K} has the trivial (hence solvable) group @{term "field_auto K K"}; each step combines the
  solvable relative group @{term "field_auto G F"} with the solvable @{term "field_auto K G"} (from
  the induction hypothesis) via @{thm [source] galois_solvable_tower_step}, using stability of
  @{term G} under @{term "field_auto K F"}.\<close>
theorem solvable_tower_imp_solvable:
  assumes K: "Subfield K"
  shows "solvable_tower K F Fs \<Longrightarrow> Subfield F
           \<Longrightarrow> Group.solvable (field_auto K F) (compose K) (identity K)"
proof (induction Fs arbitrary: F)
  case Nil then show ?case
    by (metis solvable_field_auto_self solvable_tower.simps(1))
next
  case Cons
  then show ?case
    by (metis assms galois_solvable_tower_step solvable_tower.simps(2))
qed

end
