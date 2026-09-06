section \<open>The Galois Group Acts on the Roots\<close>

theory Galois_Action
  imports Galois_Transitivity Symmetric_Generation Sym_Not_Solvable
begin

text \<open>A field automorphism (an element of @{const field_auto}) is, in particular, a
  field homomorphism on its subfield domain.\<close>
lemma field_auto_imp_field_hom_on:
  assumes K: "Subfield K" and s: "\<sigma> \<in> field_auto K F"
  shows "field_hom_on K \<sigma>"
  using K s by (rule field_auto_as_hom)

text \<open>An automorphism fixing @{term F} maps a root in @{term K} of an @{term F}-polynomial to a
  root: it permutes the root set.\<close>
lemma field_auto_maps_root:
  assumes K: "Subfield K" and sfF: "Subfield F" and FK: "F \<subseteq> K"
    and s: "\<sigma> \<in> field_auto K F" and Phi: "Phi \<in> poly_over F"
    and r: "r \<in> K" and root: "poly Phi r = 0"
  shows "poly Phi (\<sigma> r) = 0"
  using hom_preserves_roots[OF field_auto_imp_field_hom_on sfF FK _ Phi r root]
  using K field_auto_mem_iff s by blast

text \<open>The Galois group acts on the root set by restriction.  We package this as a
  @{locale Group_Action} of @{term "field_auto K F"} on the finite root set @{term X}.\<close>

context
  fixes K F :: "complex set" and Phi :: "complex poly" and X :: "complex set"
  assumes K: "Subfield K" and sfF: "Subfield F" and FK: "F \<subseteq> K"
    and Phi: "Phi \<in> poly_over F"
    and Xdef: "X = {r. poly Phi r = 0}" and XK: "X \<subseteq> K" and finX: "finite X"
begin

lemma field_auto_image_root_subset:
  assumes s: "\<sigma> \<in> field_auto K F"
  shows "\<sigma> ` X \<subseteq> X"
  using FK K Phi XK Xdef field_auto_maps_root s sfF by blast

lemma field_auto_bij_on_root:
  assumes s: "\<sigma> \<in> field_auto K F"
  shows "bij_betw \<sigma> X X"
  unfolding bij_betw_def
proof 
  show "inj_on \<sigma> X" using XK
    by (meson bij_betw_imp_inj_on field_auto_mem_iff inj_on_subset s)
  show "\<sigma> ` X = X"
    by (meson \<open>inj_on \<sigma> X\<close> endo_inj_surj field_auto_image_root_subset finX s)
qed

lemma ga_sym:
  assumes s: "\<sigma> \<in> field_auto K F"
  shows "restrict \<sigma> X \<in> transformations.Sym X"
  by (simp add: bij_betw_imp_funcset field_auto_bij_on_root s transformations.Units_bij_betwD)

lemma ga_compose:
  assumes s: "\<sigma> \<in> field_auto K F" and t: "\<tau> \<in> field_auto K F"
  shows "restrict (compose K \<sigma> \<tau>) X = compose X (restrict \<sigma> X) (restrict \<tau> X)"
  using assms XK field_auto_image_root_subset by (fastforce simp: compose_def)

lemma ga_unit: "restrict (identity K) X = identity X"
  using XK by force

lemma galois_group_action:
  "Group_Action (field_auto K F) (compose K) (identity K) (\<lambda>\<sigma>. restrict \<sigma> X) X"
proof -
  have cK: "complex_subfield K" using K by (simp add: complex_subfield_iff_subfield)
  interpret G: Group "field_auto K F" "compose K" "identity K"
    by (rule Galois_group_Group[OF cK FK])
  show ?thesis
    by unfold_locales (use ga_sym ga_compose ga_unit in blast)+
qed

text \<open>\<^emph>\<open>The Galois group is finite\<close> when @{term K} is the splitting field @{term "gen_subfield (F \<union> X)"}
  of @{term Phi}: the action on the finite root set @{term X} is faithful (by
  @{thm [source] field_auto_faithful}, an automorphism fixing @{term X} pointwise is the identity),
  so @{term "field_auto K F"} embeds into the finite symmetric group @{term "transformations.Sym X"}.\<close>
lemma finite_field_auto:
  assumes Kgen: "K = gen_subfield (F \<union> X)"
  shows "finite (field_auto K F)"
proof -
  interpret GA: Group_Action "field_auto K F" "compose K" "identity K" "\<lambda>\<sigma>. restrict \<sigma> X" X
    by (rule galois_group_action)
  have cK: "complex_subfield K" using K by (simp add: complex_subfield_iff_subfield)
  \<comment> \<open>The action on the roots is faithful.\<close>
  have faith: "GA.faithful"
    unfolding GA.faithful_def
  proof (intro ballI impI)
    fix \<sigma> assume s: "\<sigma> \<in> field_auto K F" and triv: "\<forall>x\<in>X. restrict \<sigma> X x = x"
    have sext: "\<sigma> \<in> K \<rightarrow>\<^sub>E K" using s by (simp only: field_auto_mem_iff)
    show "\<sigma> = identity K"
      using field_auto_faithful[OF cK Kgen s]
      by (metis PiE_restrict restrict_apply' restrict_ext sext triv)
  qed
    \<comment> \<open>Faithfulness gives an injection into the finite symmetric group on @{term X}.\<close>
  have inj0: "inj_on (restrict (\<lambda>\<sigma>. restrict \<sigma> X) (field_auto K F)) (field_auto K F)"
    using faith by (rule GA.faithful_inj)
  have inj: "inj_on (\<lambda>\<sigma>. restrict \<sigma> X) (field_auto K F)"
    using inj0 inj_on_restrict_eq by blast
  have finSym: "finite (transformations.Sym X)"
    by (metis GA.mem_UnitsD finX finite_PiE finite_subset subsetI)
  show ?thesis using inj GA.hom_closed finSym inj_on_finite by blast
qed

end

text \<open>Transitivity of the Galois action on the roots of an irreducible polynomial: any root
  is carried to any other by some @{term F}-automorphism (via @{thm [source]
  galois_transitive_irreducible} and the bridge @{thm [source] field_hom_on_imp_field_auto}).\<close>
lemma galois_action_transitive:
  fixes F :: "complex set" and Phi :: "complex poly" and X :: "complex set"
  assumes sfF: "Subfield F"
    and finX: "finite X"
    and Phi: "Phi \<in> poly_over F"
    and irr: "irreducible_over F Phi"
    and Xdef: "X = {r. poly Phi r = 0}"
    and closed: "\<And>q :: complex poly. 0 < degree q \<Longrightarrow> \<exists>b. poly q b = 0"
    and a: "a \<in> X" and b: "b \<in> X"
  defines "K \<equiv> generate_field (F \<union> X)"
  shows "\<exists>\<sigma>\<in>field_auto K F. restrict \<sigma> X a = b"
proof -
  have phinz: "Phi \<noteq> 0" using irr by (simp add: irreducible_over_def)
  have algX: "algebraic_over F r" if "r \<in> X" for r
    using that Phi phinz Xdef unfolding algebraic_over_def by auto
  have XK: "X \<subseteq> K" unfolding K_def using subset_generate_field by blast
  have aK: "a \<in> K" using a XK by blast
  obtain \<sigma> where hom: "field_hom_on K \<sigma>" and sab: "\<sigma> a = b"
    and fixF: "\<forall>x\<in>F. \<sigma> x = x" and onto: "\<sigma> ` K = K"
    using galois_transitive_irreducible[OF sfF finX algX Phi irr Xdef closed a b]
    unfolding K_def by blast
  have FK: "F \<subseteq> K" unfolding K_def using subset_generate_field by blast
  have aut: "restrict \<sigma> K \<in> field_auto K F"
    using field_hom_on_imp_field_auto[OF hom onto _ FK] fixF by blast
  have "restrict (restrict \<sigma> K) X a = b"
    using aK a sab XK by simp
  then show ?thesis using aut by blast
qed

end
