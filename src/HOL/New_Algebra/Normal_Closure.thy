section \<open>Stability of root-generated intermediate fields\<close>

theory Normal_Closure
  imports Galois_Solvable_Tower Radical_Extension
begin

text \<open>The @{const solvable_tower} predicate of \<open>Galois_Solvable_Tower\<close>
  requires each intermediate field to be
  \<^emph>\<open>stable\<close> under the ambient Galois group.  The reusable fact that supplies this is: a field
  @{term "generate_field (F \<union> X)"} generated over @{term F} by the \<^emph>\<open>full\<close> root set @{term X} of an
  @{term F}-polynomial is stable under every @{term F}-automorphism of any ambient field @{term K}
  containing it.\<close>

subsection \<open>An automorphism fixes the base field setwise\<close>

text \<open>An @{term F}-automorphism of @{term K} maps @{term F} onto @{term F}: it fixes @{term F}
  pointwise, and every element of @{term F} is the image of itself.\<close>
lemma field_auto_image_base:
  assumes s: "\<sigma> \<in> field_auto K F"
  shows "\<sigma> ` F = F"
proof -
  have base_fix: "\<forall>x. x \<in> F \<longrightarrow> \<sigma> x = x"
    using s by (auto simp: field_auto_mem_iff)
  have image_subset: "\<sigma> ` F \<subseteq> F"
  proof (rule subsetI)
    fix y
    assume y_image: "y \<in> \<sigma> ` F"
    obtain x where xF: "x \<in> F" and y_eq: "\<sigma> x = y"
      using y_image by blast
    have sigma_fix: "\<sigma> x = x" using base_fix xF by blast
    then show "y \<in> F" using xF y_eq by simp
  qed
  have subset_image: "F \<subseteq> \<sigma> ` F"
  proof (rule subsetI)
    fix x
    assume xF: "x \<in> F"
    have "\<sigma> x \<in> \<sigma> ` F" using xF by (rule imageI)
    then show "x \<in> \<sigma> ` F" using base_fix xF by simp
  qed
  show ?thesis by (rule subset_antisym[OF image_subset subset_image])
qed

subsection \<open>Root-generated fields are stable\<close>

text \<open>\<^emph>\<open>The stability lemma.\<close>  Let @{term X} be the full set of roots (in the ambient @{term K}) of an
  @{term F}-polynomial @{term Phi}, and let @{term "E = generate_field (F \<union> X)"} be the field it
  generates over @{term F}.  Then @{term E} is stable under every @{term F}-automorphism of @{term K}.\<close>
theorem root_generated_stable:
  fixes K F :: "complex set" and Phi :: "complex poly"
  assumes K: "Subfield K" and sfF: "Subfield F" and FK: "F \<subseteq> K"
    and Phi: "Phi \<in> poly_over F"
    and Xdef: "X = {r. poly Phi r = 0}" and XK: "X \<subseteq> K" and finX: "finite X"
    and s: "\<sigma> \<in> field_auto K F"
  shows "\<sigma> ` generate_field (F \<union> X) = generate_field (F \<union> X)"
proof -
  have hom: "field_hom_on K \<sigma>" using K s by (rule field_auto_imp_field_hom_on)
  \<comment> \<open>@{term \<sigma>} permutes the roots and fixes the base, so it fixes the generating set.\<close>
  have sX: "\<sigma> ` X = X"
    using field_auto_bij_on_root[OF K sfF FK Phi Xdef XK finX s] by (rule bij_betw_imp_surj_on)
  have sF: "\<sigma> ` F = F" by (rule field_auto_image_base[OF s])
  have sUn: "\<sigma> ` (F \<union> X) = F \<union> X"
    using sF sX by (simp add: image_Un)
  \<comment> \<open>The generating set lies in @{term K}, and generation commutes with the homomorphism.\<close>
  have "F \<union> X \<subseteq> K" using FK XK by simp
  then show ?thesis
    using field_hom_on.image_generate_field_eq[OF hom] sUn by presburger
qed

subsection \<open>A field homomorphism carries radical steps to radical steps\<close>

text \<open>A conjugate of a radical is a radical\<close>
lemma radical_step_image:
  fixes f :: "complex \<Rightarrow> complex"
  assumes hom: "field_hom_on K f" and sfF: "Subfield F" and FK: "F \<subseteq> K"
    and fixF: "\<And>x. x \<in> F \<Longrightarrow> f x = x"
    and step: "radical_step F G" and GK: "G \<subseteq> K"
  shows "radical_step F (f ` G)"
proof -
  obtain a n where n: "n > 0" and anF: "a ^ n \<in> F" and Gdef: "G = generate_field (F \<union> {a})"
    using step by (auto simp: radical_step_def)
  \<comment> \<open>@{term a} lies in @{term "G \<subseteq> K"}, and @{term F} is fixed setwise.\<close>
  have aK: "a \<in> K" using Gdef GK subset_generate_field by fastforce
  \<comment> \<open>The image of the radical is again a radical: @{term "(f a) ^ n \<in> F"}.\<close>
  have fanF: "(f a) ^ n \<in> F" 
    using aK field_hom_on.hom_power[OF hom] anF fixF by fastforce
  \<comment> \<open>The image field is generated over @{term F} by the image radical @{term "f a"}.\<close>
  have "f ` G = generate_field (F \<union> {f a})" 
    using fixF FK aK field_hom_on.image_generate_field_eq[OF hom] by (simp add: Gdef image_Un)
  then show ?thesis unfolding radical_step_def using n fanF by blast
qed

text \<open>\<^emph>\<open>General form\<close> (no fixing hypothesis): a field homomorphism carries a radical step
  \<open>F \<leadsto> G\<close> to the radical step \<open>f ` F \<leadsto> f ` G\<close>.  This is the form that iterates
  along a tower, where after the first step the base is no longer fixed pointwise.\<close>
lemma radical_step_image_gen:
  fixes f :: "complex \<Rightarrow> complex"
  assumes hom: "field_hom_on K f" and FK: "F \<subseteq> K"
    and step: "radical_step F G" and GK: "G \<subseteq> K"
  shows "radical_step (f ` F) (f ` G)"
proof -
  obtain a n where n: "n > 0" and anF: "a ^ n \<in> F" and Gdef: "G = generate_field (F \<union> {a})"
    using step by (auto simp: radical_step_def)
  have aK: "a \<in> K" using Gdef GK subset_generate_field by fastforce
  \<comment> \<open>@{term "f a"} is a radical over @{term "f ` F"}: \<open>(f a)\<^sup>n = f(a\<^sup>n) \<in> f ` F\<close>.\<close>
  have fanF: "(f a) ^ n \<in> f ` F" 
    using aK field_hom_on.hom_power[OF hom] by (metis anF imageI)
  have "f ` G = f ` generate_field (F \<union> {a})" by (simp add: Gdef)
  also have "\<dots> = generate_field (f ` F \<union> {f a})"
    using field_hom_on.image_generate_field_eq[OF hom] FK aK  by (simp add: image_Un)
  finally show ?thesis unfolding radical_step_def using n fanF by blast
qed

subsection \<open>A field homomorphism carries radical towers to radical towers\<close>

text \<open>Each field of a radical tower is a subfield (each is generated over the previous), and the tower
  is increasing.  In particular every field is contained in any subfield @{term K} that contains the
  \<^emph>\<open>top\<close> field --- but for the tower-image induction we only need that consecutive fields nest, which we
  package as: every field of the tower is a subfield of the last.  We instead carry an explicit ambient
  @{term K} with @{term "tower_top F Fs \<subseteq> K"}.\<close>
lemma radical_step_field:
  assumes "radical_step F G" shows "Subfield G \<and> F \<subseteq> G"
  using assms radical_step_def by auto

lemma radical_tower_subset_ambient:
  "Subfield K \<Longrightarrow> Subfield F \<Longrightarrow> radical_tower F Fs \<Longrightarrow> tower_top F Fs \<subseteq> K
     \<Longrightarrow> F \<subseteq> K \<and> (\<forall>G \<in> set Fs. G \<subseteq> K)"
proof (induction Fs arbitrary: F)
  case Nil
  then show ?case by simp
next
  case (Cons G Gs)
  have "radical_step F G" and tower': "radical_tower G Gs" using Cons.prems(3) by auto
  then have sfG: "Subfield G" and FG: "F \<subseteq> G"
    using radical_step_field by auto
  have topGs: "tower_top G Gs \<subseteq> K" using Cons.prems(4) by simp
  with Cons show ?case
    by (metis FG order_trans set_ConsD sfG tower')
qed

text \<open>\<^emph>\<open>A conjugate of a radical tower is a radical tower.\<close>  Applying a field homomorphism @{term f} to
  every field of a radical tower over @{term F} yields a radical tower over @{term "f ` F"}: each step
  maps to a step by @{thm [source] radical_step_image_gen}.\<close>
theorem radical_tower_image:
  fixes f :: "complex \<Rightarrow> complex"
  assumes K: "Subfield K" and hom: "field_hom_on K f"
  shows "Subfield F \<Longrightarrow> radical_tower F Fs \<Longrightarrow> tower_top F Fs \<subseteq> K
           \<Longrightarrow> radical_tower (f ` F) (List.map ((`) f) Fs)"
proof (induction Fs arbitrary: F)
  case Nil
  then show ?case by simp
next
  case (Cons G Gs)
  have step: "radical_step F G" and tower': "radical_tower G Gs" using Cons.prems(2) by auto
  have sfG: "Subfield G"
    using Cons.prems(1) local.step radical_step_field by blast
  \<comment> \<open>@{term F} and @{term G} live in @{term K}.\<close>
  have FK: "F \<subseteq> K" and GK: "G \<subseteq> K"
    using radical_tower_subset_ambient[OF K] Cons.prems sfG tower' tower_top_Cons
    by blast+
  show ?case
    using Cons.prems radical_step_image_gen[OF hom FK step GK] Cons.IH[OF sfG tower'] by simp
qed

subsection \<open>The top of a radical tower is a subfield containing the base\<close>

lemma subfield_tower_top:
  "Subfield F \<Longrightarrow> radical_tower F Fs \<Longrightarrow> Subfield (tower_top F Fs) \<and> F \<subseteq> tower_top F Fs"
  by (induction Fs arbitrary: F) (use radical_step_field in force)+

subsection \<open>Splicing a list of towers over a common base into one radical tower\<close>

text \<open>\<^emph>\<open>Base change of a tower onto a subfield containing the base.\<close>  If @{term F} is a subfield of the
  subfield @{term B}, a radical tower over @{term F} base-changes to a radical tower over @{term B}
  (not merely over @{term "generate_field (B \<union> F)"}): since @{term B} is a subfield containing
  @{term F}, @{term "generate_field (B \<union> F) = B"}.\<close>
lemma radical_tower_basechange_subfield:
  assumes B: "Subfield B" and FB: "F \<subseteq> B" and tower: "radical_tower F Fs"
  shows "radical_tower B (List.map (\<lambda>H. generate_field (B \<union> H)) Fs)"
  using B radical_tower_basechange[OF tower, of B]
  by (simp add: FB Un_absorb2 Subfield.generate_field_self)

text \<open>Validity of a family of towers each based at @{term F}.\<close>
fun all_towers_over :: "'a :: field set \<Rightarrow> 'a set list list \<Rightarrow> bool" where
  "all_towers_over F [] \<longleftrightarrow> True"
| "all_towers_over F (Ts # Tss) \<longleftrightarrow> radical_tower F Ts \<and> all_towers_over F Tss"

text \<open>\<^emph>\<open>Splice\<close> a family of towers (all based at @{term F}) into one list, base-changing each successive
  tower onto the running top @{term B}.  The accumulator @{term B} is the subfield reached so far.\<close>
fun spliced :: "'a :: field set \<Rightarrow> 'a set list list \<Rightarrow> 'a set list" where
  "spliced B [] = []"
| "spliced B (Ts # Tss) =
     (let Ts' = List.map (\<lambda>H. generate_field (B \<union> H)) Ts
      in Ts' @ spliced (tower_top B Ts') Tss)"

text \<open>Splicing a family of towers-over-@{term F} onto a subfield @{term B} containing @{term F} yields a
  radical tower over @{term B}.\<close>
lemma radical_tower_spliced:
  "Subfield B \<Longrightarrow> Subfield F \<Longrightarrow> F \<subseteq> B \<Longrightarrow> all_towers_over F Tss
     \<Longrightarrow> radical_tower B (spliced B Tss)"
proof (induction Tss arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons Ts Tss)
  define Ts' where "Ts' = List.map (\<lambda>H. generate_field (B \<union> H)) Ts"
  \<comment> \<open>The first tower, base-changed onto @{term B}, is a radical tower over @{term B}.\<close>
  have rtTs': "radical_tower B Ts'"
    unfolding Ts'_def
    using Cons.prems radical_tower_basechange_subfield by auto
  \<comment> \<open>Its top is a subfield containing @{term B} (hence @{term F}).\<close>
  define B' where "B' = tower_top B Ts'"
  have FB': "F \<subseteq> B'"
    using B'_def Cons.prems(1,3) rtTs' subfield_tower_top by blast
  \<comment> \<open>The remaining family splices onto @{term B'}, by the induction hypothesis.\<close>
  have "radical_tower B' (spliced B' Tss)"
    using B'_def Cons.IH Cons.prems FB' rtTs' subfield_tower_top by force
  then have "radical_tower B (Ts' @ spliced B' Tss)"
    using rtTs' by (simp add: B'_def radical_tower_append)
  then show ?case by (simp add: Ts'_def B'_def Let_def)
qed

subsection \<open>A radical tower is increasing; every field lies in the top\<close>

text \<open>Each field of a radical tower over @{term F} is contained in the top field: the tower is
  increasing (each step is a field extension, @{thm [source] radical_step_field}), so @{term F} and
  every listed field embed into @{term "tower_top F Fs"}.\<close>
lemma field_subset_tower_top:
  "Subfield F \<Longrightarrow> radical_tower F Fs \<Longrightarrow> F \<subseteq> tower_top F Fs \<and> (\<forall>H \<in> set Fs. H \<subseteq> tower_top F Fs)"
proof (induction Fs arbitrary: F)
  case Nil
  then show ?case by simp
next
  case (Cons G Gs)
  then show ?case
    by (meson equalityE radical_tower_subset_ambient subfield_tower_top)
qed

end
