section \<open>Module homomorphisms\<close>

theory Module_Homomorphism
  imports Module_Basics
begin

text \<open>A \<^emph>\<open>module homomorphism\<close> (over a fixed ring @{term R}) is a map @{term \<eta>} between @{term R}-modules
  that is additive and commutes with scaling.  This mirrors the group and ring homomorphism locales of
  theories \<open>Group_Theory\<close> and \<open>Ring_Theory\<close>, with the extra axiom linking the two scaling operations.
  We develop the kernel, image, and the injectivity criterion @{text "Ker = {0}"}.\<close>

text \<open>The import of \<open>FiniteProduct\<close> (through \<open>Module\<close>) re-merges HOL's @{text "+"}/@{text "-"} concrete
  syntax alongside the ring locale's, which is harmless in term positions (type inference disambiguates)
  but ambiguous in a locale-header instantiation argument.  We therefore remove the HOL syntax again, as
  \<open>Ring_Theory\<close> does, so that within this theory @{text "+"} unambiguously denotes the ring's addition.\<close>
no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

text \<open>A module homomorphism fixes a \<^emph>\<open>single\<close> scalar ring @{term R} and two @{term R}-modules --- the source
  @{term M} and the target @{term M'} --- sharing that ring.  The ring parameters \<open>+ \<cdot> \<zero> \<one>\<close> appear once in
  the \<open>for\<close> clause and are threaded verbatim into both module interpretations, so no token is bound twice.\<close>
locale module_homomorphism =
  source: Module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" +
  target: Module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" M' "(\<odot>\<^sub>2)" +
  map \<eta> M M'
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
    and M and madd (infixl \<open>\<oplus>\<close> 65) and mzero (\<open>\<zero>\<^sub>M\<close>) and scale (infixr \<open>\<odot>\<close> 75)
    and M' and madd' (infixl \<open>\<oplus>\<^sub>2\<close> 65) and mzero' (\<open>\<zero>\<^sub>2\<close>) and scale' (infixr \<open>\<odot>\<^sub>2\<close> 75)
    and \<eta> +
  assumes hom_add: "\<lbrakk> u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> \<eta> (u \<oplus> v) = \<eta> u \<oplus>\<^sub>2 \<eta> v"
    and hom_scale: "\<lbrakk> a \<in> R; v \<in> M \<rbrakk> \<Longrightarrow> \<eta> (a \<odot> v) = a \<odot>\<^sub>2 \<eta> v"
begin

subsection \<open>Basic properties\<close>

lemma hom_closed: "v \<in> M \<Longrightarrow> \<eta> v \<in> M'"
  using graph by (auto simp: PiE_iff)

lemma hom_zero: "\<eta> \<zero>\<^sub>M = \<zero>\<^sub>2"
proof -
  have "\<eta> \<zero>\<^sub>M = \<eta> (\<zero> \<odot> \<zero>\<^sub>M)" using source.scale_zero_scalar by simp
  also have "\<dots> = \<zero>\<^sub>2"
    by (simp add: hom_scale target.scale_zero_scalar)
  finally show ?thesis .
qed

lemma hom_neg:
  assumes v: "v \<in> M" shows "\<eta> (source.madd.inverse v) = target.madd.inverse (\<eta> v)"
proof -
  define n where "n = source.additive.inverse \<one>"
  \<comment> \<open>The module negation is scaling by the ring's additive inverse of @{term \<one>}.\<close>
  have sneg: "source.madd.inverse v = n \<odot> v"
    unfolding n_def using v by (simp add: source.scale_neg_scalar source.scale_one)
  have tneg: "target.madd.inverse (\<eta> v) = n \<odot>\<^sub>2 \<eta> v"
    unfolding n_def using hom_closed[OF v] by (simp add: target.scale_neg_scalar target.scale_one)
  show ?thesis
    by (simp add: hom_scale n_def sneg tneg v)
qed

text \<open>A module homomorphism commutes with finite linear combinations.  The target sum remains
  indexed by the source vectors; reindexing it over their images additionally requires injectivity
  on the chosen index set.\<close>

lemma hom_lincomb:
  assumes finA: "finite A" and AM: "A \<subseteq> M"
    and c: "\<And>v. v \<in> A \<Longrightarrow> c v \<in> R"
  shows "\<eta> (source.lincomb c A) =
    target.madd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) A"
  using finA AM c
proof (induction A rule: finite_induct)
  case empty
  then show ?case unfolding source.lincomb_def by (simp add: hom_zero)
next
  case (insert v A)
  have vM: "v \<in> M" and AM: "A \<subseteq> M" and cv: "c v \<in> R"
    using insert.prems by auto
  have cA: "\<And>u. u \<in> A \<Longrightarrow> c u \<in> R" using insert.prems by auto
  have source_terms: "(\<lambda>u. c u \<odot> u) \<in> A \<rightarrow> M"
    using AM cA by (auto intro!: source.scale_closed)
  have target_terms: "(\<lambda>u. c u \<odot>\<^sub>2 \<eta> u) \<in> A \<rightarrow> M'"
    using AM cA
    by (auto intro!: target.scale_closed hom_closed)
  have "source.lincomb c (insert v A) = (c v \<odot> v) \<oplus> source.lincomb c A"
    unfolding source.lincomb_def
    using insert.hyps source_terms cv vM by (simp add: source.scale_closed)
  then have "\<eta> (source.lincomb c (insert v A)) =
      \<eta> (c v \<odot> v) \<oplus>\<^sub>2 \<eta> (source.lincomb c A)"
    using cv vM AM cA
    by (simp add: hom_add source.scale_closed source.lincomb_closed)
  also have "\<eta> (c v \<odot> v) = c v \<odot>\<^sub>2 \<eta> v" using cv vM by (rule hom_scale)
  also have "\<eta> (source.lincomb c A) =
      target.madd.fincomp (\<lambda>u. c u \<odot>\<^sub>2 \<eta> u) A"
    using insert.IH[OF AM cA] .
  also have "(c v \<odot>\<^sub>2 \<eta> v) \<oplus>\<^sub>2
      target.madd.fincomp (\<lambda>u. c u \<odot>\<^sub>2 \<eta> u) A =
      target.madd.fincomp (\<lambda>u. c u \<odot>\<^sub>2 \<eta> u) (insert v A)"
    using insert.hyps target_terms cv vM
    by (auto intro!: target.madd.fincomp_insert[symmetric] target.scale_closed hom_closed)
  finally show ?case .
qed

subsection \<open>Composition and inverses\<close>

text \<open>Composition is restricted to the source carrier, preserving the extensional-map
  convention used throughout the set-based algebra hierarchy.\<close>
theorem compose_module_homomorphism:
  assumes second_hom: "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
    M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) N nadd nzero nscale \<theta>"
  shows "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
    M (\<oplus>) \<zero>\<^sub>M (\<odot>) N nadd nzero nscale (compose M \<theta> \<eta>)"
proof -
  interpret second: module_homomorphism R "(+)" "(\<cdot>)" \<zero> \<one>
    M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" N nadd nzero nscale \<theta>
    by (rule second_hom)
  show ?thesis
  proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
    show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)"
      by (rule source.Module_axioms)
    show "Module R (+) (\<cdot>) \<zero> \<one> nadd nzero N nscale"
      by (rule second.target.Module_axioms)
    show "compose M \<theta> \<eta> \<in> M \<rightarrow>\<^sub>E N"
      using graph second.graph by (auto simp: PiE_iff compose_def)
  next
    fix u v assume uv: "u \<in> M" "v \<in> M"
      then show "compose M \<theta> \<eta> (u \<oplus> v) =
        nadd (compose M \<theta> \<eta> u) (compose M \<theta> \<eta> v)"
      by (simp add: compose_def hom_add second.hom_add hom_closed)
  next
    fix a v assume av: "a \<in> R" "v \<in> M"
    then show "compose M \<theta> \<eta> (a \<odot> v) =
        nscale a (compose M \<theta> \<eta> v)"
      by (simp add: compose_def hom_scale second.hom_scale hom_closed source.scale_closed)
  qed
qed

text \<open>The inverse of a bijective homomorphism is again restricted to its source carrier.
  This is essential: a raw \<open>inv_into\<close> does not satisfy the repository's extensional-map
  convention away from the carrier.\<close>
theorem inverse_module_homomorphism:
  assumes bij: "bij_betw \<eta> M M'"
  shows "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
    M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
    M (\<oplus>) \<zero>\<^sub>M (\<odot>) (restrict (inv_into M \<eta>) M')"
proof -
  interpret iso: bijective_map \<eta> M M'
    by unfold_locales (rule bij)
  show ?thesis
  proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
    show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>\<^sub>2) \<zero>\<^sub>2 M' (\<odot>\<^sub>2)"
      by (rule target.Module_axioms)
    show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)"
      by (rule source.Module_axioms)
    show "restrict (inv_into M \<eta>) M' \<in> M' \<rightarrow>\<^sub>E M"
      by (rule iso.inverse.graph)
  next
    fix x y assume xy: "x \<in> M'" "y \<in> M'"
    then obtain u v where uv: "u \<in> M" "v \<in> M" "\<eta> u = x" "\<eta> v = y"
      using bij_betw_imp_surj_on[OF bij] by blast
    then show "restrict (inv_into M \<eta>) M' (x \<oplus>\<^sub>2 y) =
        restrict (inv_into M \<eta>) M' x \<oplus> restrict (inv_into M \<eta>) M' y"
      using xy bij by (auto simp: inv_into_f_eq hom_add)
  next
    fix a x assume ax: "a \<in> R" "x \<in> M'"
    then obtain v where v: "v \<in> M" "\<eta> v = x"
      using bij_betw_imp_surj_on[OF bij] by blast
    have av: "a \<odot> v \<in> M" using ax(1) v(1) by (rule source.scale_closed)
    have image: "\<eta> (a \<odot> v) = a \<odot>\<^sub>2 x"
      using ax v by (simp add: hom_scale)
    have inverse_image: "inv_into M \<eta> (a \<odot>\<^sub>2 x) = a \<odot> v"
      using bij av image by (metis bij_betw_inv_into_left)
    have inverse_x: "inv_into M \<eta> x = v"
      using bij v by (metis bij_betw_inv_into_left)
    have target_ax: "a \<odot>\<^sub>2 x \<in> M'"
      using ax by (rule target.scale_closed)
    show "restrict (inv_into M \<eta>) M' (a \<odot>\<^sub>2 x) =
        a \<odot> restrict (inv_into M \<eta>) M' x"
      using ax inverse_image inverse_x target_ax by simp
  qed
qed

lemma inverse_module_homomorphism_left:
  assumes bij: "bij_betw \<eta> M M'" and x: "x \<in> M"
  shows "restrict (inv_into M \<eta>) M' (\<eta> x) = x"
  using bij x hom_closed by (simp add: bij_betw_inv_into_left)

lemma inverse_module_homomorphism_right:
  assumes bij: "bij_betw \<eta> M M'" and y: "y \<in> M'"
  shows "\<eta> (restrict (inv_into M \<eta>) M' y) = y"
  using bij y by (simp add: bij_betw_inv_into_right)

corollary inverse_module_isomorphism:
  assumes bij: "bij_betw \<eta> M M'"
  shows "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2)
      M (\<oplus>) \<zero>\<^sub>M (\<odot>) (restrict (inv_into M \<eta>) M')
    \<and> bij_betw (restrict (inv_into M \<eta>) M') M' M"
  using bij inverse_module_homomorphism by (simp add: bij_betw_inv_into)

subsection \<open>The kernel\<close>

definition Ker :: "'b set"
  where "Ker = {v \<in> M. \<eta> v = \<zero>\<^sub>2}"

lemma Ker_subset: "Ker \<subseteq> M"
  by (auto simp: Ker_def)

lemma Ker_mem: "v \<in> Ker \<Longrightarrow> v \<in> M" 
  by (simp add: Ker_def)

lemma Ker_image: "v \<in> Ker \<Longrightarrow> \<eta> v = \<zero>\<^sub>2" 
  by (simp add: Ker_def)

lemma Ker_memI: "\<lbrakk> \<eta> v = \<zero>\<^sub>2; v \<in> M \<rbrakk> \<Longrightarrow> v \<in> Ker" 
  by (simp add: Ker_def)

text \<open>The kernel is a submodule of the source.\<close>
theorem Ker_submodule: "source.submodule Ker"
proof (intro source.submoduleI Ker_subset)
  show "\<zero>\<^sub>M \<in> Ker" by (simp add: Ker_def hom_zero)
next
  fix u v assume u: "u \<in> Ker" and v: "v \<in> Ker"
  have uM: "u \<in> M" and vM: "v \<in> M" using u v by (auto simp: Ker_def)
  show "u \<oplus> v \<in> Ker"
    by (simp add: Ker_image Ker_memI hom_add u uM v vM) 
next
  show "\<And>a v. \<lbrakk>a \<in> R; v \<in> Ker\<rbrakk> \<Longrightarrow> a \<odot> v \<in> Ker"
    using Ker_def hom_scale source.scale_closed target.scale_zero_elem by auto
qed

subsection \<open>The image\<close>

text \<open>The image of @{term \<eta>} is a submodule of the target.\<close>
theorem image_submodule: "target.submodule (\<eta> ` M)"
proof (rule target.submoduleI)
  show "\<And>u v. \<lbrakk>u \<in> \<eta> ` M; v \<in> \<eta> ` M\<rbrakk> \<Longrightarrow> u \<oplus>\<^sub>2 v \<in> \<eta> ` M"
    by (smt (verit, ccfv_threshold) hom_add image_iff source.madd_closed)
  show "\<And>a v. \<lbrakk>a \<in> R; v \<in> \<eta> ` M\<rbrakk> \<Longrightarrow> a \<odot>\<^sub>2 v \<in> \<eta> ` M"
    by (metis hom_scale imageE image_subset_iff source.scale_closed subset_refl) 
qed (use hom_closed hom_zero in blast)+

subsection \<open>Injectivity criterion\<close>

text \<open>A module homomorphism is injective iff its kernel is trivial.\<close>
theorem injective_iff_kernel_trivial:
  "inj_on \<eta> M \<longleftrightarrow> Ker = {\<zero>\<^sub>M}"
proof
  assume inj: "inj_on \<eta> M"
  show "Ker = {\<zero>\<^sub>M}"
    using hom_zero inj inj_on_contraD by (fastforce simp: Ker_def hom_zero)
next
  assume ker: "Ker = {\<zero>\<^sub>M}"
  show "inj_on \<eta> M"
  proof (rule inj_onI)
    fix x y assume xy: "x \<in> M" "y \<in> M" and eq: "\<eta> x = \<eta> y"
    have diff: "x \<oplus> source.madd.inverse y \<in> M" using xy by auto
    have "\<eta> (x \<oplus> source.madd.inverse y) = \<eta> x \<oplus>\<^sub>2 \<eta> (source.madd.inverse y)"
      using xy by (simp add: hom_add)
    also have "\<dots> = \<zero>\<^sub>2"
      using xy eq by (simp add: hom_neg)
    finally have z: "x \<oplus> source.madd.inverse y = \<zero>\<^sub>M"
      using Ker_memI diff ker by blast 
    \<comment> \<open>Cancel: \<open>x \<oplus> (- y) = \<zero>\<^sub>M\<close> forces @{term "x = y"}.\<close>
    have "source.madd.inverse y \<oplus> y = \<zero>\<^sub>M"
      using xy(2) by (simp add: source.madd.invertible_left_inverse)
    then show "x = y"
      using source.madd.inverse_unique xy z by blast 
  qed
qed

end

context Module
begin

text \<open>The carrier-restricted identity is the identity morphism in the extensional-map
  representation.\<close>
theorem identity_module_homomorphism:
  "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
    M (\<oplus>) \<zero>\<^sub>M (\<odot>) M (\<oplus>) \<zero>\<^sub>M (\<odot>) (identity M)"
proof (intro module_homomorphism.intro map.intro module_homomorphism_axioms.intro)
  show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)"
    by (rule Module_axioms)
  show "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)"
    by (rule Module_axioms)
  show "identity M \<in> M \<rightarrow>\<^sub>E M" by simp
next
  fix u v assume "u \<in> M" "v \<in> M"
  then show "identity M (u \<oplus> v) = identity M u \<oplus> identity M v"
    by (simp add: madd_closed)
next
  fix a v assume "a \<in> R" "v \<in> M"
  then show "identity M (a \<odot> v) = a \<odot> identity M v"
    by (simp add: scale_closed)
qed

end

end
