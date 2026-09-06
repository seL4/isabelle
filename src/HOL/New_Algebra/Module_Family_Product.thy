section \<open>The direct product and direct sum of a family of modules\<close>

theory Module_Family_Product
  imports Module_Homomorphism
begin

no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

text \<open>The external direct product of a family of @{term R}-modules @{term "Mod i"} (@{term "i \<in> I"}): the
  carrier is the extensional dependent function space @{term "Pi\<^sub>E I Mod"} with pointwise addition and
  scaling.  As with the homomorphism locale, the scalar ring @{term R} is fixed \<^emph>\<open>once\<close> and shared by all
  the modules.  We show the product is an @{term R}-module, the projections are module homomorphisms, and
  the direct \<^emph>\<open>sum\<close> (elements of finite support) is a submodule of the product.\<close>

subsection \<open>The product locale\<close>

locale module_family =
  base: Ring R "(+)" "(\<cdot>)" \<zero> \<one>
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70) and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>) +
  fixes I :: "'i set"
    and Mod :: "'i \<Rightarrow> 'b set"
    and madd :: "'i \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"
    and mzero :: "'i \<Rightarrow> 'b"
    and scale :: "'i \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes mod: "\<And>i. i \<in> I \<Longrightarrow>
      Module R (+) (\<cdot>) \<zero> \<one> (madd i) (mzero i) (Mod i) (scale i)"
begin

lemma comp_module: "i \<in> I \<Longrightarrow> Module R (+) (\<cdot>) \<zero> \<one> (madd i) (mzero i) (Mod i) (scale i)"
  by (rule mod)

subsection \<open>Carrier and operations\<close>

definition Pcarrier :: "('i \<Rightarrow> 'b) set"
  where "Pcarrier = (\<Pi>\<^sub>E i\<in>I. Mod i)"

definition Padd :: "('i \<Rightarrow> 'b) \<Rightarrow> ('i \<Rightarrow> 'b) \<Rightarrow> ('i \<Rightarrow> 'b)" (infixl \<open>\<oplus>\<^sub>\<Pi>\<close> 65)
  where "x \<oplus>\<^sub>\<Pi> y = (\<lambda>i\<in>I. madd i (x i) (y i))"

definition Pzero :: "'i \<Rightarrow> 'b" (\<open>\<zero>\<^sub>\<Pi>\<close>)
  where "\<zero>\<^sub>\<Pi> = (\<lambda>i\<in>I. mzero i)"

definition Pscale :: "'a \<Rightarrow> ('i \<Rightarrow> 'b) \<Rightarrow> ('i \<Rightarrow> 'b)" (infixr \<open>\<odot>\<^sub>\<Pi>\<close> 75)
  where "a \<odot>\<^sub>\<Pi> x = (\<lambda>i\<in>I. scale i a (x i))"

lemma Pcarrier_memI:
  "\<lbrakk> \<And>i. i \<in> I \<Longrightarrow> x i \<in> Mod i; x \<in> extensional I \<rbrakk> \<Longrightarrow> x \<in> Pcarrier"
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcarrier_component: "\<lbrakk> x \<in> Pcarrier; i \<in> I \<rbrakk> \<Longrightarrow> x i \<in> Mod i"
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcarrier_extensional: "x \<in> Pcarrier \<Longrightarrow> x \<in> extensional I"
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcarrier_eqI:
  "\<lbrakk> x \<in> Pcarrier; y \<in> Pcarrier; \<And>i. i \<in> I \<Longrightarrow> x i = y i \<rbrakk> \<Longrightarrow> x = y"
  by (metis Pcarrier_extensional extensionalityI)

lemma Padd_apply: "i \<in> I \<Longrightarrow> (x \<oplus>\<^sub>\<Pi> y) i = madd i (x i) (y i)" 
  by (simp add: Padd_def)

lemma Pzero_apply: "i \<in> I \<Longrightarrow> \<zero>\<^sub>\<Pi> i = mzero i" 
  by (simp add: Pzero_def)

lemma Pscale_apply: "i \<in> I \<Longrightarrow> (a \<odot>\<^sub>\<Pi> x) i = scale i a (x i)" 
  by (simp add: Pscale_def)

lemma Padd_closed [intro, simp]:
  assumes "x \<in> Pcarrier" "y \<in> Pcarrier" shows "x \<oplus>\<^sub>\<Pi> y \<in> Pcarrier"
proof (rule Pcarrier_memI)
  fix i assume i: "i \<in> I"
  interpret Mi: Module R "(+)" "(\<cdot>)" \<zero> \<one> "madd i" "mzero i" "Mod i" "scale i"
    using i by (rule mod)
  show "(x \<oplus>\<^sub>\<Pi> y) i \<in> Mod i" using assms i by (simp add: Padd_apply Pcarrier_component)
qed (auto simp: Padd_def)

lemma Pzero_closed [intro, simp]: "\<zero>\<^sub>\<Pi> \<in> Pcarrier"
  using Pcarrier_def Pzero_def mod Module.mzero_closed by fastforce

lemma Pscale_closed [intro, simp]:
  assumes "a \<in> R" and "x \<in> Pcarrier" shows "a \<odot>\<^sub>\<Pi> x \<in> Pcarrier"
  using Pcarrier_def Pscale_def mod Module.scale_closed assms by fastforce

subsection \<open>The additive abelian group of the product\<close>

lemma Padd_abelian_group: "Abelian_Group Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>"
proof (rule Abelian_Group.intro)
  show 0: "Group Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>"
  proof (intro GroupI Pzero_closed Padd_closed)
    fix x y z assume xyz: "x \<in> Pcarrier" "y \<in> Pcarrier" "z \<in> Pcarrier"
    show "(x \<oplus>\<^sub>\<Pi> y) \<oplus>\<^sub>\<Pi> z = x \<oplus>\<^sub>\<Pi> (y \<oplus>\<^sub>\<Pi> z)"
    proof (rule Pcarrier_eqI)
      fix i assume i: "i \<in> I"
      interpret Mi: Module R "(+)" "(\<cdot>)" \<zero> \<one> "madd i" "mzero i" "Mod i" "scale i"
        using i by (rule mod)
      show "((x \<oplus>\<^sub>\<Pi> y) \<oplus>\<^sub>\<Pi> z) i = (x \<oplus>\<^sub>\<Pi> (y \<oplus>\<^sub>\<Pi> z)) i"
        using xyz i by (simp add: Padd_apply Pcarrier_component Mi.madd.associative)
    qed (use xyz in auto)
  next
    fix x assume x: "x \<in> Pcarrier"
    show "\<zero>\<^sub>\<Pi> \<oplus>\<^sub>\<Pi> x = x"
    proof (rule Pcarrier_eqI)
      fix i assume i: "i \<in> I"
      interpret Mi: Module R "(+)" "(\<cdot>)" \<zero> \<one> "madd i" "mzero i" "Mod i" "scale i"
        using i by (rule mod)
      show "(\<zero>\<^sub>\<Pi> \<oplus>\<^sub>\<Pi> x) i = x i"
        using x i by (simp add: Padd_apply Pzero_apply Pcarrier_component)
    qed (use x in auto)
  next
    fix x assume x: "x \<in> Pcarrier"
    show "x \<oplus>\<^sub>\<Pi> \<zero>\<^sub>\<Pi> = x"
    proof (rule Pcarrier_eqI)
      fix i assume i: "i \<in> I"
      interpret Mi: Module R "(+)" "(\<cdot>)" \<zero> \<one> "madd i" "mzero i" "Mod i" "scale i"
        using i by (rule mod)
      show "(x \<oplus>\<^sub>\<Pi> \<zero>\<^sub>\<Pi>) i = x i"
        using x i by (simp add: Padd_apply Pzero_apply Pcarrier_component)
    qed (use x in auto)
  next
    fix x assume x: "x \<in> Pcarrier"
    have "\<exists>v. \<forall>i\<in>I. v i \<in> Mod i \<and> madd i (x i) (v i) = mzero i \<and> madd i (v i) (x i) = mzero i"
    proof (rule bchoice, intro ballI)
      fix i assume i: "i \<in> I"
      interpret Mi: Module R "(+)" "(\<cdot>)" \<zero> \<one> "madd i" "mzero i" "Mod i" "scale i"
        using i by (rule mod)
      show "\<exists>v. v \<in> Mod i \<and> madd i (x i) v = mzero i \<and> madd i v (x i) = mzero i"
        using Mi.madd.Monoid_axioms Monoid.invertible_inverse_closed Pcarrier_component i x
        by fastforce
    qed
    then obtain v where v: "\<And>i. i \<in> I \<Longrightarrow> v i \<in> Mod i
          \<and> madd i (x i) (v i) = mzero i \<and> madd i (v i) (x i) = mzero i" by blast
    show "\<exists>y \<in> Pcarrier. x \<oplus>\<^sub>\<Pi> y = \<zero>\<^sub>\<Pi> \<and> y \<oplus>\<^sub>\<Pi> x = \<zero>\<^sub>\<Pi>"
    proof
      define y where "y = (\<lambda>i\<in>I. v i)"
      show yP: "y \<in> Pcarrier" by (rule Pcarrier_memI) (use v in \<open>auto simp: y_def\<close>)
      show "x \<oplus>\<^sub>\<Pi> y = \<zero>\<^sub>\<Pi> \<and> y \<oplus>\<^sub>\<Pi> x = \<zero>\<^sub>\<Pi>"
        using Padd_def Pzero_def y_def v by auto
    qed
  qed
  show "commutative_monoid Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>"
  proof (rule commutative_monoid.intro)
    show "Monoid Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>"
    proof 
      fix x y z assume xyz: "x \<in> Pcarrier" "y \<in> Pcarrier" "z \<in> Pcarrier"
      show "(x \<oplus>\<^sub>\<Pi> y) \<oplus>\<^sub>\<Pi> z = x \<oplus>\<^sub>\<Pi> (y \<oplus>\<^sub>\<Pi> z)"
        using "0" Group_def Monoid.associative xyz by fastforce
    next
      fix x assume x: "x \<in> Pcarrier"
      show "\<zero>\<^sub>\<Pi> \<oplus>\<^sub>\<Pi> x = x"
        by (meson "0" Group_def Monoid.left_unit x)
      show "x \<oplus>\<^sub>\<Pi> \<zero>\<^sub>\<Pi> = x"
        by (meson Group_def Monoid.right_unit 0 x)
    qed auto
    show "commutative_monoid_axioms Pcarrier (\<oplus>\<^sub>\<Pi>)"
    proof 
      fix x y assume xy: "x \<in> Pcarrier" "y \<in> Pcarrier"
      show "x \<oplus>\<^sub>\<Pi> y = y \<oplus>\<^sub>\<Pi> x"
      proof (intro Pcarrier_eqI)
        fix i assume i: "i \<in> I"
        interpret Mi: Module R "(+)" "(\<cdot>)" \<zero> \<one> "madd i" "mzero i" "Mod i" "scale i"
          using i by (rule mod)
        show "(x \<oplus>\<^sub>\<Pi> y) i = (y \<oplus>\<^sub>\<Pi> x) i"
          using xy i by (simp add: Padd_apply Pcarrier_component Mi.madd.commutative)
      qed (use xy in auto)
    qed
  qed
qed

subsection \<open>The product is a module\<close>

theorem module_Pcarrier: "Module R (+) (\<cdot>) \<zero> \<one> (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi> Pcarrier (\<odot>\<^sub>\<Pi>)"
proof (intro Module.intro Module_axioms.intro base.Ring_axioms Padd_abelian_group)
    fix a x assume "a \<in> R" "x \<in> Pcarrier" then show "a \<odot>\<^sub>\<Pi> x \<in> Pcarrier" by (rule Pscale_closed)
  next
    fix a x y assume a: "a \<in> R" and xy: "x \<in> Pcarrier" "y \<in> Pcarrier"
    show "a \<odot>\<^sub>\<Pi> (x \<oplus>\<^sub>\<Pi> y) = (a \<odot>\<^sub>\<Pi> x) \<oplus>\<^sub>\<Pi> (a \<odot>\<^sub>\<Pi> y)"
    proof (rule Pcarrier_eqI)
      fix i assume i: "i \<in> I"
      interpret Mi: Module R "(+)" "(\<cdot>)" \<zero> \<one> "madd i" "mzero i" "Mod i" "scale i"
        using i by (rule mod)
      show "(a \<odot>\<^sub>\<Pi> (x \<oplus>\<^sub>\<Pi> y)) i = ((a \<odot>\<^sub>\<Pi> x) \<oplus>\<^sub>\<Pi> (a \<odot>\<^sub>\<Pi> y)) i"
        using a xy i by (simp add: Pscale_apply Padd_apply Pcarrier_component Mi.scale_distrib_madd)
    qed (use a xy in auto)
  next
    fix a b x assume ab: "a \<in> R" "b \<in> R" and x: "x \<in> Pcarrier"
    then show "(a + b) \<odot>\<^sub>\<Pi> x = (a \<odot>\<^sub>\<Pi> x) \<oplus>\<^sub>\<Pi> (b \<odot>\<^sub>\<Pi> x)"
      using Pcarrier_component Pscale_apply mod 
      by (fastforce intro!: Pcarrier_eqI simp: Padd_apply Module.scale_distrib_add)+
    show "(a \<cdot> b) \<odot>\<^sub>\<Pi> x = a \<odot>\<^sub>\<Pi> (b \<odot>\<^sub>\<Pi> x)"
      using Pcarrier_component Pscale_apply ab mod Module.scale_scale x
      by (fastforce intro!: Pcarrier_eqI)
  next
    fix x assume "x \<in> Pcarrier"
    then show "\<one> \<odot>\<^sub>\<Pi> x = x"
      using Pcarrier_component Pscale_apply mod Module.scale_one
      by (fastforce intro!: Pcarrier_eqI)
qed

sublocale product: Module R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>\<^sub>\<Pi>)" Pzero Pcarrier "(\<odot>\<^sub>\<Pi>)"
  by (rule module_Pcarrier)

subsection \<open>Projections\<close>

definition Pproj :: "'i \<Rightarrow> ('i \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "Pproj i = restrict (\<lambda>x. x i) Pcarrier"

lemma Pproj_apply: "x \<in> Pcarrier \<Longrightarrow> Pproj i x = x i"
  by (simp add: Pproj_def)

text \<open>Each projection is additive and commutes with scaling (it is a module homomorphism onto the
  factor @{term "Mod i"}); we record the two defining equations.\<close>
lemma Pproj_add: "\<lbrakk> i \<in> I; x \<in> Pcarrier; y \<in> Pcarrier \<rbrakk> \<Longrightarrow> Pproj i (x \<oplus>\<^sub>\<Pi> y) = madd i (Pproj i x) (Pproj i y)"
  by (simp add: Pproj_apply Padd_apply)

lemma Pproj_scale: "\<lbrakk> i \<in> I; a \<in> R; x \<in> Pcarrier \<rbrakk> \<Longrightarrow> Pproj i (a \<odot>\<^sub>\<Pi> x) = scale i a (Pproj i x)"
  by (simp add: Pproj_apply Pscale_apply)

subsection \<open>The direct sum\<close>

text \<open>The \<^emph>\<open>direct sum\<close> consists of the product elements of \<^emph>\<open>finite support\<close>: those @{term x} equal to the
  zero element in all but finitely many factors.  It is a submodule of the product.\<close>
definition Psum :: "('i \<Rightarrow> 'b) set"
  where "Psum = {x \<in> Pcarrier. finite {i \<in> I. x i \<noteq> mzero i}}"

lemma Psum_subset: "Psum \<subseteq> Pcarrier" 
  by (auto simp: Psum_def)

lemma Psum_memI:
  "\<lbrakk> x \<in> Pcarrier; finite {i \<in> I. x i \<noteq> mzero i} \<rbrakk> \<Longrightarrow> x \<in> Psum"
  by (simp add: Psum_def)

theorem Psum_submodule: "product.submodule Psum"
proof (rule product.submoduleI)
  show "Psum \<subseteq> Pcarrier" by (rule Psum_subset)
next
  show "\<zero>\<^sub>\<Pi> \<in> Psum" using Pzero_closed
    by (simp add: Psum_memI Pzero_def)
next
  fix x y assume x: "x \<in> Psum" and y: "y \<in> Psum"
  have xP: "x \<in> Pcarrier" and yP: "y \<in> Pcarrier" using x y by (auto simp: Psum_def)
      \<comment> \<open>The support of a sum is contained in the union of the supports.\<close>
  have "\<And>i. \<lbrakk>i \<in> I; y i = mzero i; x i = mzero i\<rbrakk> \<Longrightarrow> (x \<oplus>\<^sub>\<Pi> y) i = mzero i"
    by (metis Padd_apply Pzero_apply product.madd.left_unit xP)
  then have "{i \<in> I. (x \<oplus>\<^sub>\<Pi> y) i \<noteq> mzero i} \<subseteq> {i \<in> I. x i \<noteq> mzero i} \<union> {i \<in> I. y i \<noteq> mzero i}"
    by auto
  moreover have "finite ({i \<in> I. x i \<noteq> mzero i} \<union> {i \<in> I. y i \<noteq> mzero i})"
    using x y by (auto simp: Psum_def)
  ultimately show "x \<oplus>\<^sub>\<Pi> y \<in> Psum" using xP yP Psum_memI finite_subset by blast
next
  fix a x assume a: "a \<in> R" and x: "x \<in> Psum"
  have xP: "x \<in> Pcarrier" using x by (simp add: Psum_def)
  \<comment> \<open>Scaling can only shrink the support.\<close>
  have "\<And>i. \<lbrakk>i \<in> I; x i = mzero i\<rbrakk> \<Longrightarrow> (a \<odot>\<^sub>\<Pi> x) i = mzero i"
    by (metis Pscale_apply Pzero_apply a product.scale_zero_elem)
  then have "{i \<in> I. (a \<odot>\<^sub>\<Pi> x) i \<noteq> mzero i} \<subseteq> {i \<in> I. x i \<noteq> mzero i}"
    by auto
  moreover have "finite {i \<in> I. x i \<noteq> mzero i}" using x by (simp add: Psum_def)
  ultimately have "finite {i \<in> I. (a \<odot>\<^sub>\<Pi> x) i \<noteq> mzero i}" by (rule finite_subset)
  then show "a \<odot>\<^sub>\<Pi> x \<in> Psum" using a xP by (auto intro: Psum_memI)
qed

end

end
