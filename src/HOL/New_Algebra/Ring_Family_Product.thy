section \<open>The direct product of an indexed family of rings\<close>

theory Ring_Family_Product
  imports Ring_Theory
begin

text \<open>The external direct product of a family of rings @{term "R i"} (@{term "i \<in> I"}): the carrier is the
  extensional dependent function space @{term "Pi\<^sub>E I R"}, with pointwise addition, multiplication, zero and
  one.  This mirrors the indexed group product but for rings; its commutative and field-of-components
  refinements follow.  (A product of fields is \<^emph>\<open>not\<close> a field in general --- it has zero divisors as soon as
  @{term I} has more than one element --- so only the commutative-ring refinement is offered.)\<close>

subsection \<open>The product locale\<close>

locale ring_family =
  fixes I :: "'i set"
    and R :: "'i \<Rightarrow> 'a set"
    and add :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and mult :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero :: "'i \<Rightarrow> 'a"
    and one :: "'i \<Rightarrow> 'a"
  assumes ring: "\<And>i. i \<in> I \<Longrightarrow> Ring (R i) (add i) (mult i) (zero i) (one i)"
begin

lemma comp_ring: "i \<in> I \<Longrightarrow> Ring (R i) (add i) (mult i) (zero i) (one i)"
  by (rule ring)

subsection \<open>Carrier and operations\<close>

definition Pcarrier :: "('i \<Rightarrow> 'a) set"
  where "Pcarrier = (\<Pi>\<^sub>E i\<in>I. R i)"

definition Padd :: "('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a)" (infixl \<open>\<oplus>\<^sub>\<Pi>\<close> 65)
  where "x \<oplus>\<^sub>\<Pi> y = (\<lambda>i\<in>I. add i (x i) (y i))"

definition Pmult :: "('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a)" (infixl \<open>\<odot>\<^sub>\<Pi>\<close> 70)
  where "x \<odot>\<^sub>\<Pi> y = (\<lambda>i\<in>I. mult i (x i) (y i))"

definition Pzero :: "'i \<Rightarrow> 'a" (\<open>\<zero>\<^sub>\<Pi>\<close>)
  where "\<zero>\<^sub>\<Pi> = (\<lambda>i\<in>I. zero i)"

definition Pone :: "'i \<Rightarrow> 'a" (\<open>\<one>\<^sub>\<Pi>\<close>)
  where "\<one>\<^sub>\<Pi> = (\<lambda>i\<in>I. one i)"

lemma Pcarrier_memI:
  "\<lbrakk> \<And>i. i \<in> I \<Longrightarrow> x i \<in> R i; x \<in> extensional I \<rbrakk> \<Longrightarrow> x \<in> Pcarrier"
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcarrier_component: "\<lbrakk> x \<in> Pcarrier; i \<in> I \<rbrakk> \<Longrightarrow> x i \<in> R i"
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcarrier_extensional: "x \<in> Pcarrier \<Longrightarrow> x \<in> extensional I"
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcarrier_eqI:
  "\<lbrakk> x \<in> Pcarrier; y \<in> Pcarrier; \<And>i. i \<in> I \<Longrightarrow> x i = y i \<rbrakk> \<Longrightarrow> x = y"
  by (metis Pcarrier_extensional extensionalityI)

lemma Padd_apply: "i \<in> I \<Longrightarrow> (x \<oplus>\<^sub>\<Pi> y) i = add i (x i) (y i)" by (simp add: Padd_def)
lemma Pmult_apply: "i \<in> I \<Longrightarrow> (x \<odot>\<^sub>\<Pi> y) i = mult i (x i) (y i)" by (simp add: Pmult_def)
lemma Pzero_apply: "i \<in> I \<Longrightarrow> \<zero>\<^sub>\<Pi> i = zero i" by (simp add: Pzero_def)
lemma Pone_apply: "i \<in> I \<Longrightarrow> \<one>\<^sub>\<Pi> i = one i" by (simp add: Pone_def)

lemma Padd_closed [intro, simp]:
  assumes "x \<in> Pcarrier" "y \<in> Pcarrier" shows "x \<oplus>\<^sub>\<Pi> y \<in> Pcarrier"
proof (rule Pcarrier_memI)
  fix i assume i: "i \<in> I"
  interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
  show "(x \<oplus>\<^sub>\<Pi> y) i \<in> R i" using assms i by (simp add: Padd_apply Pcarrier_component)
qed (auto simp: Padd_def)

lemma Pmult_closed [intro, simp]:
  assumes "x \<in> Pcarrier" "y \<in> Pcarrier" shows "x \<odot>\<^sub>\<Pi> y \<in> Pcarrier"
proof (rule Pcarrier_memI)
  fix i assume i: "i \<in> I"
  interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
  show "(x \<odot>\<^sub>\<Pi> y) i \<in> R i" using assms i by (simp add: Pmult_apply Pcarrier_component)
qed (auto simp: Pmult_def)

lemma Pzero_closed [intro, simp]: "\<zero>\<^sub>\<Pi> \<in> Pcarrier"
proof (rule Pcarrier_memI)
  fix i assume i: "i \<in> I"
  interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
  show "\<zero>\<^sub>\<Pi> i \<in> R i" using i by (simp add: Pzero_apply)
qed (auto simp: Pzero_def)

lemma Pone_closed [intro, simp]: "\<one>\<^sub>\<Pi> \<in> Pcarrier"
proof (rule Pcarrier_memI)
  fix i assume i: "i \<in> I"
  interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
  show "\<one>\<^sub>\<Pi> i \<in> R i" using i by (simp add: Pone_apply)
qed (auto simp: Pone_def)

subsection \<open>The additive abelian group\<close>

lemma additive_group: "Group Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>"
proof (intro GroupI Pzero_closed Padd_closed)
  fix x y z assume xyz: "x \<in> Pcarrier" "y \<in> Pcarrier" "z \<in> Pcarrier"
  show "(x \<oplus>\<^sub>\<Pi> y) \<oplus>\<^sub>\<Pi> z = x \<oplus>\<^sub>\<Pi> (y \<oplus>\<^sub>\<Pi> z)"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
    show "((x \<oplus>\<^sub>\<Pi> y) \<oplus>\<^sub>\<Pi> z) i = (x \<oplus>\<^sub>\<Pi> (y \<oplus>\<^sub>\<Pi> z)) i"
      using xyz i by (simp add: Padd_apply Pcarrier_component Ri.additive.associative)
  qed (use xyz in auto)
next
  fix x assume x: "x \<in> Pcarrier"
  show "\<zero>\<^sub>\<Pi> \<oplus>\<^sub>\<Pi> x = x"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
    show "(\<zero>\<^sub>\<Pi> \<oplus>\<^sub>\<Pi> x) i = x i"
      by (simp add: Padd_apply Pcarrier_component Pzero_def i x)
  qed (use x in auto)
  show "x \<oplus>\<^sub>\<Pi> \<zero>\<^sub>\<Pi> = x"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
    show "(x \<oplus>\<^sub>\<Pi> \<zero>\<^sub>\<Pi>) i = x i"
      using x i by (simp add: Padd_apply Pzero_apply Pcarrier_component)
  qed (use x in auto)
next
  fix x assume x: "x \<in> Pcarrier"
  note [[unify_search_bound=10]]  \<comment>\<open>for the two following meson calls\<close>
  have "\<exists>v. v i \<in> R i \<and> add i (x i) (v i) = zero i \<and> add i (v i) (x i) = zero i" if i: "i \<in> I" for i
  proof -
    interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
    show ?thesis
      by (meson Pcarrier_component Ri.additive.invertible Ri.additive.invertibleE i x)
  qed
  then obtain v where v: "\<And>i. i \<in> I \<Longrightarrow> v i \<in> R i
          \<and> add i (x i) (v i) = zero i \<and> add i (v i) (x i) = zero i" by meson
  define y where "y = (\<lambda>i\<in>I. v i)"
  have "x \<oplus>\<^sub>\<Pi> y = \<zero>\<^sub>\<Pi> \<and> y \<oplus>\<^sub>\<Pi> x = \<zero>\<^sub>\<Pi>"
    using Padd_def Pzero_def \<open>y \<equiv> restrict v I\<close> v by auto
  then show "\<exists>y \<in> Pcarrier. x \<oplus>\<^sub>\<Pi> y = \<zero>\<^sub>\<Pi> \<and> y \<oplus>\<^sub>\<Pi> x = \<zero>\<^sub>\<Pi>"
    using Pcarrier_def v y_def by auto
qed

lemma additive_abelian_group: "Abelian_Group Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>"
proof (intro Abelian_Group.intro additive_group)
  show "commutative_monoid Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>"
  proof (rule commutative_monoid.intro)
    show "Monoid Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>"
    proof 
      fix x y z assume xyz: "x \<in> Pcarrier" "y \<in> Pcarrier" "z \<in> Pcarrier"
      show "(x \<oplus>\<^sub>\<Pi> y) \<oplus>\<^sub>\<Pi> z = x \<oplus>\<^sub>\<Pi> (y \<oplus>\<^sub>\<Pi> z)"
        using Group_def Monoid.associative additive_group xyz by fastforce
    next
      fix x assume x: "x \<in> Pcarrier"
      show "\<zero>\<^sub>\<Pi> \<oplus>\<^sub>\<Pi> x = x"
        by (meson Group_def Monoid.left_unit additive_group x)
      show "x \<oplus>\<^sub>\<Pi> \<zero>\<^sub>\<Pi> = x"
        by (meson Group_def Monoid.right_unit additive_group x)
    qed auto
    show "commutative_monoid_axioms Pcarrier (\<oplus>\<^sub>\<Pi>)"
    proof 
      fix x y assume xy: "x \<in> Pcarrier" "y \<in> Pcarrier"
      show "x \<oplus>\<^sub>\<Pi> y = y \<oplus>\<^sub>\<Pi> x"
      proof (rule Pcarrier_eqI)
        fix i assume i: "i \<in> I"
        interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
        show "(x \<oplus>\<^sub>\<Pi> y) i = (y \<oplus>\<^sub>\<Pi> x) i"
          using xy i by (simp add: Padd_apply Pcarrier_component Ri.additive.commutative)
      qed (use xy in auto)
    qed
  qed
qed

subsection \<open>The multiplicative monoid\<close>

lemma multiplicative_monoid: "Monoid Pcarrier (\<odot>\<^sub>\<Pi>) \<one>\<^sub>\<Pi>"
proof (unfold_locales)
  show "\<And>x y. x \<in> Pcarrier \<Longrightarrow> y \<in> Pcarrier \<Longrightarrow> x \<odot>\<^sub>\<Pi> y \<in> Pcarrier" by (rule Pmult_closed)
  show "\<one>\<^sub>\<Pi> \<in> Pcarrier" by (rule Pone_closed)
next
  fix x y z assume xyz: "x \<in> Pcarrier" "y \<in> Pcarrier" "z \<in> Pcarrier"
  show "(x \<odot>\<^sub>\<Pi> y) \<odot>\<^sub>\<Pi> z = x \<odot>\<^sub>\<Pi> (y \<odot>\<^sub>\<Pi> z)"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
    show "((x \<odot>\<^sub>\<Pi> y) \<odot>\<^sub>\<Pi> z) i = (x \<odot>\<^sub>\<Pi> (y \<odot>\<^sub>\<Pi> z)) i"
      using xyz i by (simp add: Pmult_apply Pcarrier_component Ri.multiplicative.associative)
  qed (use xyz in auto)
next
  fix x assume x: "x \<in> Pcarrier"
  show "\<one>\<^sub>\<Pi> \<odot>\<^sub>\<Pi> x = x"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
    show "(\<one>\<^sub>\<Pi> \<odot>\<^sub>\<Pi> x) i = x i"
      using x i by (simp add: Pmult_apply Pone_apply Pcarrier_component)
  qed (use x in auto)
next
  fix x assume x: "x \<in> Pcarrier"
  show "x \<odot>\<^sub>\<Pi> \<one>\<^sub>\<Pi> = x"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
    show "(x \<odot>\<^sub>\<Pi> \<one>\<^sub>\<Pi>) i = x i"
      using x i by (simp add: Pmult_apply Pone_apply Pcarrier_component)
  qed (use x in auto)
qed

subsection \<open>The product is a ring\<close>

theorem Ring_Pcarrier: "Ring Pcarrier (\<oplus>\<^sub>\<Pi>) (\<odot>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi> \<one>\<^sub>\<Pi>"
proof (rule Ring.intro)
  show "Abelian_Group Pcarrier (\<oplus>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi>" by (rule additive_abelian_group)
  show "Monoid Pcarrier (\<odot>\<^sub>\<Pi>) \<one>\<^sub>\<Pi>" by (rule multiplicative_monoid)
  show "Ring_axioms Pcarrier (\<oplus>\<^sub>\<Pi>) (\<odot>\<^sub>\<Pi>)"
  proof
    fix x y z assume xyz: "x \<in> Pcarrier" "y \<in> Pcarrier" "z \<in> Pcarrier"
    show "x \<odot>\<^sub>\<Pi> (y \<oplus>\<^sub>\<Pi> z) = x \<odot>\<^sub>\<Pi> y \<oplus>\<^sub>\<Pi> (x \<odot>\<^sub>\<Pi> z)"
    proof (rule Pcarrier_eqI)
      fix i assume i: "i \<in> I"
      interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
      show "(x \<odot>\<^sub>\<Pi> (y \<oplus>\<^sub>\<Pi> z)) i = (x \<odot>\<^sub>\<Pi> y \<oplus>\<^sub>\<Pi> (x \<odot>\<^sub>\<Pi> z)) i"
        using xyz i by (simp add: Pmult_apply Padd_apply Pcarrier_component Ri.distributive)
    qed (use xyz in auto)
    show "(y \<oplus>\<^sub>\<Pi> z) \<odot>\<^sub>\<Pi> x = y \<odot>\<^sub>\<Pi> x \<oplus>\<^sub>\<Pi> (z \<odot>\<^sub>\<Pi> x)"
    proof (rule Pcarrier_eqI)
      fix i assume i: "i \<in> I"
      interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
      show "((y \<oplus>\<^sub>\<Pi> z) \<odot>\<^sub>\<Pi> x) i = (y \<odot>\<^sub>\<Pi> x \<oplus>\<^sub>\<Pi> (z \<odot>\<^sub>\<Pi> x)) i"
        using xyz i by (simp add: Pmult_apply Padd_apply Pcarrier_component Ri.distributive)
    qed (use xyz in auto)
  qed
qed

sublocale product: Ring Pcarrier "(\<oplus>\<^sub>\<Pi>)" "(\<odot>\<^sub>\<Pi>)" Pzero Pone
  by (rule Ring_Pcarrier)

subsection \<open>Projections are ring homomorphisms\<close>

definition Pproj :: "'i \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "Pproj i = restrict (\<lambda>x. x i) Pcarrier"

lemma Pproj_apply: "x \<in> Pcarrier \<Longrightarrow> Pproj i x = x i"
  by (simp add: Pproj_def)

lemma Pproj_hom:
  assumes i: "i \<in> I"
  shows "ring_homomorphism (Pproj i) Pcarrier (\<oplus>\<^sub>\<Pi>) (\<odot>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi> \<one>\<^sub>\<Pi>
                            (R i) (add i) (mult i) (zero i) (one i)"
proof -
  interpret Ri: Ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule ring)
  have graph: "Pproj i \<in> Pcarrier \<rightarrow>\<^sub>E R i"
    by (simp add: Pcarrier_component Pproj_def i)
  show ?thesis
  proof 
  qed (use i in \<open>auto simp: graph Pproj_apply Pzero_apply Pone_apply Padd_apply Pmult_apply\<close>)
qed

end

subsection \<open>The product of a family of commutative rings is commutative\<close>

locale commutative_ring_family = ring_family +
  assumes comm: "\<And>i. i \<in> I \<Longrightarrow> commutative_ring (R i) (add i) (mult i) (zero i) (one i)"
begin

theorem commutative_ring_Pcarrier: "commutative_ring Pcarrier (\<oplus>\<^sub>\<Pi>) (\<odot>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi> \<one>\<^sub>\<Pi>"
proof (rule commutative_ring.intro)
  show "Ring Pcarrier (\<oplus>\<^sub>\<Pi>) (\<odot>\<^sub>\<Pi>) \<zero>\<^sub>\<Pi> \<one>\<^sub>\<Pi>" by (rule Ring_Pcarrier)
  \<comment> \<open>The multiplicative monoid is commutative.\<close>
  show "commutative_monoid Pcarrier (\<odot>\<^sub>\<Pi>) \<one>\<^sub>\<Pi>"
  proof (rule commutative_monoid.intro)
    show "Monoid Pcarrier (\<odot>\<^sub>\<Pi>) \<one>\<^sub>\<Pi>" by (rule multiplicative_monoid)
    show "commutative_monoid_axioms Pcarrier (\<odot>\<^sub>\<Pi>)"
    proof
      fix x y assume xy: "x \<in> Pcarrier" "y \<in> Pcarrier"
      show "x \<odot>\<^sub>\<Pi> y = y \<odot>\<^sub>\<Pi> x"
      proof (rule Pcarrier_eqI)
        fix i assume i: "i \<in> I"
        interpret Ri: commutative_ring "R i" "add i" "mult i" "zero i" "one i" using i by (rule comm)
        show "(x \<odot>\<^sub>\<Pi> y) i = (y \<odot>\<^sub>\<Pi> x) i"
          using xy i by (simp add: Pmult_apply Pcarrier_component Ri.multiplicative.commutative)
      qed (use xy in auto)
    qed
  qed
qed

end

end
