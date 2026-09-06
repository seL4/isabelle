section \<open>The direct product of an indexed family of groups\<close>

theory Group_Family_Product
  imports Group_Theory
begin

text \<open>The external direct product of a family of groups @{term "G i"} (@{term "i \<in> I"}): the carrier is
  the \<^emph>\<open>extensional\<close> dependent function space @{term "Pi\<^sub>E I G"} --- functions defined on @{term I} with
  @{term "x i \<in> G i"} for each index --- with pointwise composition and unit.  This generalises the binary
  external direct product of theory \<open>Group_Product\<close> to an arbitrary index set, mirroring \<open>product_group\<close> of
  \<open>HOL-Algebra.Product_Groups\<close> but in the locale idiom.\<close>

subsection \<open>The product locale\<close>

text \<open>A family of groups indexed by @{term I}: for each @{term "i \<in> I"} a carrier @{term "G i"} with
  composition @{term "comp i"} and unit @{term "unit i"} forming a \<open>comp_group\<close>.\<close>
locale group_family =
  fixes I :: "'i set"
    and G :: "'i \<Rightarrow> 'a set"
    and comp :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and unit :: "'i \<Rightarrow> 'a"
  assumes comp_group: "\<And>i. i \<in> I \<Longrightarrow> Group (G i) (comp i) (unit i)"
begin

subsection \<open>Carrier, composition and unit\<close>

text \<open>The product carrier: extensional functions @{term x} on @{term I} with @{term "x i \<in> G i"}.\<close>
definition Pcarrier :: "('i \<Rightarrow> 'a) set" (\<open>\<Prod>\<^sub>G\<close>)
  where "\<Prod>\<^sub>G = (\<Pi>\<^sub>E i\<in>I. G i)"

text \<open>Pointwise composition (extensional on @{term I}).\<close>
definition Pcomp :: "('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a)" (infixl \<open>\<otimes>\<^sub>\<Pi>\<close> 70)
  where "x \<otimes>\<^sub>\<Pi> y = (\<lambda>i\<in>I. comp i (x i) (y i))"

text \<open>The pointwise unit.\<close>
definition Punit :: "'i \<Rightarrow> 'a" (\<open>\<one>\<^sub>\<Pi>\<close>)
  where "\<one>\<^sub>\<Pi> = (\<lambda>i\<in>I. unit i)"

lemma Pcarrier_memI:
  "\<lbrakk> \<And>i. i \<in> I \<Longrightarrow> x i \<in> G i; x \<in> extensional I \<rbrakk> \<Longrightarrow> x \<in> \<Prod>\<^sub>G"
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcarrier_mem_component: "\<lbrakk> x \<in> \<Prod>\<^sub>G; i \<in> I \<rbrakk> \<Longrightarrow> x i \<in> G i"      
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcarrier_extensional: "x \<in> \<Prod>\<^sub>G \<Longrightarrow> x \<in> extensional I"
  by (auto simp: Pcarrier_def PiE_iff)

lemma Pcomp_closed [intro, simp]:
  assumes "x \<in> \<Prod>\<^sub>G" and "y \<in> \<Prod>\<^sub>G" shows "x \<otimes>\<^sub>\<Pi> y \<in> \<Prod>\<^sub>G"
proof (rule Pcarrier_memI)
  fix i assume i: "i \<in> I"
  interpret Gi: Group "G i" "comp i" "unit i" using i by (rule comp_group)
  show "(x \<otimes>\<^sub>\<Pi> y) i \<in> G i"
    using assms i by (auto simp: Pcomp_def Pcarrier_mem_component)
qed (auto simp: Pcomp_def)

lemma Punit_closed [iff]: "\<one>\<^sub>\<Pi> \<in> \<Prod>\<^sub>G"
  using Group_def Monoid.unit_closed Pcarrier_def Punit_def comp_group by fastforce

lemma Pcomp_apply: "i \<in> I \<Longrightarrow> (x \<otimes>\<^sub>\<Pi> y) i = comp i (x i) (y i)"
  by (simp add: Pcomp_def)

lemma Punit_apply: "i \<in> I \<Longrightarrow> \<one>\<^sub>\<Pi> i = unit i"
  by (simp add: Punit_def)

subsection \<open>The product is a group\<close>

text \<open>Two members of the product agree iff they agree componentwise on @{term I} (both being
  extensional).\<close>
lemma Pcarrier_eqI:
  assumes "x \<in> \<Prod>\<^sub>G" and "y \<in> \<Prod>\<^sub>G" and "\<And>i. i \<in> I \<Longrightarrow> x i = y i"
  shows "x = y"
  using assms by (metis Pcarrier_extensional extensionalityI)

theorem Group_Pcarrier: "Group \<Prod>\<^sub>G (\<otimes>\<^sub>\<Pi>) \<one>\<^sub>\<Pi>"
proof (rule GroupI)
  show "\<And>x y. x \<in> \<Prod>\<^sub>G \<Longrightarrow> y \<in> \<Prod>\<^sub>G \<Longrightarrow> x \<otimes>\<^sub>\<Pi> y \<in> \<Prod>\<^sub>G" by (rule Pcomp_closed)
  show "\<one>\<^sub>\<Pi> \<in> \<Prod>\<^sub>G" by (rule Punit_closed)
next
  fix x y z assume xyz: "x \<in> \<Prod>\<^sub>G" "y \<in> \<Prod>\<^sub>G" "z \<in> \<Prod>\<^sub>G"
  show "(x \<otimes>\<^sub>\<Pi> y) \<otimes>\<^sub>\<Pi> z = x \<otimes>\<^sub>\<Pi> (y \<otimes>\<^sub>\<Pi> z)"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Gi: Group "G i" "comp i" "unit i" using i by (rule comp_group)
    show "((x \<otimes>\<^sub>\<Pi> y) \<otimes>\<^sub>\<Pi> z) i = (x \<otimes>\<^sub>\<Pi> (y \<otimes>\<^sub>\<Pi> z)) i"
      using xyz i by (simp add: Pcomp_apply Pcarrier_mem_component Gi.associative)
  qed (use xyz in auto)
next
  fix x assume x: "x \<in> \<Prod>\<^sub>G"
  show "\<one>\<^sub>\<Pi> \<otimes>\<^sub>\<Pi> x = x"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Gi: Group "G i" "comp i" "unit i" using i by (rule comp_group)
    show "(\<one>\<^sub>\<Pi> \<otimes>\<^sub>\<Pi> x) i = x i"
      using x i by (simp add: Pcomp_apply Punit_apply Pcarrier_mem_component)
  qed (use x in auto)
next
  fix x assume x: "x \<in> \<Prod>\<^sub>G"
  show "x \<otimes>\<^sub>\<Pi> \<one>\<^sub>\<Pi> = x"
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Gi: Group "G i" "comp i" "unit i" using i by (rule comp_group)
    show "(x \<otimes>\<^sub>\<Pi> \<one>\<^sub>\<Pi>) i = x i"
      using x i by (simp add: Pcomp_apply Punit_apply Pcarrier_mem_component)
  qed (use x in auto)
next
  fix x assume x: "x \<in> \<Prod>\<^sub>G"
  \<comment> \<open>The inverse is the pointwise inverse.\<close>
  \<comment> \<open>Choose a two-sided inverse in each factor.\<close>
  have "\<exists>v. \<forall>i\<in>I. v i \<in> G i \<and> comp i (x i) (v i) = unit i \<and> comp i (v i) (x i) = unit i"
  proof (intro bchoice ballI)
    fix i assume i: "i \<in> I"
    interpret Gi: Group "G i" "comp i" "unit i" using i by (rule comp_group)
    have xi: "x i \<in> G i" using x i by (rule Pcarrier_mem_component)
    then have "Gi.invertible (x i)" by simp
    then show "\<exists>v. v \<in> G i \<and> comp i (x i) v = unit i \<and> comp i v (x i) = unit i"
      using xi by (auto simp: Gi.invertible_def)
  qed
  then obtain v where v: "\<And>i. i \<in> I \<Longrightarrow> v i \<in> G i
        \<and> comp i (x i) (v i) = unit i \<and> comp i (v i) (x i) = unit i" by blast
  show "\<exists>y \<in> \<Prod>\<^sub>G. x \<otimes>\<^sub>\<Pi> y = \<one>\<^sub>\<Pi> \<and> y \<otimes>\<^sub>\<Pi> x = \<one>\<^sub>\<Pi>"
  proof
    define y where "y = (\<lambda>i\<in>I. v i)"
    have yi: "y i = v i" if "i \<in> I" for i using that by (simp add: y_def)
    show yG: "y \<in> \<Prod>\<^sub>G"
      by (rule Pcarrier_memI) (use v in \<open>auto simp: y_def\<close>)
    have "x \<otimes>\<^sub>\<Pi> y = \<one>\<^sub>\<Pi> \<and> y \<otimes>\<^sub>\<Pi> x = \<one>\<^sub>\<Pi>"
    proof (intro conjI Pcarrier_eqI Punit_closed Pcomp_closed x yG)
      fix i assume i: "i \<in> I"
      show "(x \<otimes>\<^sub>\<Pi> y) i = \<one>\<^sub>\<Pi> i" "(y \<otimes>\<^sub>\<Pi> x) i = \<one>\<^sub>\<Pi> i"
        using v[OF i] i by (simp_all add: Pcomp_apply Punit_apply yi)
    qed
    then show "x \<otimes>\<^sub>\<Pi> y = \<one>\<^sub>\<Pi> \<and> y \<otimes>\<^sub>\<Pi> x = \<one>\<^sub>\<Pi>" .
  qed
qed

sublocale product: Group Pcarrier "(\<otimes>\<^sub>\<Pi>)" Punit
  by (rule Group_Pcarrier)

subsection \<open>Projections are homomorphisms\<close>

text \<open>The projection onto the @{term i}th factor is a \<open>comp_group\<close> homomorphism from the product onto
  @{term "G i"}.\<close>
definition Pproj :: "'i \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "Pproj i = restrict (\<lambda>x. x i) \<Prod>\<^sub>G"

lemma Pproj_apply: "x \<in> \<Prod>\<^sub>G \<Longrightarrow> Pproj i x = x i"
  by (simp add: Pproj_def)

lemma Pproj_hom:
  assumes i: "i \<in> I"
  shows "group_homomorphism (Pproj i) \<Prod>\<^sub>G (\<otimes>\<^sub>\<Pi>) \<one>\<^sub>\<Pi> (G i) (comp i) (unit i)"
proof -
  interpret Gi: Group "G i" "comp i" "unit i" using i by (rule comp_group)
  have graph: "Pproj i \<in> \<Prod>\<^sub>G \<rightarrow>\<^sub>E G i"
    by (simp add: Pcarrier_def PiE_mem Pproj_def i)
  show ?thesis
  proof 
  qed (use i in \<open>auto simp: graph Pproj_apply Punit_apply Pcomp_apply\<close>)
qed

end

subsection \<open>The product of a family of abelian groups is abelian\<close>

locale abelian_group_family = group_family +
  assumes abelian: "\<And>i. i \<in> I \<Longrightarrow> Abelian_Group (G i) (comp i) (unit i)"
begin

theorem abelian_group_Pcarrier: "Abelian_Group \<Prod>\<^sub>G (\<otimes>\<^sub>\<Pi>) \<one>\<^sub>\<Pi>"
proof (rule Abelian_Group.intro)
  show "Group \<Prod>\<^sub>G (\<otimes>\<^sub>\<Pi>) \<one>\<^sub>\<Pi>" by (rule Group_Pcarrier)
  \<comment> \<open>The product operation is commutative, so the (already-established) monoid is commutative.\<close>
  have comm: "x \<otimes>\<^sub>\<Pi> y = y \<otimes>\<^sub>\<Pi> x" if xy: "x \<in> \<Prod>\<^sub>G" "y \<in> \<Prod>\<^sub>G" for x y
  proof (rule Pcarrier_eqI)
    fix i assume i: "i \<in> I"
    interpret Gi: Abelian_Group "G i" "comp i" "unit i" using i by (rule abelian)
    show "(x \<otimes>\<^sub>\<Pi> y) i = (y \<otimes>\<^sub>\<Pi> x) i"
      using xy i by (simp add: Pcomp_apply Pcarrier_mem_component Gi.commutative)
  qed (use xy in auto)
  show "commutative_monoid \<Prod>\<^sub>G (\<otimes>\<^sub>\<Pi>) \<one>\<^sub>\<Pi>"
    by (simp add: comm commutative_monoid_axioms.intro commutative_monoid_def product.Monoid_axioms)
qed

end

end
