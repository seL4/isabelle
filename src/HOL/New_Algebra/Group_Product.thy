section \<open>The external direct product of two groups\<close>

theory Group_Product
  imports Solvable_Transfer
begin

text \<open>The external direct product of two groups: carrier the Cartesian product of the carriers, with
  componentwise operation and unit.  This is the group-theoretic prerequisite for combining two
  solvable Galois groups (the compositum of two splitting fields embeds into the product of their
  Galois groups); its headline consequence is that a \<^emph>\<open>product of solvable groups is solvable\<close>.\<close>

locale group_product =
  G: Group G "(\<cdot>)" \<one> + G': Group G' "(\<cdot>')" "\<one>'"
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
    and G' and composition' (infixl \<open>\<cdot>''\<close> 70) and unit' (\<open>\<one>''\<close>)
begin

definition pcarrier :: "('a \<times> 'b) set" where "pcarrier = G \<times> G'"

definition pcomp :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" (infixl \<open>\<otimes>\<^sub>\<times>\<close> 70)
  where "x \<otimes>\<^sub>\<times> y = (fst x \<cdot> fst y, snd x \<cdot>' snd y)"

definition punit :: "'a \<times> 'b" (\<open>\<one>\<^sub>\<times>\<close>) where "\<one>\<^sub>\<times> = (\<one>, \<one>')"

lemma pcomp_closed [intro, simp]:
  "x \<in> pcarrier \<Longrightarrow> y \<in> pcarrier \<Longrightarrow> x \<otimes>\<^sub>\<times> y \<in> pcarrier"
  by (auto simp: pcarrier_def pcomp_def)

lemma punit_closed [intro, simp]: "\<one>\<^sub>\<times> \<in> pcarrier"
  by (auto simp: pcarrier_def punit_def)

text \<open>The direct product is a group.\<close>
theorem Group_product: "Group pcarrier (\<otimes>\<^sub>\<times>) \<one>\<^sub>\<times>"
proof (rule GroupI)
  fix x y z assume "x \<in> pcarrier" "y \<in> pcarrier" "z \<in> pcarrier"
  then show "(x \<otimes>\<^sub>\<times> y) \<otimes>\<^sub>\<times> z = x \<otimes>\<^sub>\<times> (y \<otimes>\<^sub>\<times> z)"
    by (auto simp: pcarrier_def pcomp_def G.associative G'.associative)
next
  fix u assume u: "u \<in> pcarrier"
  then show "\<one>\<^sub>\<times> \<otimes>\<^sub>\<times> u = u" "u \<otimes>\<^sub>\<times> \<one>\<^sub>\<times> = u"
    by (auto simp: pcarrier_def pcomp_def punit_def)
  have fu: "fst u \<in> G" and su: "snd u \<in> G'" 
    using u by (auto simp: pcarrier_def)
  obtain a where a: "a \<in> G" "fst u \<cdot> a = \<one>" "a \<cdot> fst u = \<one>"
    using G.invertible[OF fu] by (auto simp: G.invertible_def)
  obtain b where b: "b \<in> G'" "snd u \<cdot>' b = \<one>'" "b \<cdot>' snd u = \<one>'"
    using G'.invertible[OF su] by (auto simp: G'.invertible_def)
  show "\<exists>v \<in> pcarrier. u \<otimes>\<^sub>\<times> v = \<one>\<^sub>\<times> \<and> v \<otimes>\<^sub>\<times> u = \<one>\<^sub>\<times>"
    using a b pcomp_def punit_def pcarrier_def by auto
qed auto

sublocale prod: Group pcarrier "(\<otimes>\<^sub>\<times>)" "\<one>\<^sub>\<times>" 
  by (rule Group_product)

subsection \<open>Projections are homomorphisms; the derived series is componentwise-bounded\<close>

text \<open>The (extensional) first and second projections are group homomorphisms onto @{term G} and
  @{term G'}.  We use @{term "restrict fst pcarrier"} so the maps are extensional, as the
  homomorphism locale requires; on @{term pcarrier} they agree with @{term fst} / @{term snd}.\<close>
definition p1 :: "'a \<times> 'b \<Rightarrow> 'a"
  where "p1 = restrict fst pcarrier"

definition p2 :: "'a \<times> 'b \<Rightarrow> 'b" 
  where "p2 = restrict snd pcarrier"

lemma p1_eq: "x \<in> pcarrier \<Longrightarrow> p1 x = fst x" 
  by (simp add: p1_def)

lemma p2_eq: "x \<in> pcarrier \<Longrightarrow> p2 x = snd x" 
  by (simp add: p2_def)

lemma p1_hom: "group_homomorphism p1 pcarrier (\<otimes>\<^sub>\<times>) \<one>\<^sub>\<times> G (\<cdot>) \<one>"
proof 
  show "p1 \<in> pcarrier \<rightarrow>\<^sub>E G" 
    by (auto simp: p1_def pcarrier_def)
  show "\<And>x y. x \<in> pcarrier \<Longrightarrow> y \<in> pcarrier \<Longrightarrow> p1 (x \<otimes>\<^sub>\<times> y) = p1 x \<cdot> p1 y"
    using p1_eq pcomp_closed pcomp_def by auto
  show "p1 \<one>\<^sub>\<times> = \<one>"
    using p1_eq punit_closed punit_def by auto
qed

lemma p2_hom: "group_homomorphism p2 pcarrier (\<otimes>\<^sub>\<times>) \<one>\<^sub>\<times> G' (\<cdot>') \<one>'"
proof 
  show "p2 \<in> pcarrier \<rightarrow>\<^sub>E G'" 
    by (auto simp: p2_def pcarrier_def)
  show "\<And>x y. x \<in> pcarrier \<Longrightarrow> y \<in> pcarrier \<Longrightarrow> p2 (x \<otimes>\<^sub>\<times> y) = p2 x \<cdot>' p2 y"
    using p2_eq pcomp_closed pcomp_def by auto
  show "p2 \<one>\<^sub>\<times> = \<one>'"
    using p2_eq punit_closed punit_def by auto
qed

text \<open>An element of the product's derived series projects into each factor's derived series.\<close>
lemma derivedSeries_p1: "p1 ` prod.derivedSeries n \<subseteq> G.derivedSeries n"
proof (induction n)
  case 0
  show ?case
    by (meson group_homomorphism.image_derivedSeries_subset p1_hom)
next
  case (Suc n)
  interpret F: group_homomorphism p1 pcarrier "(\<otimes>\<^sub>\<times>)" "\<one>\<^sub>\<times>" G "(\<cdot>)" \<one> by (rule p1_hom)
  have "p1 ` prod.derivedSeries (Suc n)
          \<subseteq> G.commutator_subgroup (p1 ` prod.derivedSeries n) (p1 ` prod.derivedSeries n)"
    using F.image_commutator_subgroup_sub[OF prod.derivedSeries_subset prod.derivedSeries_subset]
    by simp
  also have "\<dots> \<subseteq> G.commutator_subgroup (G.derivedSeries n) (G.derivedSeries n)"
    using G.commutator_subgroup_mono[OF Suc.IH Suc.IH] .
  also have "\<dots> = G.derivedSeries (Suc n)" by simp
  finally show ?case .
qed

lemma derivedSeries_p2: "p2 ` prod.derivedSeries n \<subseteq> G'.derivedSeries n"
proof (induction n)
  case 0 show ?case
    by (meson group_homomorphism.image_derivedSeries_subset p2_hom)
next
  case (Suc n)
  interpret S: group_homomorphism p2 pcarrier "(\<otimes>\<^sub>\<times>)" "\<one>\<^sub>\<times>" G' "(\<cdot>')" "\<one>'" by (rule p2_hom)
  have "p2 ` prod.derivedSeries (Suc n)
          \<subseteq> G'.commutator_subgroup (p2 ` prod.derivedSeries n) (p2 ` prod.derivedSeries n)"
    using S.image_commutator_subgroup_sub[OF prod.derivedSeries_subset prod.derivedSeries_subset] by simp
  also have "\<dots> \<subseteq> G'.commutator_subgroup (G'.derivedSeries n) (G'.derivedSeries n)"
    using G'.commutator_subgroup_mono[OF Suc.IH Suc.IH] .
  also have "\<dots> = G'.derivedSeries (Suc n)" by simp
  finally show ?case .
qed

subsection \<open>Product of solvable groups is solvable\<close>

text \<open>\<^emph>\<open>The direct product of two solvable groups is solvable.\<close>  If both factors' derived series reach
  the trivial subgroup (at steps @{term m}, @{term k}), then at step @{term "max m k"} the product's
  derived series projects to @{term "{\<one>}"} in each factor (the derived series is monotone decreasing),
  hence consists of the single element @{term "\<one>\<^sub>\<times>"}.\<close>
theorem solvable_product:
  assumes solvG: "G.solvable" and solvG': "G'.solvable"
  shows "prod.solvable"
proof -
  obtain m where m: "G.derivedSeries m = {\<one>}" using solvG unfolding G.solvable_def by blast
  obtain k where k: "G'.derivedSeries k = {\<one>'}" using solvG' unfolding G'.solvable_def by blast
  define N where "N = max m k"
  have dGN: "G.derivedSeries N = {\<one>}"
    using m G.derivedSeries_antimono[of m N] G.derivedSeries_unit_closed by (auto simp: N_def)
  have dG'N: "G'.derivedSeries N = {\<one>'}"
    using k G'.derivedSeries_antimono[of k N] G'.derivedSeries_unit_closed by (auto simp: N_def)
  \<comment> \<open>At step @{term N} the product's derived series projects to a point in each factor.\<close>
  have "prod.derivedSeries N \<subseteq> {\<one>\<^sub>\<times>}"
  proof
    fix x assume x: "x \<in> prod.derivedSeries N"
    have xp: "x \<in> pcarrier" using x prod.derivedSeries_subset by blast
    then have "p1 x = \<one>" "p2 x = \<one>'" using derivedSeries_p1 dGN derivedSeries_p2 dG'N
      using x by blast+
    then show "x \<in> {\<one>\<^sub>\<times>}"
      using p1_eq p2_eq punit_def xp by auto
  qed
  moreover have "\<one>\<^sub>\<times> \<in> prod.derivedSeries N" by (rule prod.derivedSeries_unit_closed)
  ultimately have "prod.derivedSeries N = {\<one>\<^sub>\<times>}" by auto
  then show ?thesis unfolding prod.solvable_def by blast
qed

end

end
