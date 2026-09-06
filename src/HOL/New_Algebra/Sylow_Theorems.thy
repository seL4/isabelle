theory Sylow_Theorems
  imports Group_Theory Group_Operations "HOL-Computational_Algebra.Primes"
begin

section \<open>The First Sylow Theorem\<close>

context Group
begin

interpretation left: left_translations_of_group G "(\<cdot>)" \<one>
  by unfold_locales

text \<open>The set of @{term n}-element subsets of @{term G}.\<close>

definition \<Omega> :: "nat \<Rightarrow> 'a set set"
  where "\<Omega> n = {B. B \<subseteq> G \<and> card B = n}"

text \<open>The left-translation action on @{term "\<Omega> n"}: each @{term "g \<in> G"} acts by mapping
  a subset @{term B} to @{term "(\<cdot>) g ` B = {g \<cdot> b | b. b \<in> B}"}.  We make the map
  extensional on @{term "\<Omega> n"} so it lies in @{term "\<Omega> n \<rightarrow>\<^sub>E \<Omega> n"}.\<close>

definition \<phi>_left :: "nat \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "\<phi>_left n g = restrict (\<lambda>B. (\<cdot>) g ` B) (\<Omega> n)"

text \<open>Membership in @{term "\<Omega> n"}.\<close>

lemma \<Omega>_memI [intro]: "\<lbrakk>B \<subseteq> G; card B = n\<rbrakk> \<Longrightarrow> B \<in> \<Omega> n"
  unfolding \<Omega>_def by simp

lemma \<Omega>_memD [dest]: "B \<in> \<Omega> n \<Longrightarrow> B \<subseteq> G \<and> card B = n"
  unfolding \<Omega>_def by simp

text \<open>The cardinality of @{term "\<Omega> n"} is the binomial coefficient @{term "card G choose n"}.\<close>

lemma card_\<Omega>:
  assumes "finite G"
  shows "card (\<Omega> n) = card G choose n"
  using assms by (simp add: \<Omega>_def n_subsets)

text \<open>Left multiplication by @{term "g \<in> G"} is injective on the carrier.\<close>

lemma left_mult_inj_on:
  assumes "g \<in> G"
  shows "inj_on ((\<cdot>) g) G"
  by (simp add: assms inj_on_def)

text \<open>Left multiplication maps subsets of @{term G} to subsets of @{term G}.\<close>

lemma left_mult_image_subset:
  assumes "g \<in> G" "B \<subseteq> G"
  shows "(\<cdot>) g ` B \<subseteq> G"
  using assms by auto

text \<open>Left multiplication preserves cardinality of subsets of @{term G}.\<close>

lemma left_mult_image_card:
  assumes "g \<in> G" "B \<subseteq> G"
  shows "card ((\<cdot>) g ` B) = card B"
  by (meson assms left_mult_inj_on card_image inj_on_subset)

text \<open>The action @{term "\<phi>_left n g"} maps @{term "\<Omega> n"} to itself.\<close>

lemma \<phi>_left_closed:
  assumes "g \<in> G" "B \<in> \<Omega> n"
  shows "(\<cdot>) g ` B \<in> \<Omega> n"
  using assms left_mult_image_subset left_mult_image_card by (fastforce simp: \<Omega>_def)

text \<open>The action applied to an element of @{term "\<Omega> n"}.\<close>

lemma \<phi>_left_apply [simp]:
  assumes "B \<in> \<Omega> n"
  shows "\<phi>_left n g B = (\<cdot>) g ` B"
  using assms unfolding \<phi>_left_def by simp

text \<open>Outside @{term "\<Omega> n"}, the action is undefined.\<close>

lemma \<phi>_left_undefined:
  assumes "B \<notin> \<Omega> n"
  shows "\<phi>_left n g B = undefined"
  using assms unfolding \<phi>_left_def by simp

text \<open>The action is extensional on @{term "\<Omega> n"}.\<close>

lemma \<phi>_left_extensional: "\<phi>_left n g \<in> extensional (\<Omega> n)"
  unfolding \<phi>_left_def by (rule restrict_extensional)

text \<open>The action maps @{term "\<Omega> n"} into itself.\<close>

lemma \<phi>_left_mapsto:
  assumes "g \<in> G"
  shows "\<phi>_left n g \<in> \<Omega> n \<rightarrow>\<^sub>E \<Omega> n"
  using assms \<phi>_left_closed \<phi>_left_extensional
  by (auto simp: PiE_def Pi_def extensional_def \<phi>_left_def restrict_def \<Omega>_def)

text \<open>Left multiplication by @{term "g \<in> G"} followed by @{term "inverse g"} is the identity
  on subsets of @{term G}.\<close>

lemma left_mult_image_inverse:
  assumes "g \<in> G" "B \<subseteq> G"
  shows "(\<cdot>) (inverse g) ` ((\<cdot>) g ` B) = B"
proof (intro iffI set_eqI)
  fix x
  assume "x \<in> (\<cdot>) (inverse g) ` ((\<cdot>) g ` B)"
  then obtain b where "b \<in> B" "x = inverse g \<cdot> (g \<cdot> b)" by blast
  then show "x \<in> B"
    by (metis assms invertible invertible_left_inverse2 subsetD) 
next
  fix x
  assume "x \<in> B" then show "x \<in> (\<cdot>) (inverse g) ` ((\<cdot>) g ` B)"
    by (metis assms imageI in_mono invertible invertible_left_inverse2)
qed

text \<open>The action @{term "\<phi>_left n g"} is a bijection on @{term "\<Omega> n"}.\<close>

lemma \<phi>_left_bij:
  assumes "g \<in> G"
  shows "bij_betw (\<phi>_left n g) (\<Omega> n) (\<Omega> n)"
proof (intro bij_betw_byWitness [where f' = "\<phi>_left n (inverse g)"] strip)
    fix B assume B: "B \<in> \<Omega> n"
    then have BG: "B \<subseteq> G" and gB: "(\<cdot>) g ` B \<in> \<Omega> n" 
      using assms B \<phi>_left_closed by auto
    with B show "\<phi>_left n (inverse g) (\<phi>_left n g B) = B"
      using assms BG \<phi>_left_apply left_mult_image_inverse
      by presburger
  next
    fix B assume B: "B \<in> \<Omega> n"
    then have BG: "B \<subseteq> G" by auto
    have gB: "(\<cdot>) (inverse g) ` B \<in> \<Omega> n"
      using assms B \<phi>_left_closed [of "inverse g"] by auto
    have "\<phi>_left n g (\<phi>_left n (inverse g) B) = (\<cdot>) g ` ((\<cdot>) (inverse g) ` B)"
      using B gB \<phi>_left_apply by presburger
    also have "\<dots> = B"
      using assms BG left_mult_image_inverse [of "inverse g"]
      by (metis invertible invertible_inverse_closed invertible_inverse_inverse)
    finally show "\<phi>_left n g (\<phi>_left n (inverse g) B) = B" .
  next
  show "\<phi>_left n g ` \<Omega> n \<subseteq> \<Omega> n"
    using assms \<phi>_left_closed by auto
  show "\<phi>_left n (inverse g) ` \<Omega> n \<subseteq> \<Omega> n"
    using assms \<phi>_left_closed [of "inverse g"] by auto
qed

text \<open>The action satisfies the unit law.\<close>

lemma \<phi>_left_unit: "\<phi>_left n \<one> = identity (\<Omega> n)"
  by (force simp: image_def left_unit \<phi>_left_def subsetD)

text \<open>The action satisfies the composition law.\<close>

lemma \<phi>_left_compose:
  assumes "g \<in> G" "h \<in> G"
  shows "\<phi>_left n (g \<cdot> h) = compose (\<Omega> n) (\<phi>_left n g) (\<phi>_left n h)"
proof (rule ext)
  fix B
  show "\<phi>_left n (g \<cdot> h) B = compose (\<Omega> n) (\<phi>_left n g) (\<phi>_left n h) B"
  proof (cases "B \<in> \<Omega> n")
    case True
    then have "compose (\<Omega> n) (\<phi>_left n g) (\<phi>_left n h) B = \<phi>_left n g ((\<cdot>) h ` B)"
      by (simp add: compose_eq)
    also have "\<dots> = (\<cdot>) g ` ((\<cdot>) h ` B)"
      using assms True \<phi>_left_closed by simp
    also have "\<dots> = (\<cdot>) (g \<cdot> h) ` B"
    proof -
      have "B \<subseteq> G" using True by auto
      then show ?thesis
        using associative [OF assms] by (simp add: image_def) (metis subsetD)
    qed
    also have "\<dots> = \<phi>_left n (g \<cdot> h) B" using True by simp
    finally show ?thesis by simp
  next
    case False
    then show ?thesis by (simp add: \<phi>_left_def compose_def)
  qed
qed

text \<open>The left-translation action on @{term "\<Omega> n"} is a @{locale Group_Action}.\<close>

theorem subset_action:
  "Group_Action G (\<cdot>) \<one> (\<phi>_left n) (\<Omega> n)"
proof 
  fix g assume "g \<in> G"
  then show "\<phi>_left n g \<in> Monoid.Units (\<Omega> n \<rightarrow>\<^sub>E \<Omega> n) (compose (\<Omega> n)) (identity (\<Omega> n))"
    by (simp add: \<phi>_left_bij \<phi>_left_mapsto transformations.Units_bij_betwD)
qed (auto simp: \<phi>_left_unit \<phi>_left_compose)

end

lemma (in Group) Sylow_abelian:
  assumes grp: "Abelian_Group G (\<cdot>) \<one>" "finite G"
    and prime: "prime p" and dvd: "p dvd card G"
  shows "\<exists>g\<in>G. element_order g = p"
  using dvd grp
proof (induction "card G" arbitrary: G "(\<cdot>)" "\<one>" rule: less_induct)
  case less
  interpret G: Abelian_Group G composition unit
    using \<open>Abelian_Group G composition unit\<close> .
  have "card G \<noteq> 1"
    using less.prems(1) prime by force
  then have "card G > 1"
    using less.prems(3) nat_neq_iff by fastforce
  with less obtain a where a: "a\<in>G" "a \<noteq> unit"
    by (metis One_nat_def card_le_Suc0_iff_eq linorder_not_le)
  let ?r = "G.element_order a"
  show ?case
  proof (cases "p dvd ?r")
    case True
    then obtain r' where "?r = p * r'"
      by auto
    have fin: "finite G" using less by simp
    have aG: "G.power a r' \<in> G" using a by simp
    from \<open>?r = p * r'\<close>
    have pow_eq: "G.power (G.power a r') p = unit"
      by (metis G.power_element_order G.power_mult a(1) fin mult.commute)
    then have dvd_p: "G.element_order (G.power a r') dvd p"
      using G.element_order_dvd[OF fin aG] by blast
    have "G.element_order (G.power a r') \<noteq> 1"
    proof
      assume "G.element_order (G.power a r') = 1"
      then have "G.element_order a dvd r'"
        using aG G.element_order_dvd[OF fin \<open>a\<in>G\<close>] G.power_element_order[OF fin aG]
        by auto
      then show False
        using G.element_order_pos[OF fin \<open>a\<in>G\<close>] \<open>?r = p * r'\<close> prime by simp
    qed
    with dvd_p show ?thesis using aG
      using prime prime_nat_iff by blast
  next
    case False
    then have not_dvd: "\<not> p dvd ?r" .
    have fin: "finite G" using less by simp
    define C where "C = G.cyclic_subgroup a"
    have C_sub: "C \<subseteq> G" unfolding C_def using G.cyclic_subgroup_subset a by simp
    have card_C: "card C = ?r" unfolding C_def using G.card_cyclic_subgroup[OF fin \<open>a\<in>G\<close>] .
    interpret sub_C: Subgroup C G composition unit
      unfolding C_def using G.cyclic_subgroup_is_subgroup[OF fin \<open>a\<in>G\<close>] .
    interpret CG: subgroup_of_abelian_group C G composition unit ..
    have card_quotient: "card CG.Factor_Group = CG.index"
      using CG.card_Factor_Group less by simp
    then have \<open>card C < card G\<close>
      by (metis C_sub card_C card_mono fin le_neq_implies_less less.prems(1) not_dvd)

    define FactG where "FactG \<equiv> some_elem ` CG.Factor_Group"
    define comp where "comp \<equiv> class_representatives.rep_comp G CG.Factor_Group CG.quotient_composition"
    interpret iso: group_isomorphism "restrict some_elem CG.Factor_Group" 
      CG.Factor_Group CG.quotient_composition "CG.Class unit" 
      FactG comp "some_elem (CG.Class unit)"
      using CG.group_isomorphism_Factor_Group_class_reps 
      by (force simp: FactG_def local.comp_def)
    have *: "card C * card FactG = card G"
      using CG.card_class_reps CG.lagrange FactG_def card_quotient fin by presburger
    then have "card FactG > 1"
      by (metis \<open>card C < card G\<close> mult.commute nat_mult_1 nat_mult_less_cancel_disj)
    have "finite FactG"
      using CG.class_reps_subset FactG_def fin finite_subset by blast
    have "card FactG < card G"
      using \<open>card G > 1\<close>
      by (metis "*" G.power_1 G.power_element_order a card_C dvd_mult_cancel2 dvd_triv_right
          fin less_nat_zero_code nat_dvd_not_less nat_neq_iff)
    have \<open>p dvd card FactG\<close>
      by (metis "*" card_C less.prems(1) not_dvd prime prime_dvd_multD)
    have abel_FactG: "Abelian_Group FactG comp (some_elem (CG.Class unit))"
      using CG.abelian_class_reps[OF CG.quotient_abelian] by (simp add: FactG_def local.comp_def)
    obtain g where g: "g \<in> FactG" "Monoid.element_order comp (some_elem (CG.Class unit)) g = p"
      using less(1)[of FactG comp "some_elem (CG.Class unit)"]
        \<open>card FactG < card G\<close> \<open>p dvd card FactG\<close> abel_FactG \<open>finite FactG\<close> \<open>1 < card FactG\<close>
      by auto
    then obtain X where X: "X \<in> CG.Factor_Group" "some_elem X = g" by (auto simp: FactG_def)
    obtain g' where g': "g' \<in> G" "X = CG.Class g'"
      using CG.representant_exists[OF X(1)] by auto
    have finFG: "finite CG.Factor_Group"
      using CG.Partition_def fin finite_imageI by auto
    then have nat_dvd: "CG.quotient.element_order (CG.Class g') dvd G.element_order g'"
      by (metis CG.natural.commutes_with_power CG.quotient.element_order_dvd G.power_element_order
          X(1) fin g')
    have "iso.image.sub.element_order (restrict some_elem CG.Factor_Group X) 
              dvd CG.quotient.element_order X"
      using iso.element_order_image_dvd[OF finFG \<open>finite FactG\<close> X(1)] by simp
    then have "p dvd CG.quotient.element_order (CG.Class g')"
      using X g g' by auto
    then show ?thesis
      using G.element_order_power_prime fin g'(1) gcd_nat.trans nat_dvd prime by blast
  qed
qed

subsection \<open>Conjugation, Center, and Centralizer\<close>

context Group begin

text \<open>The conjugation action: @{term g} acts on @{term x} by @{text "g x g⁻¹"}.
  We use @{text "g x g⁻¹"} rather than @{text "g⁻¹ x g"} so that the map
  @{text "g \<mapsto> (x \<mapsto> g x g⁻¹)"} is a group homomorphism (not anti-homomorphism).\<close>

definition conjugation :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "conjugation g x = (if g \<in> G \<and> x \<in> G then g \<cdot> x \<cdot> inverse g else x)"

lemma conjugation_closed:
  assumes "g \<in> G" "x \<in> G"
  shows "conjugation g x \<in> G"
  using assms by (simp add: conjugation_def)

lemma conjugation_unit:
  assumes "x \<in> G"
  shows "conjugation \<one> x = x"
  using assms by (simp add: conjugation_def)

lemma conjugation_compose:
  assumes "g \<in> G" "h \<in> G"
  shows "conjugation (g \<cdot> h) x = conjugation g (conjugation h x)"
  by (simp add: assms associative conjugation_def inverse_composition_commute)

lemma conjugation_outside [simp]:
  "x \<notin> G \<Longrightarrow> conjugation g x = x"
  by (simp add: conjugation_def)

lemma conjugation_bij:
  assumes "g \<in> G"
  shows "bij_betw (conjugation g) G G"
proof (rule bij_betwI)
  show "\<And>x. x \<in> G \<Longrightarrow> conjugation (inverse g) (conjugation g x) = x"
    using assms by (simp add: conjugation_def associative invertible_left_inverse2)
  show "\<And>y. y \<in> G \<Longrightarrow> conjugation g (conjugation (inverse g) y) = y"
    using assms by (simp add: conjugation_def associative invertible_right_inverse2)
qed (auto simp: conjugation_closed assms)

text \<open>The restricted conjugation map, suitable for the @{locale Group_Action} locale.\<close>

definition \<phi>_conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "\<phi>_conj g = restrict (conjugation g) G"

lemma \<phi>_conj_apply [simp]:
  assumes "g \<in> G" "x \<in> G"
  shows "\<phi>_conj g x = g \<cdot> x \<cdot> inverse g"
  using assms by (simp add: \<phi>_conj_def conjugation_def)

lemma \<phi>_conj_outside [simp]:
  "x \<notin> G \<Longrightarrow> \<phi>_conj g x = undefined"
  by (simp add: \<phi>_conj_def)

lemma \<phi>_conj_extensional: "\<phi>_conj g \<in> extensional G"
  unfolding \<phi>_conj_def by (rule restrict_extensional)

lemma \<phi>_conj_mapsto:
  assumes "g \<in> G"
  shows "\<phi>_conj g \<in> G \<rightarrow>\<^sub>E G"
  using assms by (auto simp: PiE_def Pi_def \<phi>_conj_def conjugation_closed)

lemma \<phi>_conj_bij:
  assumes "g \<in> G"
  shows "bij_betw (\<phi>_conj g) G G"
  by (simp add: \<phi>_conj_def assms conjugation_bij)

lemma \<phi>_conj_unit: "\<phi>_conj \<one> = identity G"
  by auto

lemma \<phi>_conj_compose:
  assumes "g \<in> G" "h \<in> G"
  shows "\<phi>_conj (g \<cdot> h) = compose G (\<phi>_conj g) (\<phi>_conj h)"
  by (force simp: conjugation_closed \<phi>_conj_def assms compose_def conjugation_compose)

theorem conjugation_action: "Group_Action G (\<cdot>) \<one> \<phi>_conj G"
proof 
  fix g assume "g \<in> G"
  then show "\<phi>_conj g \<in> Monoid.Units (G \<rightarrow>\<^sub>E G) (compose G) (identity G)"
    by (simp add: \<phi>_conj_bij \<phi>_conj_mapsto transformations.Units_bijective)
qed (auto simp: \<phi>_conj_unit \<phi>_conj_compose)


text \<open>The center of @{term G}: elements that commute with everything.\<close>

definition center :: "'a set"
  where "center = {z \<in> G. \<forall>g \<in> G. z \<cdot> g = g \<cdot> z}"

text \<open>The centralizer of an element @{term y}: elements that commute with @{term y}.\<close>

definition centralizer :: "'a \<Rightarrow> 'a set"
  where "centralizer y = {g \<in> G. g \<cdot> y = y \<cdot> g}"

lemma center_subset: "center \<subseteq> G"
  by (auto simp: center_def)

lemma center_mem_iff:
  assumes "z \<in> G"
  shows "z \<in> center \<longleftrightarrow> (\<forall>g \<in> G. z \<cdot> g = g \<cdot> z)"
  using assms by (simp add: center_def)

lemma centralizer_subset: "centralizer y \<subseteq> G"
  by (auto simp: centralizer_def)

lemma centralizer_mem_iff:
  assumes "g \<in> G" "y \<in> G"
  shows "g \<in> centralizer y \<longleftrightarrow> g \<cdot> y = y \<cdot> g"
  using assms by (simp add: centralizer_def)

text \<open>Interpret the conjugation action to access orbits, stabilizers, and fixed points.\<close>

interpretation conj: Group_Action G "(\<cdot>)" \<one> \<phi>_conj G
  by (rule conjugation_action)

lemma center_eq_fixed_points: "center = conj.fixed_points"
  unfolding center_def conj.fixed_points_def conj.stabilizer_def
  by (force simp: subset_iff simp flip: commute_iff_inverse)

text \<open>The class equation separates the singleton conjugacy classes, which are exactly the
  center, from the nontrivial conjugacy classes.\<close>

theorem class_equation:
  assumes "finite G"
  shows "card G = card center + (\<Sum>X \<in> conj.nontrivial_orbits. card X)"
  using conj.fixed_point_class_equation[OF assms]
  by (simp add: center_eq_fixed_points)

lemma centralizer_eq_stabilizer:
  assumes "y \<in> G"
  shows "centralizer y = conj.stabilizer y"
  using assms
  by (auto simp: centralizer_def commute_iff_inverse conj.stabilizer_def)


text \<open>The center is a subgroup of @{term G}.\<close>

lemma inverse_commutes:
  assumes "x \<in> G" "\<forall>g \<in> G. x \<cdot> g = g \<cdot> x"
  shows "\<forall>g \<in> G. inverse x \<cdot> g = g \<cdot> inverse x"
proof
  fix g assume gG: "g \<in> G"
  have "x \<cdot> (inverse x \<cdot> g) = g"
    using assms(1) gG by (simp add: associative [symmetric])
  moreover have "x \<cdot> (g \<cdot> inverse x) = g"
    by (simp add: assms associative gG)
  ultimately show "inverse x \<cdot> g = g \<cdot> inverse x"
    using assms(1) gG
    by (metis composition_closed invertible invertible_inverse_closed
        invertible_left_inverse2)
qed

lemma center_subgroup: "Subgroup center G (\<cdot>) \<one>"
proof (rule subgroupI)
  fix x y assume "x \<in> center" "y \<in> center"
  then show "x \<cdot> y \<in> center"
    unfolding center_def mem_Collect_eq
    by (metis associative composition_closed)
next
  fix x assume x: "x \<in> center"
  then show "invertible x" using center_subset by auto
  show "inverse x \<in> center"
    using x center_subset inverse_commutes by (auto simp: center_def)
qed (auto simp add: center_def)


text \<open>The center is an abelian group.\<close>

lemma center_abelian: "Abelian_Group center (\<cdot>) \<one>"
proof -
  interpret CG: subgroup_of_group center G "(\<cdot>)" \<one>
    by (simp add: Group_axioms center_subgroup subgroup_of_group_def)
  show ?thesis
  proof 
    fix x y assume x: "x \<in> center" and y: "y \<in> center"
    then show "x \<cdot> y = y \<cdot> x"
      using center_subset center_def by blast
  qed
qed


text \<open>The centralizer of @{term "y \<in> G"} is a subgroup of @{term G}.\<close>

lemma centralizer_subgroup:
  assumes "y \<in> G"
  shows "Subgroup (centralizer y) G (\<cdot>) \<one>"
  using conj.stabilizer_subgroup[OF assms] centralizer_eq_stabilizer[OF assms] by simp

text \<open>If @{term y} is not in the center, then its centralizer is a proper subgroup.\<close>

lemma centralizer_proper:
  assumes "y \<in> G" "y \<notin> center" "finite G"
  shows "card (centralizer y) < card G"
proof -
  have "centralizer y \<subseteq> G" by (rule centralizer_subset)
  moreover have "centralizer y \<noteq> G"
    by (metis assms center_mem_iff centralizer_mem_iff)
  ultimately show ?thesis using assms(3) by (simp add: psubsetI psubset_card_mono)
qed


end

text \<open>Preimage of a subgroup under a group homomorphism is a subgroup.\<close>

lemma (in group_homomorphism) preimage_subgroup:
  assumes sub: "Subgroup S G' (\<cdot>') \<one>'"
  defines "H \<equiv> {g \<in> G. \<eta> g \<in> S}"
  shows "Subgroup H G (\<cdot>) \<one>"
proof (rule source.subgroupI)
  show "H \<subseteq> G" "\<one> \<in> H"  
    using commutes_with_unit sub Submonoid.sub_unit_closed by (fastforce simp: H_def Subgroup_def)+
next
  fix x y assume "x \<in> H" "y \<in> H"
  then have xG: "x \<in> G" and yG: "y \<in> G" and xS: "\<eta> x \<in> S" and yS: "\<eta> y \<in> S"
    unfolding H_def by auto
  have "\<eta> (x \<cdot> y) = \<eta> x \<cdot>' \<eta> y" using commutes_with_composition xG yG by auto
  also have "\<dots> \<in> S" using sub xS yS
    by (meson Group_def Monoid.composition_closed Subgroup_def)
  finally show "x \<cdot> y \<in> H" unfolding H_def using xG yG by auto
next
  fix x assume "x \<in> H"
  then have xG: "x \<in> G" and xS: "\<eta> x \<in> S" unfolding H_def by auto
  show "source.invertible x" using xG by auto
  have "\<eta> (source.inverse x) = target.inverse (\<eta> x)"
    using invertible_commutes_with_inverse xG by blast
  also have "\<dots> \<in> S"
    using sub target.Gen_def target.Gen_subgroup_eq target.generate.inv xS by blast
  finally show "source.inverse x \<in> H" 
    by (auto simp: H_def xG)
qed

text \<open>Cardinality of the preimage: each coset in the subgroup contributes @{term "card (Ker)"} elements.\<close>

lemma (in group_homomorphism) preimage_card:
  assumes sub: "Subgroup S G' (\<cdot>') \<one>'" and fin: "finite G" and fin': "finite G'"
    and img: "S \<subseteq> \<eta> ` G"
  defines "H \<equiv> {g \<in> G. \<eta> g \<in> S}"
  shows "card H = card S * card Ker"
proof -
  \<comment> \<open>Partition @{term H} into fibers: for each @{term "s \<in> S"}, the fiber is
    @{text "{g \<in> G. \<eta> g = s}"}, which is a kernel coset.\<close>
  define fiber where "fiber s = {g \<in> G. \<eta> g = s}" for s
  have H_eq: "H = (\<Union>s \<in> S. fiber s)"
    unfolding H_def fiber_def by auto
  have fib_class: "\<exists>g \<in> G. fiber s = kernel.Class g" if "s \<in> S" for s
  \<comment> \<open>Each fiber over @{term "s \<in> S"} is nonempty.\<close>
  proof -
    obtain g where gG: "g \<in> G" and sg: "\<eta> g = s"
      using \<open>s \<in> S\<close> img by auto
    have "fiber s = kernel.Class g"
    proof (intro set_eqI iffI)
      fix x assume "x \<in> fiber s"
      then have xG: "x \<in> G" and "\<eta> x = s" "\<eta> x = \<eta> g" 
        unfolding fiber_def using sg by auto
      then have "\<eta> (inverse x \<cdot> g) = \<one>'"
        using invertible_image_lemma sg xG \<open>g \<in> G\<close> by (auto simp add: commutes_with_composition)
      then have "inverse x \<cdot> g \<in> Ker"
        using Ker_memI gG xG by blast
      then have "(x, g) \<in> kernel.Congruence"
        by (metis gG kernel.CongruenceI kernel.symmetric source.invertible
            source.invertible_right_inverse2 xG)
      then show "x \<in> kernel.Class g"
        by (rule kernel.ClassI)
    next
      fix x assume "x \<in> kernel.Class g"
      then have "(x, g) \<in> kernel.Congruence"
        using kernel.ClassD gG by blast
      then have xG: "x \<in> G" using kernel.left_closed by auto
      from \<open>(x, g) \<in> kernel.Congruence\<close> obtain k where kK: "k \<in> Ker" and xgk: "x = g \<cdot> k"
        using kernel.CongruenceD by auto
      then have "\<eta> x = \<eta> g \<cdot>' \<eta> k"
        using commutes_with_composition gG Ker_closed[OF kK] by auto
      then show "x \<in> fiber s" unfolding fiber_def using xG
        using Ker_image gG kK sg by force
    qed
    then show "\<exists>g \<in> G. fiber s = kernel.Class g" using gG by auto
  qed
  \<comment> \<open>Each fiber has exactly @{term "card Ker"} elements.\<close>
  have fib_card: "\<And>s. s \<in> S \<Longrightarrow> card (fiber s) = card Ker"
    by (metis fib_class kernel.Class_cardinality)
  \<comment> \<open>The fibers are pairwise disjoint.\<close>
  have fib_disj: "disjoint_family_on fiber S"
    unfolding disjoint_family_on_def fiber_def by auto
  \<comment> \<open>Fibers are finite (since @{term G} is finite).\<close>
  have fib_fin: "\<And>s. s \<in> S \<Longrightarrow> finite (fiber s)"
    unfolding fiber_def using fin by auto
  have "finite S"
    using fin' sub by (meson finite_subset Subgroup_def Submonoid.subset)
  then show ?thesis
    using card_UN_disjoint'[OF fib_disj fib_fin] by (simp add: H_eq fib_card)
qed

subsection \<open>First Sylow Theorem\<close>

theorem (in Group) Sylow_I:
  fixes p :: nat and m :: nat
  assumes "prime p"
    and "finite G"
    and "p ^ m dvd card G"
  shows "\<exists>H. Subgroup H G (\<cdot>) \<one> \<and> card H = p ^ m"
  using assms(3,2) Group_axioms 
proof (induction "card G" arbitrary: G "(\<cdot>)" "\<one>" m rule: less_induct)
  case less
  then interpret G: Group G composition unit
    by (simp add: Group_def)
  show ?case
  proof (cases "m = 0")
    case True
    then have "Subgroup {unit} G composition unit \<and> card {unit} = p ^ m"
      by (auto intro: G.subgroupI)
    then show ?thesis by blast
  next
    case False
    have fin: "finite G" using less.prems by simp
    have pa_dvd: "p ^ m dvd card G" using less.prems by simp
    have p_dvd_G: "p dvd card G"
      using False pa_dvd by auto
    show ?thesis
    proof (cases "p dvd card G.center")
      case True
      \<comment> \<open>Case 2: @{term p} divides @{term "card G.center"}.\<close>
      \<comment> \<open>Step 1: By Cauchy's theorem for abelian groups, the center contains
        an element @{term z} of order @{term p}.\<close>
      have center_fin: "finite G.center"
        using fin G.center_subset finite_subset by blast
      interpret Z: Group G.center composition unit
        using G.center_subgroup Subgroup.axioms(2) by force
      obtain z where zZ: "z \<in> G.center" and z_ord: "Z.element_order z = p"
        using Z.Sylow_abelian[OF G.center_abelian center_fin \<open>prime p\<close> True]
        by auto
      have zG: "z \<in> G" using zZ G.center_subset by auto
      have z_comm: "\<And>g. g \<in> G \<Longrightarrow> composition z g = composition g z"
        using zZ G.center_def by auto
          \<comment> \<open>The element orders in the center and in @{term G} coincide.\<close>
      have "Z.power z n = G.power z n" for n
        by (induction n) auto
      then have z_ord_G: "G.element_order z = p" using z_ord
        unfolding Z.element_order_def G.element_order_def by simp
      have p_pos: "p > 0" using \<open>prime p\<close> prime_gt_0_nat by blast
      \<comment> \<open>Step 2: Build the cyclic subgroup @{text "N = \<langle>z\<rangle>"} of order @{term p}.\<close>
      define N where "N = G.power z ` {..<p}"
      have N_alt: "N = range (G.power z)"
        using G.power_mod_order[OF fin zG] p_pos z_ord_G
        by (fastforce simp: N_def)
      have N_sub: "N \<subseteq> G" unfolding N_def using zG by auto
      have card_N: "card N = p"
        using G.power_inj_on_order[OF fin zG] z_ord_G
        by (simp add: N_def card_image)
      have unit_N: "unit \<in> N" unfolding N_alt
        by (metis G.power_0 rangeI)
      have comp_N: "composition x y \<in> N" if "x \<in> N" "y \<in> N" for x y
        using that zG by (force simp: N_alt simp flip: G.power_add)
      have inv_N: "G.inverse x \<in> N" if "x \<in> N" for x
      proof -
        obtain i where xi: "x = G.power z i"
          using that N_alt \<open>x \<in> N\<close> by blast
        have xG: "x \<in> G" using that N_sub by auto
        define y where "y = G.power z ((p - 1) * i)"
        have yN: "y \<in> N" unfolding y_def N_alt by auto
        have yG: "y \<in> G" using yN N_sub by auto
        have "composition x y = G.power z (i + (p - 1) * i)"
          unfolding xi y_def using zG G.power_add by auto
        also have "i + (p - 1) * i = p * i" using p_pos by (simp add: algebra_simps)
        also have "G.power z (p * i) = G.power (G.power z p) i"
          using zG G.power_mult by simp
        also have "G.power (G.power z p) i = unit"
          using G.power_element_order[OF fin zG] z_ord_G by simp
        finally have xy: "composition x y = unit" .
        then show ?thesis
          by (metis G.center_mem_iff G.inverse_equality Z.power_closed xG xi yG yN zZ)
      qed
      have sub_N: "Subgroup N G composition unit"
        using G.subgroupI N_sub comp_N inv_N unit_N by blast
      \<comment> \<open>Step 3: @{term N} is m normal subgroup of @{term G} (since @{term z} is central).\<close>
      have N_normal: "normal_subgroup N G composition unit"
      proof -
        interpret NG: subgroup_of_group N G composition unit
          by (simp add: G.Group_axioms sub_N subgroup_of_group_def)
        show ?thesis
        proof (rule NG.Left_equals_Right_coset_implies_normality)
          fix g assume gG: "g \<in> G"
          show "NG.Left_Coset g N = NG.Right_Coset N g"
          proof -
            have power_comm: "composition g (G.power z i) = composition (G.power z i) g" for i
            proof (induction i)
              case 0
              then show ?case by (simp add: gG)
            next
              case (Suc i) then show ?case
                by (metis G.center_mem_iff G.power_closed Z.power_closed gG zG zZ)
            qed
            show ?thesis
            proof (intro set_eqI iffI)
              fix x
              assume "x \<in> NG.Left_Coset g N"
              then obtain n where nN: "n \<in> N" and xeq: "x = composition g n"
                by (auto simp: NG.Left_Coset_def)
              from nN obtain i where ni: "n = G.power z i"
                using N_alt by blast
              then show "x \<in> NG.Right_Coset N g"
                using nN power_comm xeq by auto
            next
              fix x
              assume "x \<in> NG.Right_Coset N g"
              then obtain n where nN: "n \<in> N" and xeq: "x = composition n g"
                by (auto simp: NG.Right_Coset_def)
              from nN obtain i where ni: "n = G.power z i"
                using N_alt by blast
              have "x = composition g n"
                using xeq ni power_comm by simp
              then show "x \<in> NG.Left_Coset g N"
                using nN by (auto simp: NG.Left_Coset_def)
            qed
          qed
        qed
      qed
      \<comment> \<open>Step 4: Form the quotient group @{text "G/N"} and apply the induction hypothesis.\<close>
      interpret NG: normal_subgroup N G composition unit
        using N_normal .
      have card_FG: "card NG.Factor_Group = NG.index"
        using NG.card_Factor_Group fin by simp
      have card_G_eq: "card G = card N * NG.index"
        using NG.lagrange fin by simp
      then have card_G_eq': "card G = p * card NG.Factor_Group"
        using card_N card_FG by simp
      have FG_lt: "card NG.Factor_Group < card G"
        using assms(1) card_G_eq' fin prime_nat_iff zG by fastforce
      show ?thesis
      proof -
        \<comment> \<open>The quotient group is finite.\<close>
        have fin_FG: "finite NG.Factor_Group"
          using fin NG.partition partition_on_def by (metis finite_UnionD)
        \<comment> \<open>Divisibility: @{term "p ^ (m - 1)"} divides @{term "card NG.Factor_Group"}.\<close>
        have "p ^ m dvd p * card NG.Factor_Group"
          using pa_dvd card_G_eq' by simp
        then have pa1_dvd: "p ^ (m - 1) dvd card NG.Factor_Group"
          by (metis False dvd_mult_cancel p_pos power_eq_if)
        \<comment> \<open>Apply the induction hypothesis to the class-representative group (type @{typ \<open>'a set\<close>}).\<close>
        define FactG where "FactG \<equiv> some_elem ` NG.Factor_Group"
        define fcomp where "fcomp \<equiv> class_representatives.rep_comp G NG.Factor_Group NG.quotient_composition"
        interpret iso: group_isomorphism "restrict some_elem NG.Factor_Group"
          NG.Factor_Group NG.quotient_composition "NG.Class unit"
          FactG fcomp "some_elem (NG.Class unit)"
          using NG.group_isomorphism_Factor_Group_class_reps
          by (force simp: FactG_def fcomp_def)
        interpret Group_FactG: Group FactG fcomp "some_elem (NG.Class unit)"
          using iso.target.Group_axioms .
        have fin_FactG: "finite FactG"
          using NG.class_reps_subset FactG_def fin finite_subset by blast
        have card_FactG: "card FactG = card NG.Factor_Group"
          using NG.card_class_reps FactG_def by simp
        have FG_lt': "card FactG < card G"
          using FG_lt card_FactG by simp
        obtain K' where
          K'_sub: "Subgroup K' FactG fcomp (some_elem (NG.Class unit))" and
          K'_card: "card K' = p ^ (m - 1)"
          by (metis FG_lt' card_FactG fin_FactG iso.target.Group_axioms less.hyps pa1_dvd)
        \<comment> \<open>Transfer @{term K'} back to @{term NG.Factor_Group} via the inverse isomorphism.\<close>
        define inv_\<eta> where "inv_\<eta> \<equiv> restrict (inv_into NG.Factor_Group (restrict some_elem NG.Factor_Group)) FactG"
        interpret inv_iso: group_isomorphism inv_\<eta> FactG fcomp "some_elem (NG.Class unit)"
          NG.Factor_Group NG.quotient_composition "NG.Class unit"
          using iso.inverse_group_isomorphism by (simp add: inv_\<eta>_def)
        define K where "K \<equiv> inv_\<eta> ` K'"
        have K_sub: "Subgroup K NG.Factor_Group NG.quotient_composition (NG.Class unit)"
          unfolding K_def using inv_iso.image_subgroup[OF K'_sub] .
        have "inj_on inv_\<eta> K'"
          using inv_iso.injective K'_sub
          by (meson inj_on_subset Subgroup_def Submonoid.subset)
        then have K_card: "card K = p ^ (m - 1)"
          unfolding K_def using K'_card card_image by metis

        \<comment> \<open>Pull back @{term K} to @{term G} via the natural homomorphism.\<close>
        define H where "H = {g \<in> G. NG.Class g \<in> K}"
        \<comment> \<open>@{term H} is m subgroup of @{term G}.\<close>
        interpret NG_hom: group_homomorphism NG.Class G composition unit
                                     NG.Factor_Group NG.quotient_composition "NG.Class unit"
          by (simp add: G.Group_axioms NG.natural.Monoid_homomorphism_axioms NG.quotient.Group_axioms
              group_homomorphism_def)
        have H_sub: "Subgroup H G composition unit"
          unfolding H_def using K_sub NG_hom.preimage_subgroup by blast 
        \<comment> \<open>Compute @{term "card H"}.\<close>
        have K_in_image: "K \<subseteq> NG.Class ` G"
          using K_sub NG.natural.surjective by (metis Subgroup_def Submonoid.subset)
        have "card H = card K * card NG_hom.Ker"
          unfolding H_def
          using NG_hom.preimage_card[OF K_sub fin fin_FG K_in_image] .
        \<comment> \<open>The kernel of the natural map is @{term N}, so @{term "card NG_hom.Ker = p"}.\<close>
        moreover have "NG_hom.Ker = N"
        proof (intro set_eqI iffI)
          fix x
          assume "x \<in> NG_hom.Ker" then show "x \<in> N"
            by (metis NG.Class_unit_normal_subgroup NG.Class_self NG_hom.Ker_image NG_hom.kernel.sub)
        next
          fix x
          assume "x \<in> N" then show "x \<in> NG_hom.Ker"
            by (metis G.left_unit NG.Class_eq NG.CongruenceI NG.sub NG_hom.Ker_memI unit_N)
        qed
        moreover have "card K * card N = p ^ m"
          by (simp add: False power_eq_if K_card card_N)
        ultimately have "card H = p ^ m" by simp
        with H_sub show ?thesis by blast
      qed
    next
      case False
      \<comment> \<open>Case 1: @{term p} does not divide @{term "card G.center"}.\<close>
      interpret conj: Group_Action G composition unit G.\<phi>_conj G
        by (rule G.conjugation_action)
      \<comment> \<open>The conjugation action partitions @{term G} into orbits.
        By orbit-stabilizer, the class equation gives
        @{text "|G| = |Z(G)| + \<Sigma> [G : C(y_j)]"}.
        Since @{term p} divides @{term "card G"} but not @{term "card G.center"},
        some non-trivial orbit must have size not divisible by @{term p}.\<close>
      \<comment> \<open>There exists m non-central @{term y} whose orbit size is not divisible by @{term p}.\<close>
      \<comment> \<open>The class equation gives @{text "|G| = |Z(G)| + \<Sigma> [G : C(y_j)]"}.
        Since @{term p} divides @{term "card G"} but not @{term "card G.center"},
        some non-trivial conjugacy class must have size coprime to @{term p}.\<close>
      obtain y where yG: "y \<in> G" and y_not_center: "y \<notin> G.center"
        and not_dvd_orbit: "\<not> p dvd card (conj.orbit y)"
      proof -
        \<comment> \<open>If every non-center orbit is divisible by @{term p}, then
          @{term p} divides @{term "card G.center"}, contradicting @{term False}.\<close>
        have "\<not> (\<forall>y \<in> G. y \<notin> G.center \<longrightarrow> p dvd card (conj.orbit y))"
        proof
          assume all: "\<forall>y \<in> G. y \<notin> G.center \<longrightarrow> p dvd card (conj.orbit y)"
          have "p dvd card (G - G.center)"
            using conj.dvd_card_nonfixed_points[OF fin]
            by (simp add: G.center_eq_fixed_points all)
          with False show False
            by (metis G.center_subset card_Diff_subset card_mono dvd_diffD1 fin finite_subset p_dvd_G)
        qed
        then show ?thesis using that by blast
      qed

      define X where "X \<equiv> conj.orbit y"
      \<comment> \<open>The orbit has size @{text "[G : C(y)]"} by orbit-stabilizer.\<close>
      have orbit_stab: "card G = card X * card (conj.stabilizer y)"
        using conj.orbit_stabilizer_card[OF yG fin] X_def by simp
      have stab_eq: "conj.stabilizer y = G.centralizer y"
        using G.centralizer_eq_stabilizer[OF yG] by simp
      \<comment> \<open>Since @{term "p ^ m"} divides @{term "card X * card (G.centralizer y)"}
        and @{term p} does not divide @{term "card X"}, we get
        @{term "p ^ m dvd card (G.centralizer y)"}.\<close>
      have "coprime (card X) (p ^ m)"
        using X_def assms(1) not_dvd_orbit prime_imp_power_coprime by blast
      then have pa_dvd_cent: "p ^ m dvd card (G.centralizer y)"
        by (metis pa_dvd orbit_stab stab_eq coprime_dvd_mult_right_iff coprime_commute)
      have cent_proper: "card (G.centralizer y) < card G"
        using G.centralizer_proper[OF yG y_not_center fin] .
      \<comment> \<open>The centralizer is m subgroup, hence m group.\<close>
      have cent_sub: "Subgroup (G.centralizer y) G composition unit"
        using G.centralizer_subgroup[OF yG] .
      have cent_grp: "Group (G.centralizer y) composition unit"
        using Subgroup.axioms(2)[OF cent_sub] .
      have cent_fin: "finite (G.centralizer y)"
        using fin G.centralizer_subset by (rule rev_finite_subset)
      \<comment> \<open>By the induction hypothesis, the centralizer has m subgroup of order @{term "p ^ m"}.\<close>
      obtain H where H_sub: "Subgroup H (G.centralizer y) composition unit"
                 and H_card: "card H = p ^ m"
        using cent_fin cent_grp cent_proper less.hyps pa_dvd_cent by blast
      \<comment> \<open>A subgroup of m subgroup is m subgroup of @{term G}.\<close>
      have "Subgroup H G composition unit"
        using subgroup_transitive[OF H_sub cent_sub] .
      with H_card show ?thesis by auto
    qed
  qed
qed

text \<open>Cauchy's theorem for arbitrary finite groups is now an immediate corollary of the
  first Sylow theorem: taking @{term "m = 1"} yields a subgroup of order @{term p}, and a
  group of prime order is cyclic, so any of its non-unit elements has order exactly @{term p}.
  (For abelian groups this was already available as \<open>Sylow_abelian\<close>.)\<close>

corollary (in Group) Cauchy:
  fixes p :: nat
  assumes prime: "prime p" and fin: "finite G" and dvd: "p dvd card G"
  shows "\<exists>g\<in>G. element_order g = p"
proof -
  have "p ^ 1 dvd card G" using dvd by simp
  then obtain H where H: "Subgroup H G (\<cdot>) \<one>" and cardH: "card H = p"
    using Sylow_I[OF prime fin, of 1] by auto
  interpret H: Subgroup H G "(\<cdot>)" \<one> by (rule H)
  have p2: "p \<ge> 2" using prime by (simp add: prime_ge_2_nat)
  have finH: "finite H" using fin H.subset by (rule rev_finite_subset)
  have "card H \<noteq> 1" using p2 cardH by simp
  then have "H \<noteq> {\<one>}"
    using is_singleton_altdef by blast
  then obtain g where gH: "g \<in> H" and gne: "g \<noteq> \<one>"
    by blast
  \<comment> \<open>The element order comes from @{term "(\<cdot>)"} and @{term \<one>} alone, so it
    agrees @{term H} and @{term G}.\<close>
  have dvdp: "H.sub.element_order g dvd p"
    using H.sub.element_order_dvd_card[OF finH gH] cardH by simp
  have ordne1: "H.sub.element_order g \<noteq> 1"
    using fin gH gne power_element_order by force
  have "H.sub.element_order g = p"
    using dvdp ordne1 prime by (auto simp: prime_nat_iff)
  with gH H.subset show ?thesis by blast
qed


section \<open>The Second Sylow Theorem\<close>

text \<open>If H is a subgroup of a group G and g is in G, then the conjugate
  @{text "g H g⁻¹"} is again a subgroup of G.\<close>

context Group begin

definition conjugate_subgroup :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "conjugate_subgroup g H = conjugation g ` H"

lemma conjugate_subgroup_mem_iff:
  assumes "g \<in> G" "H \<subseteq> G" "x \<in> G"
  shows "x \<in> conjugate_subgroup g H \<longleftrightarrow> (\<exists>h \<in> H. x = g \<cdot> h \<cdot> inverse g)"
  unfolding conjugate_subgroup_def using assms
  by (auto simp: conjugation_def)

lemma conjugate_subgroup_subset:
  assumes "H \<subseteq> G"
  shows "conjugate_subgroup g H \<subseteq> G"
  using assms by (auto simp: conjugate_subgroup_def conjugation_def)

lemma conjugate_subgroup_card:
  assumes "H \<subseteq> G" "finite H"
  shows "card (conjugate_subgroup g H) = card H"
  using card_image[of "conjugation g" H] inj_on_subset[OF bij_betw_imp_inj_on[OF conjugation_bij] \<open>H\<subseteq>G\<close>]
  by (metis conjugation_def conjugate_subgroup_def conjugation_unit ext unit_closed)

text \<open>Conjugation is a homomorphism: it distributes over products and inverses.\<close>
lemma conjugation_hom:
  assumes "h1 \<in> G" "h2 \<in> G"
  shows "conjugation g h1 \<cdot> conjugation g h2 = conjugation g (h1 \<cdot> h2)"
    using assms by (simp add: conjugation_def associative invertible_left_inverse2)

lemma conjugation_inverse:
  assumes "h \<in> G"
  shows "conjugation g (inverse h) = inverse (conjugation g h)"
  using conjugation_def assms inverse_composition_commute by auto

lemma conjugate_subgroup_is_subgroup:
  assumes sub: "Subgroup H G (\<cdot>) \<one>" and g: "g \<in> G"
  shows "Subgroup (conjugate_subgroup g H) G (\<cdot>) \<one>"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> using sub .
  show ?thesis
  proof (rule subgroupI)
    show "conjugate_subgroup g H \<subseteq> G"
      by (simp add: H.subset conjugate_subgroup_subset g)
  next
    have "conjugation g \<one> = \<one>" using g by (simp add: conjugation_def)
    then show "\<one> \<in> conjugate_subgroup g H"
      using H.subset conjugate_subgroup_mem_iff g by force
  next
    fix x y assume "x \<in> conjugate_subgroup g H" "y \<in> conjugate_subgroup g H"
    then obtain hx hy where hx: "hx \<in> H" "x = conjugation g hx"
      and hy: "hy \<in> H" "y = conjugation g hy"
      unfolding conjugate_subgroup_def by auto
    have "x \<cdot> y = conjugation g (hx \<cdot> hy)"
      by (simp add: conjugation_hom hx hy)
    then show "x \<cdot> y \<in> conjugate_subgroup g H"
      using conjugate_subgroup_def hx(1) hy(1) by blast
  next
    fix x assume "x \<in> conjugate_subgroup g H"
    then obtain h where h: "h \<in> H" "x = conjugation g h"
      unfolding conjugate_subgroup_def by auto
    have hG: "h \<in> G" using h(1) H.subset by auto
    show "invertible x" using h(2) conjugation_closed[OF g hG] by auto
    show "inverse x \<in> conjugate_subgroup g H"
      using h conjugation_inverse[OF hG]
      by (metis H.sub.invertible H.submonoid_inverse_closed conjugate_subgroup_def imageI)
  qed
qed

lemma conjugate_subgroup_self:
  assumes sub: "Subgroup H G (\<cdot>) \<one>" and gH: "g \<in> H" and fin: "finite G"
  shows "conjugate_subgroup g H = H"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> using sub .
  have finH: "finite H" using fin H.subset finite_subset by auto
  have "conjugate_subgroup g H \<subseteq> H"
    using gH by (auto simp: conjugate_subgroup_def conjugation_def)
  then show "conjugate_subgroup g H = H"
    by (simp add: H.subset card_subset_eq conjugate_subgroup_card finH gH)
qed

lemma conjugate_subgroup_unit:
  assumes "H \<subseteq> G"
  shows "conjugate_subgroup \<one> H = H"
  using assms by (force simp: conjugate_subgroup_def conjugation_unit)

lemma conjugate_subgroup_compose:
  assumes "g \<in> G" "h \<in> G" "H \<subseteq> G"
  shows "conjugate_subgroup (g \<cdot> h) H = conjugate_subgroup g (conjugate_subgroup h H)"
  unfolding conjugate_subgroup_def
  using assms by (auto simp: conjugation_compose intro: imageI)


text \<open>If @{term H} normalises @{term K} (i.e.\ every element of @{term H} conjugates @{term K}
  to itself), then the set product @{term "HK = H \<times> K"} is a subgroup of @{term G}.\<close>

definition subgroup_product :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "subgroup_product H K = (\<lambda>(h,k). h \<cdot> k) ` (H \<times> K)"

lemma subgroup_product_mem_iff:
  "x \<in> subgroup_product H K \<longleftrightarrow> (\<exists>h \<in> H. \<exists>k \<in> K. x = h \<cdot> k)"
  unfolding subgroup_product_def by auto

lemma subgroup_product_subset:
  assumes "H \<subseteq> G" "K \<subseteq> G"
  shows "subgroup_product H K \<subseteq> G"
  unfolding subgroup_product_def using assms by auto

lemma 
  assumes "Subgroup K G (\<cdot>) \<one>" "H \<subseteq> G"
  shows subgroup_product_superset_left:  "H \<subseteq> subgroup_product H K" 
    and subgroup_product_superset_right: "H \<subseteq> subgroup_product K H"
proof -
  interpret K: Subgroup K G "(\<cdot>)" \<one> using assms(1) .
  show "H \<subseteq> subgroup_product H K"
    using assms(2) subgroup_product_mem_iff by force
  show "H \<subseteq> subgroup_product K H"
    by (smt (verit) K.sub_unit_closed assms(2) left_unit subgroup_product_mem_iff
        subset_eq)
qed

lemma normalizes_subgroup_product_is_subgroup:
  assumes Hsub: "Subgroup H G (\<cdot>) \<one>"
    and Ksub: "Subgroup K G (\<cdot>) \<one>"
    and norm: "\<forall>h \<in> H. conjugate_subgroup h K = K"
  shows "Subgroup (subgroup_product H K) G (\<cdot>) \<one>"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> using Hsub .
  interpret K: Subgroup K G "(\<cdot>)" \<one> using Ksub .
  have swap: "\<exists>k' \<in> K. k \<cdot> h = h \<cdot> k'" if "k \<in> K" "h \<in> H" for k h
  proof -
    have "conjugation (inverse h) k \<in> K"
      by (metis H.image_of_inverse_iff conjugate_subgroup_def image_eqI norm that)
    moreover have "conjugation (inverse h) k = inverse h \<cdot> k \<cdot> h"
      by (simp add: conjugation_def that)
    moreover have "k \<cdot> h = h \<cdot> (inverse h \<cdot> k \<cdot> h)"
      by (simp add: that flip: associative)
    ultimately show ?thesis by auto
  qed
  show ?thesis
  proof (rule subgroupI)
    show "subgroup_product H K \<subseteq> G"
      by (simp add: H.subset K.subset subgroup_product_subset)
    show "\<one> \<in> subgroup_product H K"
      using subgroup_product_mem_iff by force
  next
    fix x y
    assume xHK: "x \<in> subgroup_product H K" and yHK: "y \<in> subgroup_product H K"
    obtain h1 k1 where h1H: "h1 \<in> H" and k1K: "k1 \<in> K" and xeq: "x = h1 \<cdot> k1"
      using xHK unfolding subgroup_product_mem_iff by auto
    obtain h2 k2 where h2H: "h2 \<in> H" and k2K: "k2 \<in> K" and yeq: "y = h2 \<cdot> k2"
      using yHK unfolding subgroup_product_mem_iff by auto
    obtain k' where k'K: "k' \<in> K" and k'eq: "k1 \<cdot> h2 = h2 \<cdot> k'"
      using swap[OF k1K h2H] by auto
    have "x \<cdot> y = h1 \<cdot> k1 \<cdot> (h2 \<cdot> k2)" using xeq yeq by simp
    also have "\<dots> = (h1 \<cdot> h2) \<cdot> (k' \<cdot> k2)"
      by (metis H.sub K.sub associative composition_closed h1H h2H k'K k'eq k1K k2K)
    finally have "x \<cdot> y = (h1 \<cdot> h2) \<cdot> (k' \<cdot> k2)" .
    then show "x \<cdot> y \<in> subgroup_product H K"
      using h1H h2H k'K k2K subgroup_product_mem_iff by auto
  next
    fix g assume gHK: "g \<in> subgroup_product H K"
    obtain h k where hH: "h \<in> H" and kK: "k \<in> K" and geq: "g = h \<cdot> k"
      using gHK unfolding subgroup_product_mem_iff by auto
    show "invertible g"
      by (simp add: geq hH kK)
    \<comment> \<open>@{term "inverse g = inverse k \<cdot> inverse h"}, and we swap to get @{term "inverse h \<cdot> k''"}.\<close>
    have "inverse g = inverse k \<cdot> inverse h"
      by (simp add: geq hH inverse_composition_commute kK)
    moreover have ikK: "inverse k \<in> K"
      using K.subgroup_inverse_equality[OF kK]
            K.sub.invertible_inverse_closed kK by auto
    moreover have ihH: "inverse h \<in> H"
      using H.subgroup_inverse_equality[OF hH]
            H.sub.invertible_inverse_closed hH by auto
    moreover obtain k'' where k''K: "k'' \<in> K" and k''eq: "inverse k \<cdot> inverse h = inverse h \<cdot> k''"
      using swap[OF ikK ihH] by auto
    ultimately show "inverse g \<in> subgroup_product H K"
      unfolding subgroup_product_mem_iff using ihH k''K by auto
  qed
qed


text \<open>The normalizer of a subgroup @{term H} in @{term G}: the set of elements
  that normalize @{term H} under conjugation.\<close>

definition normalizer :: "'a set \<Rightarrow> 'a set"
  where "normalizer H = {g \<in> G. conjugate_subgroup g H = H}"

lemma normalizer_subset: "normalizer H \<subseteq> G"
  unfolding normalizer_def by auto

lemma normalizer_mem_iff:
  "g \<in> normalizer H \<longleftrightarrow> g \<in> G \<and> conjugate_subgroup g H = H"
  unfolding normalizer_def by auto

lemma normalizer_subgroup:
  assumes sub: "Subgroup H G (\<cdot>) \<one>" and fin: "finite G"
  shows "Subgroup (normalizer H) G (\<cdot>) \<one>"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> using sub .
  show ?thesis
  proof (rule subgroupI)
    show "\<one> \<in> normalizer H"
      by (simp add: H.subset conjugate_subgroup_unit normalizer_mem_iff)
  next
    fix g h assume gN: "g \<in> normalizer H" and hN: "h \<in> normalizer H"
    then show "g \<cdot> h \<in> normalizer H"
      using H.subset conjugate_subgroup_compose normalizer_mem_iff by force
  next
    fix g assume gN: "g \<in> normalizer H"
    then have gG: "g \<in> G" and gH: "conjugate_subgroup g H = H"
      unfolding normalizer_mem_iff by auto
    have "conjugate_subgroup (inverse g) H = conjugate_subgroup (inverse g \<cdot> g) H"
      using H.subset conjugate_subgroup_compose gG gH invertible invertible_inverse_closed
      by presburger
    also have "\<dots> = H"
      by (simp add: conjugate_subgroup_self fin gG sub)
    finally have "conjugate_subgroup (inverse g) H = H" .
    then show "inverse g \<in> normalizer H"
      by (simp add: normalizer_mem_iff gG)
  qed (auto simp: normalizer_subset normalizer_mem_iff)
qed

lemma subgroup_subset_normalizer:
  assumes sub: "Subgroup H G (\<cdot>) \<one>" and "finite G"
  shows "H \<subseteq> normalizer H"
proof
  fix h assume hH: "h \<in> H"
  interpret H: Subgroup H G "(\<cdot>)" \<one> using sub .
  show "h \<in> normalizer H"
    by (simp add: conjugate_subgroup_self hH normalizer_mem_iff assms)
qed

lemma normal_in_normalizer:
  assumes sub: "Subgroup H G (\<cdot>) \<one>" and fin: "finite G"
  shows "normal_subgroup H (normalizer H) (\<cdot>) \<one>"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> using sub .
  interpret N: Subgroup "normalizer H" G "(\<cdot>)" \<one>
    using normalizer_subgroup[OF sub fin] .
  have sub_H_N: "Subgroup H (normalizer H) (\<cdot>) \<one>"
  proof
  qed (auto simp: subgroup_subset_normalizer[OF sub fin])
  show ?thesis
  proof (intro normal_subgroup.intro subgroup_of_group.intro)
    show "Subgroup H (normalizer H) (\<cdot>) \<one>" by (rule sub_H_N)
    show "Group (normalizer H) (\<cdot>) \<one>" using N.sub.Group_axioms .
    show "normal_subgroup_axioms H (normalizer H) (\<cdot>) \<one>"
    proof 
      fix g k assume gN: "g \<in> normalizer H" and kH: "k \<in> H"
      have igH: "conjugate_subgroup (inverse g) H = H"
        using normalizer_subgroup[OF sub fin] gN normalizer_mem_iff by blast
      have "conjugation (inverse g) k \<in> conjugate_subgroup (inverse g) H"
        unfolding conjugate_subgroup_def using kH by auto
      then show "N.sub.inverse g \<cdot> k \<cdot> g \<in> H"
        using conjugation_def gN igH kH H.subset by fastforce
    qed
  qed
qed


text \<open>The order formula for a product whose factors normalize one another in the
  relevant direction.  The second isomorphism theorem supplies the quotient
  cardinalities, so this bridge remains entirely within the native set-based API.\<close>

lemma normalizes_subgroup_product_card:
  assumes Hsub: "Subgroup H G (\<cdot>) \<one>"
    and Ksub: "Subgroup K G (\<cdot>) \<one>"
    and norm: "\<forall>h \<in> H. conjugate_subgroup h K = K"
    and fin: "finite G"
  shows "card (subgroup_product H K) * card (H \<inter> K) = card H * card K"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> using Hsub .
  interpret K: Subgroup K G "(\<cdot>)" \<one> using Ksub .
  have product_sub: "Subgroup (subgroup_product H K) G (\<cdot>) \<one>"
    by (rule normalizes_subgroup_product_is_subgroup[OF Hsub Ksub norm])
  interpret product: Subgroup "subgroup_product H K" G "(\<cdot>)" \<one>
    using product_sub .
  interpret N: Subgroup "normalizer K" G "(\<cdot>)" \<one>
    by (rule normalizer_subgroup[OF Ksub fin])
  have product_subset_N: "subgroup_product H K \<subseteq> normalizer K"
  proof
    fix x
    assume x: "x \<in> subgroup_product H K"
    obtain h k where hH: "h \<in> H" and kK: "k \<in> K" and xeq: "x = h \<cdot> k"
      using x unfolding subgroup_product_mem_iff by auto
    have hN: "h \<in> normalizer K"
      unfolding normalizer_mem_iff
      using H.subset hH norm hH by blast
    have kN: "k \<in> normalizer K"
      using subgroup_subset_normalizer[OF Ksub fin] kK by blast
    show "x \<in> normalizer K"
      using xeq N.sub_composition_closed hN kN by simp
  qed
  have product_N_sub: "Subgroup (subgroup_product H K) (normalizer K) (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF product.Subgroup_axioms N.Subgroup_axioms])
    show "subgroup_product H K \<subseteq> normalizer K" by (rule product_subset_N)
  qed
  have product_N_group: "subgroup_of_group (subgroup_product H K) (normalizer K)
      (\<cdot>) \<one>"
    by (rule subgroup_of_groupI[OF product_N_sub N.sub.Group_axioms])
  have K_normal_N: "normal_subgroup K (normalizer K) (\<cdot>) \<one>"
    by (rule normal_in_normalizer[OF Ksub fin])
  interpret KN: normal_subgroup K "normalizer K" "(\<cdot>)" \<one>
    using K_normal_N .
  have K_product: "K \<subseteq> subgroup_product H K"
    by (rule subgroup_product_superset_right[OF Hsub K.subset])
  have K_product_sub: "Subgroup K (subgroup_product H K) (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF K.Subgroup_axioms product.Subgroup_axioms])
    show "K \<subseteq> subgroup_product H K" by (rule K_product)
  qed
  have K_normal_product: "normal_subgroup K (subgroup_product H K) (\<cdot>) \<one>"
  proof (intro normal_subgroup.intro subgroup_of_group.intro)
    show "Subgroup K (subgroup_product H K) (\<cdot>) \<one>" by (rule K_product_sub)
    show "Group (subgroup_product H K) (\<cdot>) \<one>" using product.sub.Group_axioms .
    show "normal_subgroup_axioms K (subgroup_product H K) (\<cdot>) \<one>"
    proof
      fix g k
      assume gP: "g \<in> subgroup_product H K" and kK: "k \<in> K"
      have gN: "g \<in> normalizer K"
        using product_subset_N[THEN subsetD, OF gP] .
      have conjugate: "N.sub.inverse g \<cdot> k \<cdot> g \<in> K"
        using KN.normal[OF gN kK] .
      have inverse_eq: "product.sub.inverse g = N.sub.inverse g"
        using product.subgroup_inverse_equality[OF gP]
          N.subgroup_inverse_equality[OF gN] by simp
      show "product.sub.inverse g \<cdot> k \<cdot> g \<in> K"
        using conjugate by (simp only: inverse_eq)
    qed
  qed
  have H_product_sub: "Subgroup H (subgroup_product H K) (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF H.Subgroup_axioms product.Subgroup_axioms])
    show "H \<subseteq> subgroup_product H K"
      by (rule subgroup_product_superset_left[OF Ksub H.subset])
  qed
  have HIntK_product_sub:
      "Subgroup (H \<inter> K) (subgroup_product H K) (\<cdot>) \<one>"
    by (rule product.sub.subgroup_intersection[OF H_product_sub K_product_sub])
  have HIntK_H_sub: "Subgroup (H \<inter> K) H (\<cdot>) \<one>"
  proof (rule subgroup_restrict[OF HIntK_product_sub H_product_sub])
    show "H \<inter> K \<subseteq> H" by blast
  qed
  interpret KP: normal_subgroup K "subgroup_product H K" "(\<cdot>)" \<one>
    using K_normal_product .
  have HIntK_normal: "normal_subgroup (H \<inter> K) H (\<cdot>) \<one>"
  proof (intro normal_subgroup.intro subgroup_of_group.intro)
    show "Subgroup (H \<inter> K) H (\<cdot>) \<one>" by (rule HIntK_H_sub)
    show "Group H (\<cdot>) \<one>" using H.sub.Group_axioms .
    show "normal_subgroup_axioms (H \<inter> K) H (\<cdot>) \<one>"
    proof
      fix h k
      assume hH: "h \<in> H" and kI: "k \<in> H \<inter> K"
      have hP: "h \<in> subgroup_product H K"
        using subgroup_product_superset_left[OF Ksub H.subset] hH by blast
      have kH: "k \<in> H" and kK: "k \<in> K" using kI by auto
      have in_H: "H.sub.inverse h \<cdot> k \<cdot> h \<in> H"
        using H.sub_composition_closed H.submonoid_inverse_closed hH kH by auto
      have in_K: "product.sub.inverse h \<cdot> k \<cdot> h \<in> K"
        using KP.normal[OF hP kK] .
      have inverse_eq: "H.sub.inverse h = product.sub.inverse h"
        using H.subgroup_inverse_equality[OF hH]
          product.subgroup_inverse_equality[OF hP] by simp
      show "H.sub.inverse h \<cdot> k \<cdot> h \<in> H \<inter> K"
      proof
        show "H.sub.inverse h \<cdot> k \<cdot> h \<in> H" by (rule in_H)
        show "H.sub.inverse h \<cdot> k \<cdot> h \<in> K"
          using in_K by (simp only: inverse_eq)
      qed
    qed
  qed
  interpret HIntK: normal_subgroup "H \<inter> K" H "(\<cdot>)" \<one>
    using HIntK_normal .
  have H_product_group: "subgroup_of_group H (subgroup_product H K) (\<cdot>) \<one>"
    by (rule subgroup_of_groupI[OF H_product_sub product.sub.Group_axioms])
  have product_locale:
      "normal_subgroup_product K H (subgroup_product H K) (\<cdot>) \<one>"
    by (rule normal_subgroup_product.intro[OF K_normal_product H_product_group])
  interpret iso: second_iso_theorem K H "subgroup_product H K" "(\<cdot>)" \<one>
    by (rule second_iso_theorem.intro[OF product_locale])
  have iso_product: "iso.HK = subgroup_product H K"
    by (simp add: iso.HK_def subgroup_product_def)
  have fract_left: "iso.Fract_HK_K = KP.Partition"
    unfolding iso.Fract_HK_K_def iso_product KP.Partition_def by rule
  have fract_right: "iso.Fract_H_HIntK = HIntK.Partition"
    unfolding iso.Fract_H_HIntK_def HIntK.Partition_def by rule
  have finH: "finite H" using finite_subset[OF H.subset fin] .
  have fin_product: "finite (subgroup_product H K)"
    using finite_subset[OF subgroup_product_subset[OF H.subset K.subset] fin] .
  have card_left: "card iso.Fract_HK_K = KP.index"
    using KP.card_Factor_Group[OF fin_product] fract_left by simp
  have card_right: "card iso.Fract_H_HIntK = HIntK.index"
    using HIntK.card_Factor_Group[OF finH] fract_right by simp
  have iso_card: "card iso.Fract_HK_K = card iso.Fract_H_HIntK"
  proof -
    obtain f composition unit composition' unit' where f:
      "group_isomorphism f iso.Fract_HK_K composition unit
        iso.Fract_H_HIntK composition' unit'"
      using iso.second_isomorphism unfolding isomorphic_as_groups_def by auto
    interpret f: group_isomorphism f iso.Fract_HK_K composition unit
        iso.Fract_H_HIntK composition' unit' using f .
    show ?thesis using f.bijective by (rule bij_betw_same_card)
  qed
  have card_product:
      "card (subgroup_product H K) = card K * card iso.Fract_HK_K"
    using KP.lagrange[OF fin_product] card_left iso_product by simp
  have card_H: "card H = card (H \<inter> K) * card iso.Fract_H_HIntK"
    using HIntK.lagrange[OF finH] card_right fract_right by simp
  have "card (subgroup_product H K) * card (H \<inter> K) =
      (card K * card iso.Fract_HK_K) * card (H \<inter> K)"
    by (simp only: card_product)
  also have "\<dots> = card K * (card (H \<inter> K) * card iso.Fract_H_HIntK)"
    by (simp add: iso_card ac_simps)
  also have "\<dots> = card K * card H"
    by (simp only: card_H)
  also have "\<dots> = card H * card K"
    by (simp add: ac_simps)
  finally show ?thesis .
qed

text \<open>Sylow @{term p}-subgroups: subgroups whose order is the largest power of @{term p}
  dividing @{term "card G"}.\<close>

definition Sylow_subgroups :: "nat \<Rightarrow> 'a set set"
  where "Sylow_subgroups p =
    {H. Subgroup H G (\<cdot>) \<one> \<and> card H = p ^ multiplicity p (card G)}"

text \<open>Sylow @{term p}-subgroups exist by the first Sylow theorem.\<close>

lemma Sylow_subgroups_nonempty:
  assumes "prime p" "finite G"
  shows "Sylow_subgroups p \<noteq> {}"
  using Sylow_I[OF assms] multiplicity_dvd by (auto simp: Sylow_subgroups_def)

text \<open>Conjugation preserves Sylow @{term p}-subgroups.\<close>

lemma conjugate_Sylow_is_Sylow:
  assumes "P \<in> Sylow_subgroups p" "g \<in> G" "finite G"
  shows "conjugate_subgroup g P \<in> Sylow_subgroups p"
proof -
  interpret Subgroup P G "(\<cdot>)" \<one>
    using Sylow_subgroups_def assms by blast
  show ?thesis
    using assms conjugate_subgroup_card
    by (simp add: Sylow_subgroups_def conjugate_subgroup_is_subgroup finite_subset subset)
qed


text \<open>The conjugation action on subsets of @{term G}: each @{term "g \<in> G"} maps a subset
  @{term H} to @{term "conjugation g ` H"}.  We restrict to @{term "Sylow_subgroups p"}
  to obtain a group action.\<close>

definition \<phi>_Sylow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "\<phi>_Sylow p g = restrict (conjugate_subgroup g) (Sylow_subgroups p)"

lemma Sylow_subgroups_subgroup:
  "P \<in> Sylow_subgroups p \<Longrightarrow> Subgroup P G (\<cdot>) \<one>"
  unfolding Sylow_subgroups_def by auto

lemma Sylow_subgroups_subset:
  "P \<in> Sylow_subgroups p \<Longrightarrow> P \<subseteq> G"
  unfolding Sylow_subgroups_def using Submonoid.subset Subgroup_def by fastforce

lemma Sylow_subgroups_card:
  "P \<in> Sylow_subgroups p \<Longrightarrow> card P = p ^ multiplicity p (card G)"
  unfolding Sylow_subgroups_def by auto

lemma \<phi>_Sylow_mapsto:
  assumes "g \<in> G" "prime p" "finite G"
  shows "\<phi>_Sylow p g \<in> Sylow_subgroups p \<rightarrow>\<^sub>E Sylow_subgroups p"
  unfolding \<phi>_Sylow_def PiE_def Pi_def
  using conjugate_Sylow_is_Sylow assms by auto

lemma \<phi>_Sylow_bij:
  assumes g: "g \<in> G" and p: "prime p" and fin: "finite G"
  shows "bij_betw (\<phi>_Sylow p g) (Sylow_subgroups p) (Sylow_subgroups p)"
proof (intro bij_betw_byWitness strip)
  show "\<phi>_Sylow p (inverse g) (\<phi>_Sylow p g P) = P" if P: "P \<in> Sylow_subgroups p" for P
  proof -
    have Psub: "P \<subseteq> G" using Sylow_subgroups_subset[OF P] .
    have gP: "conjugate_subgroup g P \<in> Sylow_subgroups p"
      using conjugate_Sylow_is_Sylow[OF P g fin] .
    show "\<phi>_Sylow p (inverse g) (\<phi>_Sylow p g P) = P"
      unfolding \<phi>_Sylow_def using P gP
      by (metis conjugate_subgroup_unit Psub conjugate_subgroup_compose g
          invertible invertible_inverse_closed invertible_left_inverse restrict_apply)
  qed
  show "\<phi>_Sylow p g (\<phi>_Sylow p (inverse g) Q) = Q" if Q: "Q \<in> Sylow_subgroups p" for Q
  proof -
    have igQ: "conjugate_subgroup (inverse g) Q \<in> Sylow_subgroups p"
      using conjugate_Sylow_is_Sylow[OF Q _ fin] g by auto
    show "\<phi>_Sylow p g (\<phi>_Sylow p (inverse g) Q) = Q"
      unfolding \<phi>_Sylow_def using Q igQ Sylow_subgroups_subset[OF Q]
      by (metis conjugate_subgroup_unit conjugate_subgroup_compose g
          invertible invertible_inverse_closed invertible_right_inverse restrict_apply)
  qed
qed (use \<phi>_Sylow_mapsto[OF _ p fin] g in \<open>auto simp: PiE_def Pi_def\<close>)

lemma \<phi>_Sylow_unit:
  assumes "prime p" "finite G"
  shows "\<phi>_Sylow p \<one> = identity (Sylow_subgroups p)"
  using Sylow_subgroups_subset \<phi>_Sylow_def conjugate_subgroup_unit by fastforce

lemma \<phi>_Sylow_compose:
  assumes g: "g \<in> G" "h \<in> G" "prime p" "finite G"
  shows "\<phi>_Sylow p (g \<cdot> h) = compose (Sylow_subgroups p) (\<phi>_Sylow p g) (\<phi>_Sylow p h)"
  unfolding \<phi>_Sylow_def compose_def
  by (force simp: Sylow_subgroups_subset conjugate_Sylow_is_Sylow conjugate_subgroup_compose assms)

lemma \<phi>_Sylow_action:
  assumes "prime p" "finite G"
  shows "Group_Action G (\<cdot>) \<one> (\<phi>_Sylow p) (Sylow_subgroups p)"
proof 
  fix g assume "g \<in> G"
  then show "\<phi>_Sylow p g \<in> Monoid.Units (Sylow_subgroups p \<rightarrow>\<^sub>E Sylow_subgroups p)
              (compose (Sylow_subgroups p)) (identity (Sylow_subgroups p))"
    using \<phi>_Sylow_mapsto \<phi>_Sylow_bij assms
    by (intro transformations.Units_bij_betwD) auto
qed (use \<phi>_Sylow_unit \<phi>_Sylow_compose assms in auto)

lemma prime_power_dvd_not_prime_dvd:
  fixes p d :: nat and k :: nat
  assumes "prime p" "d dvd p ^ k" "\<not> p dvd d"
  shows "d = 1"
  by (metis assms dvd_trans prime_dvd_power prime_factor_nat primes_dvd_imp_eq)

text \<open>The second Sylow theorem: any two Sylow @{term p}-subgroups of @{term G} are conjugate.
  That is, the conjugation action of @{term G} on @{term "Sylow_subgroups p"} is transitive.\<close>

theorem Sylow_II:
  assumes "prime p" "finite G"
    and "P \<in> Sylow_subgroups p" "Q \<in> Sylow_subgroups p"
  shows "\<exists>g \<in> G. conjugate_subgroup g P = Q"
proof -
  interpret act: Group_Action G "(\<cdot>)" \<one> "\<phi>_Sylow p" "Sylow_subgroups p"
    using \<phi>_Sylow_action[OF assms(1,2)] .
  text \<open>Let @{term P} act on @{term "Sylow_subgroups p"} by conjugation.
    Consider the orbits of this restricted action.  The key combinatorial
    argument shows that @{term Q} must lie in the orbit of @{term P}.\<close>
  have P_self_orbit: "\<forall>g \<in> P. conjugate_subgroup g P = P"
    using conjugate_subgroup_self[OF Sylow_subgroups_subgroup[OF assms(3)] _ assms(2)] by auto
  text \<open>Transitivity of the conjugation action via the left-coset counting
    argument.  @{term P} acts on the left cosets of @{term Q} by left multiplication.
    Since the number of cosets is coprime to @{term p}, there must be a fixed coset,
    which yields the conjugating element.\<close>
  interpret Psub: Subgroup P G "(\<cdot>)" \<one>
    using Sylow_subgroups_subgroup[OF assms(3)] .
  interpret Qsub: Subgroup Q G "(\<cdot>)" \<one>
    using Sylow_subgroups_subgroup[OF assms(4)] .
  interpret QG: subgroup_of_group Q G "(\<cdot>)" \<one>
    by (simp add: Qsub.Subgroup_axioms Group_axioms subgroup_of_group_def)
  show "\<exists>g \<in> G. conjugate_subgroup g P = Q"
  proof -
    have finP: "finite P" using assms(2) Psub.subset finite_subset by auto
    have finQ: "finite Q" using assms(2) Qsub.subset finite_subset by auto
    define k where "k = multiplicity p (card G)"
    have cardP': "card P = p ^ k" and cardQ': "card Q = p ^ k"
      using Sylow_subgroups_card assms k_def by blast+
    have p_pos: "p > 0"
      by (simp add: assms(1) prime_gt_0_nat)
    have cardG_pos: "card G > 0"
      using Psub.subset assms(2) card_0_eq by blast
    \<comment> \<open>The index @{text "[G:Q]"} is not divisible by @{term p}.\<close>
    have lagrange_Q: "card G = card Q * QG.index"
      using QG.lagrange[OF assms(2)] .
    have index_pos: "QG.index > 0"
      using cardG_pos lagrange_Q by (cases "QG.index") auto
    have index_eq: "QG.index = card G div (p ^ k)"
      by (simp add: cardQ' lagrange_Q p_pos)
    have not_p_dvd_index: "\<not> p dvd QG.index"
      using multiplicity_decompose[of concl:p]
      using assms(1) cardG_pos index_eq k_def not_prime_unit by auto
    \<comment> \<open>@{term P} acts on the left cosets @{text "G/Q"} by left multiplication.
      A coset @{text "gQ"} is fixed by @{term P} iff @{text "P \<subseteq> gQg⁻¹"}.
      Since @{text "[G:Q]"} is not divisible by @{term p} and every orbit of
      the @{term P}-action has size dividing @{text "p^k"}, there is a fixed coset.\<close>
    define L where "L = (\<lambda>g. g \<cdot>| Q) ` G"
    have finL: "finite L"
      using L_def assms(2) by blast
    \<comment> \<open>The left cosets of @{term Q} have cardinality @{text "[G:Q]"}.\<close>
    have L_sub_Omega: "L \<subseteq> \<Omega> (p ^ k)"
      by (auto simp: L_def Qsub.subset \<Omega>_memI \<phi>_left_closed act.Left_Coset_def cardQ')
    show "\<exists>g\<in>G. conjugate_subgroup g P = Q"
    proof -
      \<comment> \<open>Set up the action of @{term P} on @{term "\<Omega> (p ^ k)"} by left multiplication.\<close>
      interpret P_act: Group_Action P "(\<cdot>)" \<one> "\<phi>_left (p ^ k)" "\<Omega> (p ^ k)"
      proof 
        fix g assume gP: "g \<in> P"
        then show "\<phi>_left (p ^ k) g 
                 \<in> Monoid.Units (\<Omega> (p ^ k) \<rightarrow>\<^sub>E \<Omega> (p ^ k)) (compose (\<Omega> (p ^ k))) (identity (\<Omega> (p ^ k)))"
          by (simp add: \<phi>_left_bij \<phi>_left_mapsto transformations.Units_bijective)
      qed (auto simp add: \<phi>_left_unit \<phi>_left_compose)
      \<comment> \<open>@{term Q} is an element of @{term "\<Omega> (p ^ k)"}.\<close>
      have Q_in_Omega: "Q \<in> \<Omega> (p ^ k)"
        using Qsub.subset cardQ' by auto
      \<comment> \<open>The stabilizer of @{term Q} under the @{term P}-action is @{term "P \<inter> Q"}.\<close>
      have stab_Q: "P_act.stabilizer Q = P \<inter> Q"
      proof (rule set_eqI)
        fix a
        show "a \<in> P_act.stabilizer Q \<longleftrightarrow> a \<in> P \<inter> Q"
        proof
          assume "a \<in> P_act.stabilizer Q"
          then have aP: "a \<in> P" and eq: "\<phi>_left (p ^ k) a Q = Q"
            unfolding P_act.stabilizer_def by auto
          have "(\<cdot>) a ` Q = Q" using Q_in_Omega eq by simp
          with aP show "a \<in> P \<inter> Q"
            by (metis IntI Psub.sub.right_unit Qsub.sub_unit_closed image_eqI)
        next
          assume a: "a \<in> P \<inter> Q"
          then have "(\<cdot>) a ` Q = Q"
            by (simp add: Qsub.sub.left_mult_image_card Qsub.sub.left_mult_image_subset 
                card_subset_eq finQ)
          then show "a \<in> P_act.stabilizer Q"
            unfolding P_act.stabilizer_def using a by (simp add: Q_in_Omega)
        qed
      qed
      \<comment> \<open>By orbit-stabilizer, the orbit size divides @{text "p ^ k"}.\<close>
      have orbit_dvd: "card (P_act.orbit Q) dvd p ^ k"
        by (metis P_act.orbit_stabilizer_card Q_in_Omega cardP' dvd_triv_left finP)
      \<comment> \<open>The orbit of @{term Q} under @{term P} is contained in @{term L}.\<close>
      have orbit_sub_L: "P_act.orbit Q \<subseteq> L"
        using P_act.orbit_mem_iff Q_in_Omega by (auto simp: L_def coset_notation.Left_Coset_def)
      \<comment> \<open>@{term L} has cardinality @{text "[G:Q]"}, not divisible by @{term p}.\<close>
      have card_L: "card L = QG.index"
      proof -
        have union_L: "\<Union>L = G"
        proof
          show "\<Union>L \<subseteq> G"
            unfolding L_def coset_notation.Left_Coset_def using Qsub.subset by auto
          have "\<And>x. x \<in> G \<Longrightarrow> \<exists>g\<in>G. x \<in> g \<cdot>| Q"
            by (metis Qsub.sub_unit_closed act.Left_Coset_memI right_unit)
          then show "G \<subseteq> \<Union>L"
            by (auto simp: L_def)
        qed
        have disj_L: "C1 \<inter> C2 = {}"
          if C1L: "C1 \<in> L" and C2L: "C2 \<in> L" and neq: "C1 \<noteq> C2" for C1 C2
        proof -
          obtain g1 g2 where g1G: "g1 \<in> G" and C1eq: "C1 = g1 \<cdot>| Q"
            and g2G: "g2 \<in> G" and C2eq: "C2 = g2 \<cdot>| Q"
            using C1L C2L unfolding L_def by auto
          show "C1 \<inter> C2 = {}"
          proof (rule ccontr)
            assume "C1 \<inter> C2 \<noteq> {}"
            then obtain x where xC1: "x \<in> C1" and xC2: "x \<in> C2" by auto
            obtain q1 q2 where q1Q: "q1 \<in> Q" and xeq1: "x = g1 \<cdot> q1"
              and q2Q: "q2 \<in> Q" and xeq2: "x = g2 \<cdot> q2"
              and eq12: "g1 \<cdot> q1 = g2 \<cdot> q2"
              using C1eq C2eq xC1 xC2 by fastforce
            have q1G: "q1 \<in> G" and q2G: "q2 \<in> G" using q1Q q2Q Qsub.subset by auto
            \<comment> \<open>Show @{text "C1 = C2"} by showing every element of one is in the other.\<close>
            have "C1 = C2"
            proof (rule set_eqI)
              fix y
              show "y \<in> C1 \<longleftrightarrow> y \<in> C2"
              proof
                assume "y \<in> C1"
                then obtain r where rQ: "r \<in> Q" and yeq: "y = g1 \<cdot> r"
                  unfolding C1eq coset_notation.Left_Coset_def by auto
                have rG: "r \<in> G" using rQ Qsub.subset by auto
                have iq1Q: "inverse q1 \<in> Q"
                  using q1Q by (intro Qsub.submonoid_inverse_closed) auto
                have "q2 \<cdot> inverse q1 \<cdot> r \<in> Q"
                  using q2Q iq1Q rQ by (intro Qsub.sub_composition_closed) auto
                moreover have "y = g2 \<cdot> (q2 \<cdot> inverse q1 \<cdot> r)"
                proof -
                  have "g2 \<cdot> (q2 \<cdot> inverse q1 \<cdot> r) = g2 \<cdot> q2 \<cdot> inverse q1 \<cdot> r"
                    using g2G q2G q1G rG by (simp add: associative)
                  also have "\<dots> = g1 \<cdot> r"
                    by (metis eq12 g1G q1G Qsub.sub associative commute_iff_inverse iq1Q left_unit right_unit
                        unit_closed)
                  finally show ?thesis using yeq by simp
                qed
                ultimately show "y \<in> C2"
                  unfolding C2eq coset_notation.Left_Coset_def by auto
              next
                assume "y \<in> C2"
                then obtain r where rQ: "r \<in> Q" and yeq: "y = g2 \<cdot> r"
                  unfolding C2eq coset_notation.Left_Coset_def by auto
                have rG: "r \<in> G" using rQ Qsub.subset by auto
                have iq2Q: "inverse q2 \<in> Q"
                  using q2Q by (intro Qsub.submonoid_inverse_closed) auto
                have "q1 \<cdot> inverse q2 \<cdot> r \<in> Q"
                  using q1Q iq2Q rQ by (intro Qsub.sub_composition_closed) auto
                moreover have "y = g1 \<cdot> (q1 \<cdot> inverse q2 \<cdot> r)"
                proof -
                  have "g1 \<cdot> (q1 \<cdot> inverse q2 \<cdot> r) = g1 \<cdot> q1 \<cdot> inverse q2 \<cdot> r"
                    using g1G q1G q2G rG by (simp add: associative)
                  also have "\<dots> = g2 \<cdot> r"
                    using eq12 g2G q2G rG by (simp add: associative invertible_right_inverse)
                  finally show ?thesis using yeq by simp
                qed
                ultimately show "y \<in> C1"
                  unfolding C1eq coset_notation.Left_Coset_def by auto
              qed
            qed
            with neq show False by contradiction
          qed
        qed
        have card_coset: "\<And>C. C \<in> L \<Longrightarrow> card C = card Q"
          using L_sub_Omega cardQ' by auto
        have "card G = (\<Sum>C\<in>L. card C)"
          unfolding union_L [symmetric]
        proof (intro card_Union_disjoint)
          show "disjoint L" using disj_L unfolding disjoint_def by auto
          show "\<And>A. A \<in> L \<Longrightarrow> finite A"
            using union_L \<open>finite G\<close> by (meson Union_upper finite_subset)
        qed
        also have "\<dots> = (\<Sum>C\<in>L. card Q)"
          by (rule sum.cong) (auto simp: card_coset)
        finally have "card G = card Q * card L" by simp
        with lagrange_Q show ?thesis
          using cardG_pos by auto
      qed
      \<comment> \<open>Every orbit of @{term P} on @{term L} has size a power of @{term p},
        and @{text "[G:Q]"} is not divisible by @{term p}.
        So there is a fixed coset @{text "gQ"}.\<close>
      have "\<exists>C \<in> L. \<forall>a \<in> P. (\<cdot>) a ` C = C"
      proof (rule ccontr)
        assume nofix: "\<not> (\<exists>C\<in>L. \<forall>a\<in>P. (\<cdot>) a ` C = C)"
        \<comment> \<open>The P-orbit of a coset in L stays inside L.\<close>
        have orbit_in_L: "P_act.orbit C \<subseteq> L" if "C \<in> L" for C
        proof
          fix D assume "D \<in> P_act.orbit C"
          then obtain a where aP: "a \<in> P" and aG: "a \<in> G" and Deq: "\<phi>_left (p ^ k) a C = D"
            by (auto simp: P_act.orbit_def)
          from that obtain g where gG: "g \<in> G" and Ceq: "C = g \<cdot>| Q" unfolding L_def by auto
          have "D = (\<cdot>) a ` C" using Deq that L_sub_Omega by auto
          also have "\<dots> = (a \<cdot> g) \<cdot>| Q"
            unfolding coset_notation.Left_Coset_def using aG gG Qsub.subset by (auto simp: Ceq associative)
          finally show "D \<in> L" unfolding L_def using aG gG by auto
        qed
        \<comment> \<open>By orbit-stabilizer, each \<open>P\<close>-orbit size divides \<open>card P = p ^ k\<close>.\<close>
        have orbit_dvd_gen: "card (P_act.orbit C) dvd p ^ k" if "C \<in> L" for C
          unfolding dvd_def
          using L_sub_Omega P_act.orbit_stabilizer_card cardP' finP that by auto
        \<comment> \<open>A singleton orbit means the coset is fixed by all of P.\<close>
        have orbit_singleton_fixed: "\<forall>a\<in>P. (\<cdot>) a ` C = C"
          if "C \<in> L" "P_act.orbit C = {C}" for C
        proof
          fix a assume aP: "a \<in> P"
          have COmega: "C \<in> \<Omega> (p ^ k)" using that(1) L_sub_Omega by auto
          then show "(\<cdot>) a ` C = C" 
            by (metis P_act.orbit_memI \<phi>_left_apply aP emptyE insert_iff that(2))
        qed
        \<comment> \<open>A nontrivial divisor of \<open>p ^ k\<close> is divisible by \<open>p\<close>.\<close>
        have div_ppow: "p dvd d" if "d dvd p ^ k" "d > 1" for d :: nat
          using assms(1) prime_power_dvd_not_prime_dvd that by blast
        \<comment> \<open>Assuming no fixed coset, every P-orbit on L has size divisible by p.\<close>
        have orbit_p_dvd: "p dvd card (P_act.orbit C)" if CL: "C \<in> L" for C
        proof -
          have "C \<in> P_act.orbit C" 
            using L_sub_Omega P_act.orbit_self that by blast
          moreover have "P_act.orbit C \<noteq> {C}"
            by (metis nofix orbit_singleton_fixed that)
          ultimately have "card (P_act.orbit C) \<noteq> 1" using card_1_singletonE by force
          then show ?thesis using div_ppow
            using assms(1) orbit_dvd_gen prime_power_dvd_not_prime_dvd that by blast
        qed
        \<comment> \<open>The P-orbits partition L, so p divides card L = [G:Q].\<close>
        define Lorbs where "Lorbs = P_act.orbit ` L"
        have cover: "\<Union> Lorbs = L"
          using L_sub_Omega P_act.orbit_self orbit_in_L by (auto simp: Lorbs_def)
        have disj: "disjoint Lorbs"
          using P_act.orbit_disjoint L_sub_Omega 
          by (intro disjointI) (auto simp: Lorbs_def)
        have "\<And>A. A \<in> Lorbs \<Longrightarrow> finite A"
          using cover finL by (metis Union_upper rev_finite_subset)
        then have cardL_sum: "card L = (\<Sum>X\<in>Lorbs. card X)" 
          using disj card_Union_disjoint cover by blast
        have "p dvd (\<Sum>X\<in>Lorbs. card X)"
          using orbit_p_dvd by (intro dvd_sum) (auto simp: Lorbs_def)
        with cardL_sum not_p_dvd_index show False
          by (simp add: card_L)
      qed
      then obtain g where gG: "g \<in> G" and fixed: "\<forall>a \<in> P. (\<cdot>) a ` (g \<cdot>| Q) = g \<cdot>| Q"
        using L_def by blast
      \<comment> \<open>A fixed coset @{text "gQ"} yields @{text "g⁻¹Pg \<subseteq> Q"}.\<close>
      have conj_sub: "conjugate_subgroup (inverse g) P \<subseteq> Q"
      proof
        fix x assume xconj: "x \<in> conjugate_subgroup (inverse g) P"
        then obtain a where aP: "a \<in> P" and xeq: "x = conjugation (inverse g) a"
          unfolding conjugate_subgroup_def by auto
        \<comment> \<open>Since @{term "a \<in> P"}, left multiplication by @{term a} fixes @{term "g \<cdot>| Q"}.\<close>
        then have "a \<cdot> (g \<cdot> \<one>) \<in> g \<cdot>| Q"
          by (metis Qsub.sub_unit_closed coset_notation.Left_Coset_def fixed imageI)
        then show "x \<in> Q"
          using gG aP associative conjugation_def gG invertible_left_inverse2 xeq by auto 
      qed
      \<comment> \<open>By equal cardinality, we get equality.\<close>
      have "conjugate_subgroup (inverse g) P = Q"
        by (simp add: Psub.subset cardP' cardQ' card_subset_eq conj_sub conjugate_subgroup_card finP finQ gG)
      then show "\<exists>g\<in>G. conjugate_subgroup g P = Q"
        using gG by blast
    qed
  qed
qed

text \<open>A Sylow subgroup cannot normalize a distinct Sylow subgroup.  The
  normalized product is a finite subgroup whose order is forced between the
  common Sylow order and the maximal p-power dividing @{term "card G"}.\<close>

lemma normalizes_Sylow_subgroups_eq:
  assumes prime: "prime p" and fin: "finite G"
    and P: "P \<in> Sylow_subgroups p" and Q: "Q \<in> Sylow_subgroups p"
    and norm: "\<forall>g \<in> P. conjugate_subgroup g Q = Q"
  shows "Q = P"
proof -
  interpret Psub: Subgroup P G "(\<cdot>)" \<one>
    using Sylow_subgroups_subgroup[OF P] .
  interpret Qsub: Subgroup Q G "(\<cdot>)" \<one>
    using Sylow_subgroups_subgroup[OF Q] .
  have finP: "finite P" using finite_subset[OF Psub.subset fin] .
  have finQ: "finite Q" using finite_subset[OF Qsub.subset fin] .
  define m where "m = multiplicity p (card G)"
  have cardP: "card P = p ^ m"
    using Sylow_subgroups_card[OF P] by (simp add: m_def)
  have cardQ: "card Q = p ^ m"
    using Sylow_subgroups_card[OF Q] by (simp add: m_def)
  have product_sub: "Subgroup (subgroup_product P Q) G (\<cdot>) \<one>"
    by (rule normalizes_subgroup_product_is_subgroup[OF
          Psub.Subgroup_axioms Qsub.Subgroup_axioms norm])
  interpret product: Subgroup "subgroup_product P Q" G "(\<cdot>)" \<one>
    using product_sub .
  interpret productG: subgroup_of_group "subgroup_product P Q" G "(\<cdot>)" \<one>
    by (rule subgroup_of_groupI[OF product_sub Group_axioms])
  have fin_product: "finite (subgroup_product P Q)"
    using finite_subset[OF subgroup_product_subset[OF Psub.subset Qsub.subset] fin] .
  have product_card:
      "card (subgroup_product P Q) * card (P \<inter> Q) = card P * card Q"
    by (rule normalizes_subgroup_product_card[OF
          Psub.Subgroup_axioms Qsub.Subgroup_axioms norm fin])
  have product_card_power:
      "card (subgroup_product P Q) * card (P \<inter> Q) = p ^ (m + m)"
  proof -
    have "card (subgroup_product P Q) * card (P \<inter> Q) = card P * card Q"
      by (rule product_card)
    also have "... = p ^ m * p ^ m"
      by (simp add: cardP cardQ)
    also have "... = p ^ (m + m)"
      by (rule monoid_mult_class.power_add[symmetric])
    finally show ?thesis .
  qed
  have product_dvd_power: "card (subgroup_product P Q) dvd p ^ (m + m)"
    unfolding dvd_def
    by (rule exI[where x="card (P \<inter> Q)"]) (simp add: product_card_power)
  have primepow_product:
      "\<exists>i \<le> m + m. card (subgroup_product P Q) = p ^ i"
  proof (rule iffD1[OF divides_primepow_nat[OF prime,
        of "card (subgroup_product P Q)" "m + m"]])
    show "card (subgroup_product P Q) dvd p ^ (m + m)"
      by (rule product_dvd_power)
  qed
  obtain i where i_le: "i \<le> m + m" and card_product: "card (subgroup_product P Q) = p ^ i"
    using primepow_product by blast
  have product_lagrange:
      "card G = card (subgroup_product P Q) * productG.index"
    using productG.lagrange[OF fin] .
  have product_dvd_G: "card (subgroup_product P Q) dvd card G"
    unfolding dvd_def
    by (rule exI[where x="productG.index"]) (simp add: product_lagrange)
  have p_i_dvd_G: "p ^ i dvd card G"
    using card_product product_dvd_G by simp
  have G_nonempty: "G \<noteq> {}"
    using Psub.subset Psub.sub_unit_closed by blast
  have cardG_pos: "card G > 0"
    using fin G_nonempty by (simp add: card_gt_0_iff)
  have i_le_m: "i \<le> m"
  proof -
    have cardG_ne: "card G \<noteq> 0" using cardG_pos by simp
    have mult_le:
        "multiplicity p (p ^ i) \<le> multiplicity p (card G)"
      by (rule dvd_imp_multiplicity_le[OF p_i_dvd_G cardG_ne])
    have mult_power: "multiplicity p (p ^ i) = i"
      using prime by simp
    have "i \<le> multiplicity p (card G)"
      using mult_le mult_power by simp
    then show ?thesis by (simp add: m_def)
  qed
  have P_product: "P \<subseteq> subgroup_product P Q"
    by (rule subgroup_product_superset_left[OF Qsub.Subgroup_axioms Psub.subset])
  have p_power_le: "p ^ m \<le> p ^ i"
    using card_mono[OF fin_product P_product] cardP card_product by simp
  have p_gt_one: "1 < p" by (rule prime_gt_1_nat[OF prime])
  have m_le_i: "m \<le> i"
    using p_power_le by (rule power_le_imp_le_exp[OF p_gt_one])
  have exp_eq: "i = m" using le_antisym i_le_m m_le_i .
  have product_card_eq: "card (subgroup_product P Q) = card P"
    using card_product cardP exp_eq by simp
  have P_eq_product: "P = subgroup_product P Q"
    by (rule card_subset_eq[OF fin_product P_product]) (simp add: product_card_eq)
  have Q_product: "Q \<subseteq> subgroup_product P Q"
    by (rule subgroup_product_superset_right[OF Psub.Subgroup_axioms Qsub.subset])
  have Q_subset_P: "Q \<subseteq> P"
  proof
    fix x assume xQ: "x \<in> Q"
    have x_product: "x \<in> subgroup_product P Q"
      using Q_product xQ by blast
    show "x \<in> P"
      using P_eq_product x_product by simp
  qed
  have card_Q_eq_P: "card Q = card P"
    using cardP cardQ by simp
  show ?thesis
    by (rule card_subset_eq[OF finP Q_subset_P card_Q_eq_P])
qed

text \<open>Conjugation is transitive on the Sylow @{term p}-subgroups.\<close>

lemma Sylow_subgroups_orbit:
  assumes prime: "prime p" and fin: "finite G"
    and P: "P \<in> Sylow_subgroups p"
  shows "(\<lambda>g. \<phi>_Sylow p g P) ` G = Sylow_subgroups p"
proof -
  interpret act: Group_Action G "(\<cdot>)" \<one> "\<phi>_Sylow p" "Sylow_subgroups p"
    using \<phi>_Sylow_action[OF prime fin] .
  show "(\<lambda>g. \<phi>_Sylow p g P) ` G = Sylow_subgroups p"
  proof (rule equalityI)
    show "(\<lambda>g. \<phi>_Sylow p g P) ` G \<subseteq> Sylow_subgroups p"
    proof
      fix Q assume Qimage: "Q \<in> (\<lambda>g. \<phi>_Sylow p g P) ` G"
      obtain g where gG: "g \<in> G" and Qeq: "\<phi>_Sylow p g P = Q"
        using Qimage by blast
      have "\<phi>_Sylow p g P \<in> Sylow_subgroups p"
        by (rule act.action_closed[OF gG P])
      with Qeq show "Q \<in> Sylow_subgroups p" by simp
    qed
    show "Sylow_subgroups p \<subseteq> (\<lambda>g. \<phi>_Sylow p g P) ` G"
    proof
      fix Q assume Q: "Q \<in> Sylow_subgroups p"
      have gPQ_ex: "\<exists>g \<in> G. conjugate_subgroup g P = Q"
        by (rule Sylow_II[OF prime fin P Q])
      then obtain g where gG: "g \<in> G" and gPQ: "conjugate_subgroup g P = Q"
        by blast
      have "\<phi>_Sylow p g P = Q"
        unfolding \<phi>_Sylow_def using P gPQ by simp
      then show "Q \<in> (\<lambda>g. \<phi>_Sylow p g P) ` G"
        using gG by blast
    qed
  qed
qed

text \<open>The number of Sylow @{term p}-subgroups divides the group order.\<close>

lemma Sylow_subgroups_card_dvd:
  assumes prime: "prime p" and fin: "finite G"
  shows "card (Sylow_subgroups p) dvd card G"
proof -
  have nonempty: "Sylow_subgroups p \<noteq> {}"
    by (rule Sylow_subgroups_nonempty[OF prime fin])
  then obtain P where P: "P \<in> Sylow_subgroups p"
    by blast
  interpret act: Group_Action G "(\<cdot>)" \<one> "\<phi>_Sylow p" "Sylow_subgroups p"
    using \<phi>_Sylow_action[OF prime fin] .
  have orbit_S: "act.orbit P = Sylow_subgroups p"
    using Sylow_subgroups_orbit[OF prime fin P]
    by (simp add: act.orbit_eq)
  have stab_normalizer: "act.stabilizer P = normalizer P"
    unfolding act.stabilizer_def normalizer_def \<phi>_Sylow_def
    using P by simp
  have orbit_stab:
      "card G = card (Sylow_subgroups p) * card (normalizer P)"
    using act.orbit_stabilizer_card[OF P fin] orbit_S stab_normalizer by simp
  show "card (Sylow_subgroups p) dvd card G"
    unfolding dvd_def
    by (rule exI[where x="card (normalizer P)"]) (simp add: orbit_stab)
qed

text \<open>The number of Sylow @{term p}-subgroups divides the group order and is
  congruent to one modulo @{term p}.\<close>

theorem Sylow_III:
  assumes prime: "prime p" and fin: "finite G"
  shows "card (Sylow_subgroups p) dvd card G"
    and "p dvd card (Sylow_subgroups p) - 1"
proof -
  have fin_S: "finite (Sylow_subgroups p)"
  proof -
    have sub_pow: "Sylow_subgroups p \<subseteq> Pow G"
    proof
      fix X assume X: "X \<in> Sylow_subgroups p"
      have "X \<subseteq> G" by (rule Sylow_subgroups_subset[OF X])
      then show "X \<in> Pow G" by simp
    qed
    have "finite (Pow G)" by (simp add: fin)
    then show ?thesis by (rule finite_subset[OF sub_pow])
  qed
  have nonempty: "Sylow_subgroups p \<noteq> {}"
    by (rule Sylow_subgroups_nonempty[OF prime fin])
  then obtain P where P: "P \<in> Sylow_subgroups p"
    by blast
  interpret Psub: Subgroup P G "(\<cdot>)" \<one>
    using Sylow_subgroups_subgroup[OF P] .
  have finP: "finite P" using finite_subset[OF Psub.subset fin] .
  have cardP: "card P = p ^ multiplicity p (card G)"
    using Sylow_subgroups_card[OF P] .
  interpret act: Group_Action G "(\<cdot>)" \<one> "\<phi>_Sylow p" "Sylow_subgroups p"
    using \<phi>_Sylow_action[OF prime fin] .
  have div_S: "card (Sylow_subgroups p) dvd card G"
    by (rule Sylow_subgroups_card_dvd[OF prime fin])
  have P_act_map:
      "\<phi>_Sylow p g \<in> Monoid.Units
        (Sylow_subgroups p \<rightarrow>\<^sub>E Sylow_subgroups p)
        (compose (Sylow_subgroups p)) (identity (Sylow_subgroups p))"
    if "g \<in> P" for g
  proof -
    have gG: "g \<in> G" using Psub.subset that by blast
    show ?thesis
      by (rule act.hom_closed[OF gG])
  qed
  interpret P_act: Group_Action P "(\<cdot>)" \<one> "\<phi>_Sylow p" "Sylow_subgroups p"
  proof
    fix g assume "g \<in> P"
    then show "\<phi>_Sylow p g \<in> Monoid.Units
        (Sylow_subgroups p \<rightarrow>\<^sub>E Sylow_subgroups p)
        (compose (Sylow_subgroups p)) (identity (Sylow_subgroups p))"
      by (rule P_act_map)
  next
    fix g h assume gP: "g \<in> P" and hP: "h \<in> P"
    have gG: "g \<in> G" using Psub.subset gP by blast
    have hG: "h \<in> G" using Psub.subset hP by blast
    show "\<phi>_Sylow p (g \<cdot> h) =
        compose (Sylow_subgroups p) (\<phi>_Sylow p g) (\<phi>_Sylow p h)"
      using act.hom_compose[OF gG hG] .
  next
    show "\<phi>_Sylow p \<one> = identity (Sylow_subgroups p)"
      by (rule act.hom_unit)
  qed
  have fixed_P: "P \<in> P_act.fixed_points"
  proof (rule P_act.fixed_pointI[OF P])
    fix g assume gP: "g \<in> P"
    have gG: "g \<in> G" using Psub.subset gP by blast
    have conjugate: "conjugate_subgroup g P = P"
      by (rule conjugate_subgroup_self[OF Psub.Subgroup_axioms gP fin])
    show "\<phi>_Sylow p g P = P"
      unfolding \<phi>_Sylow_def using P conjugate by simp
  qed
  have fixed_unique: "Q = P"
    if Qfixed: "Q \<in> P_act.fixed_points" for Q
  proof -
    have Qmem: "Q \<in> Sylow_subgroups p"
      using subsetD[OF P_act.fixed_points_subset Qfixed] .
    have normQ: "\<forall>g \<in> P. conjugate_subgroup g Q = Q"
    proof
      fix g assume gP: "g \<in> P"
      have fixed: "\<phi>_Sylow p g Q = Q"
        using P_act.fixed_pointD[OF Qfixed gP] .
      have gG: "g \<in> G" using Psub.subset gP by blast
      have map_eq: "(\<phi>_Sylow p g) Q = conjugate_subgroup g Q"
        unfolding \<phi>_Sylow_def using Qmem by simp
      show "conjugate_subgroup g Q = Q"
        using map_eq fixed by simp
    qed
    show ?thesis
      by (rule normalizes_Sylow_subgroups_eq[OF prime fin P Qmem normQ])
  qed
  have fixed_eq: "P_act.fixed_points = {P}"
  proof (rule equalityI)
    show "P_act.fixed_points \<subseteq> {P}"
    proof
      fix Q assume Qfixed: "Q \<in> P_act.fixed_points"
      have "Q = P" by (rule fixed_unique[OF Qfixed])
      then show "Q \<in> {P}" by simp
    qed
    show "{P} \<subseteq> P_act.fixed_points"
      by (simp add: fixed_P)
  qed
  have p_dvd_nonfixed:
      "p dvd card (Sylow_subgroups p - P_act.fixed_points)"
  proof (rule P_act.dvd_card_nonfixed_points[OF fin_S])
    fix Q
    assume Q: "Q \<in> Sylow_subgroups p" and Qnot: "Q \<notin> P_act.fixed_points"
      have orbit_ne: "P_act.orbit Q \<noteq> {Q}"
    proof
      assume orbit_eq: "P_act.orbit Q = {Q}"
      have "Q \<in> P_act.fixed_points"
        using P_act.fixed_point_iff_orbit_singleton[OF Q] orbit_eq by simp
      then show False using Qnot by contradiction
    qed
    have orbit_card_ne: "card (P_act.orbit Q) \<noteq> 1"
    proof
      assume orbit_card: "card (P_act.orbit Q) = 1"
      then obtain R where orbit_R: "P_act.orbit Q = {R}"
        by (rule card_1_singletonE)
      have Qorbit: "Q \<in> P_act.orbit Q"
        by (rule P_act.orbit_self[OF Q])
      then have "R = Q" using orbit_R by simp
      with orbit_R orbit_ne show False by simp
    qed
    have orbit_stab_Q:
        "card P = card (P_act.orbit Q) * card (P_act.stabilizer Q)"
      using P_act.orbit_stabilizer_card[OF Q finP] .
    have orbit_dvd: "card (P_act.orbit Q) dvd p ^ multiplicity p (card G)"
      unfolding dvd_def
      by (rule exI[where x="card (P_act.stabilizer Q)"])
        (metis cardP orbit_stab_Q)
    show "p dvd card (P_act.orbit Q)"
    proof (rule ccontr)
      assume "\<not> p dvd card (P_act.orbit Q)"
      then have "card (P_act.orbit Q) = 1"
        by (rule prime_power_dvd_not_prime_dvd[OF prime orbit_dvd])
      then show False using orbit_card_ne by contradiction
    qed
  qed
  have diff_card:
      "card (Sylow_subgroups p - P_act.fixed_points) =
        card (Sylow_subgroups p) - 1"
    using fixed_eq P by (simp add: card_Diff_singleton)
  show "card (Sylow_subgroups p) dvd card G" by (rule div_S)
  show "p dvd card (Sylow_subgroups p) - 1"
    using p_dvd_nonfixed diff_card by simp
qed

end

end
