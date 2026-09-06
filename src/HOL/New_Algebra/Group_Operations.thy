theory Group_Operations
  imports Group_Theory "HOL-Computational_Algebra.Primes"
begin

section \<open>Group Actions\<close>

text \<open>This theory formalises group actions with respect to the locale-based group
  infrastructure of @{text Group_Theory}, following the same development as
  @{text GroupAction.thy} (which uses the record-based groups of HOL-Algebra).

  A group action of a group $(G, \cdot, 1)$ on a set $S$ is given by a group
  homomorphism $\varphi : G \to \operatorname{Sym}(S)$, where $\operatorname{Sym}(S)$
  is the symmetric group on $S$ (i.e.\ the group of bijections $S \to S$).\<close>


subsection \<open>Definition and Basic Properties\<close>

locale Group_Action =
  grp: Group G "(\<cdot>)" \<one> + transformations S
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) and \<phi> and S +
  assumes hom_closed: "g \<in> G \<Longrightarrow> \<phi> g \<in> Sym"
    and hom_compose: "\<lbrakk> g \<in> G; h \<in> G \<rbrakk> \<Longrightarrow> \<phi> (g \<cdot> h) = compose S (\<phi> g) (\<phi> h)"
    and hom_unit: "\<phi> \<one> = identity S"

begin

sublocale coset_notation .

text \<open>The action of @{term \<one>} has no effect.\<close>

lemma one_is_id [simp]:
  assumes "s \<in> S"
  shows "\<phi> \<one> s = s"
  using assms hom_unit by simp

text \<open>The action maps @{term S} to itself.\<close>

lemma action_closed [intro, simp]:
  assumes "g \<in> G" "s \<in> S"
  shows "\<phi> g s \<in> S"
  using assms hom_closed Units_bij_betwI by (meson bij_betwE)

text \<open>The image of any group element is a bijection on @{term S}.\<close>

lemma images_are_bij:
  assumes "g \<in> G"
  shows "bij_betw (\<phi> g) S S"
  using assms hom_closed by auto

text \<open>The action respects group multiplication.\<close>

lemma action_mult:
  assumes "g \<in> G" "h \<in> G" "s \<in> S"
  shows "\<phi> g (\<phi> h s) = \<phi> (g \<cdot> h) s"
  using assms hom_compose by (simp add: compose_eq)

text \<open>The action of @{term "grp.inverse g"} reverts the action of @{term g}.\<close>

lemma group_inv_rel:
  assumes "g \<in> G" "t \<in> S" "\<phi> g t = s"
  shows "\<phi> (grp.inverse g) s = t"
  using action_mult assms by force

lemma action_inverse:
  assumes "g \<in> G" "s \<in> S"
  shows "\<phi> (grp.inverse g) (\<phi> g s) = s"
  using assms action_closed group_inv_rel by blast


subsection \<open>Stabilizer\<close>

text \<open>The stabilizer of a point @{term "s \<in> S"} is the set of group elements
  that fix @{term s} under the action.\<close>

definition stabilizer
  where "stabilizer s = {g \<in> G. \<phi> g s = s}"


text \<open>The stabilizer of any point in @{term S} is a subgroup of @{term G}.\<close>

theorem stabilizer_subgroup:
  assumes "s \<in> S"
  shows "Subgroup (stabilizer s) G (\<cdot>) \<one>"
proof (rule grp.subgroupI)
  fix g h
  assume "g \<in> stabilizer s" "h \<in> stabilizer s"
  then show "g \<cdot> h \<in> stabilizer s"
    using action_mult assms stabilizer_def by force
qed (auto simp: assms group_inv_rel stabilizer_def)

subsection \<open>Fixed Points\<close>

text \<open>The fixed points of a group action are those elements of @{term S} that
  are fixed by every group element.  Equivalently, a point is fixed if and only
  if its stabilizer is the whole group.\<close>

definition fixed_points
  where "fixed_points = {s \<in> S. G \<subseteq> stabilizer s}"

lemma fixed_points_subset: "fixed_points \<subseteq> S"
  unfolding fixed_points_def by auto

lemma fixed_point_char:
  assumes "s \<in> S"
  shows "s \<in> fixed_points \<longleftrightarrow> (\<forall>g \<in> G. \<phi> g s = s)"
  unfolding fixed_points_def stabilizer_def using assms by auto

lemma fixed_pointI:
  assumes "s \<in> S" "\<And>g. g \<in> G \<Longrightarrow> \<phi> g s = s"
  shows "s \<in> fixed_points"
  using assms fixed_point_char by auto

lemma fixed_pointD:
  assumes "s \<in> fixed_points" "g \<in> G"
  shows "\<phi> g s = s"
  using assms unfolding fixed_points_def stabilizer_def by auto

text \<open>A point is fixed if and only if its stabilizer is the whole group.\<close>

lemma fixed_point_stabilizer:
  assumes "s \<in> S"
  shows "s \<in> fixed_points \<longleftrightarrow> stabilizer s = G"
  using assms fixed_points_def stabilizer_def by auto


subsection \<open>Orbits\<close>

text \<open>The orbit of a point @{term "s \<in> S"} under the group action is the set
  of all images of @{term s} under group elements.\<close>

definition orbit
  where "orbit s \<equiv> {\<phi> g s | g. g \<in> G}"

lemma orbit_eq: "orbit s = (\<lambda>g. \<phi> g s) ` G"
  by (auto simp: orbit_def)

lemma orbit_subset:
  assumes "s \<in> S"
  shows "orbit s \<subseteq> S"
  unfolding orbit_def using assms by auto

lemma orbit_self:
  assumes "s \<in> S"
  shows "s \<in> orbit s"
  unfolding orbit_def using assms grp.unit_closed by force

lemma orbit_mem_iff:
  assumes "s \<in> S"
  shows "t \<in> orbit s \<longleftrightarrow> (\<exists>g \<in> G. \<phi> g s = t)"
  unfolding orbit_def by auto

lemma orbit_memI:
  assumes "g \<in> G"
  shows "\<phi> g s \<in> orbit s"
  unfolding orbit_def using assms by auto

lemma orbit_memE:
  assumes "t \<in> orbit s"
  obtains g where "g \<in> G" "\<phi> g s = t"
  using assms unfolding orbit_def by auto

lemma orbit_nonempty: "orbit s \<noteq> {}"
  using orbit_memI by auto

text \<open>A point is fixed precisely when its orbit is the singleton containing it.\<close>

lemma fixed_point_iff_orbit_singleton:
  assumes "s \<in> S"
  shows "s \<in> fixed_points \<longleftrightarrow> orbit s = {s}"
proof
  assume fixed: "s \<in> fixed_points"
  show "orbit s = {s}"
  proof (rule set_eqI)
    fix t
    show "t \<in> orbit s \<longleftrightarrow> t \<in> {s}"
    proof
      assume "t \<in> orbit s"
      then obtain g where "g \<in> G" "\<phi> g s = t" by (rule orbit_memE)
      then show "t \<in> {s}" using fixed fixed_pointD by simp
    next
      assume "t \<in> {s}"
      then show "t \<in> orbit s" using assms orbit_self by simp
    qed
  qed
next
  assume orbit: "orbit s = {s}"
  show "s \<in> fixed_points"
  proof (rule fixed_pointI[OF assms])
    fix g assume "g \<in> G"
    then have "\<phi> g s \<in> orbit s" by (rule orbit_memI)
    then show "\<phi> g s = s" by (simp add: orbit)
  qed
qed

lemma card_orbit_gt0I: "finite G \<Longrightarrow> card (orbit s) > 0"
  by (metis card_gt_0_iff finite_imageI orbit_eq orbit_nonempty)

subsection \<open>The Orbit-Stabilizer Theorem\<close>

text \<open>Two group elements give the same image under the action if and only if
  they lie in the same right coset of the stabilizer.\<close>

lemma same_orbit_iff_same_coset:
  assumes "s \<in> S" "g \<in> G" "h \<in> G"
  shows "\<phi> g s = \<phi> h s \<longleftrightarrow> grp.inverse g \<cdot> h \<in> stabilizer s"
proof
  assume "\<phi> g s = \<phi> h s"
  then show "grp.inverse g \<cdot> h \<in> stabilizer s"
    using assms Group_Action.action_mult Group_Action_axioms action_inverse
      by (fastforce simp: invertible_inverse_closed stabilizer_def)
next
  assume mem: "grp.inverse g \<cdot> h \<in> stabilizer s"
  then have "\<phi> g (\<phi> (grp.inverse g) (\<phi> h s)) = \<phi> g s"
    using assms by (simp add: action_mult stabilizer_def)
  then show "\<phi> g s = \<phi> h s"
    using assms by (simp add: action_mult grp.invertible_right_inverse2)
qed

text \<open>The orbit-stabilizer theorem.  The map @{term "\<lambda>g. \<phi> g s"} from
  @{term G} to @{term "orbit s"} is surjective, and its fibers are exactly
  the left cosets of the stabilizer.  Hence the number of distinct images
  equals the index of the stabilizer, and Lagrange's theorem gives the
  cardinality form.\<close>

text \<open>Every left coset of the stabilizer has the same cardinality as the
  stabilizer itself.\<close>

lemma coset_fiber:
  assumes s: "s \<in> S" and g: "g \<in> G"
  shows "{h \<in> G. \<phi> h s = \<phi> g s} = g \<cdot>| stabilizer s"
proof (rule set_eqI)
  fix h
  show "(h \<in> {h \<in> G. \<phi> h s = \<phi> g s}) = (h \<in> g \<cdot>| stabilizer s)"
  proof
    assume h: "h \<in> {h \<in> G. \<phi> h s = \<phi> g s}"
    then have hG: "h \<in> G" and eq: "\<phi> h s = \<phi> g s" by auto
    from same_orbit_iff_same_coset [OF s g hG] eq
    have "grp.inverse g \<cdot> h \<in> stabilizer s" by simp
    then show "h \<in> g \<cdot>| stabilizer s"
      by (simp add: g grp.invertible_right_inverse2 hG rev_image_eqI Left_Coset_def)
  next
    assume h: "h \<in> g \<cdot>| stabilizer s"
    then obtain t where t: "t \<in> stabilizer s" and ht: "h = g \<cdot> t"
      unfolding Left_Coset_def by auto
    from t have tG: "t \<in> G" and ts: "\<phi> t s = s"
      unfolding stabilizer_def by auto
    have hG: "h \<in> G" using ht g tG by auto
    then show "h \<in> {h \<in> G. \<phi> h s = \<phi> g s}"
      using action_mult g ht s tG ts by fastforce
  qed
qed

text \<open>The orbit-stabilizer theorem (bijection form).  The map that sends each
  orbit element to its fiber under @{term "\<lambda>g. \<phi> g s"} is a bijection from
  @{term "orbit s"} to the set of left cosets of the stabilizer.\<close>

theorem orbit_stabilizer_bij:
  assumes "s \<in> S"
  shows "bij_betw (\<lambda>t. {g \<in> G. \<phi> g s = t}) (orbit s) ((\<lambda>g. g \<cdot>| stabilizer s) ` G)"
  using coset_fiber assms
  by (auto simp: bij_betw_def inj_on_def orbit_def)

text \<open>The orbit-stabilizer theorem (cardinality form).\<close>

theorem orbit_stabilizer_card:
  assumes s: "s \<in> S" and fin: "finite G"
  shows "card G = card (orbit s) * card (stabilizer s)"
proof -
  let ?f = "\<lambda>g. \<phi> g s"
  have surj: "?f ` G = orbit s"
    unfolding orbit_def by auto
  have fibers: "\<And>g. g \<in> G \<Longrightarrow> {h \<in> G. ?f h = ?f g} = g \<cdot>| stabilizer s"
    using coset_fiber [OF s] by auto
  have fiber_card: "card {h \<in> G. ?f h = ?f g} = card (stabilizer s)"
    if g: "g \<in> G" for g
  proof -
    have \<section>: "bij_betw ((\<cdot>) g) (stabilizer s) (g \<cdot>| stabilizer s)"
      using that by (auto simp: bij_betw_def inj_on_def stabilizer_def)
    have "card {h \<in> G. ?f h = ?f g} = card (g \<cdot>| stabilizer s)"
      using fibers [OF that] by simp
    also have "\<dots> = card (stabilizer s)"
      using \<section> by (simp add: bij_betw_same_card)
    finally show ?thesis
      by presburger
  qed
  have decomp: "G = (\<Union>t \<in> orbit s. {g \<in> G. ?f g = t})"
    using surj by auto
  have disj: "\<And>t1 t2. \<lbrakk> t1 \<in> orbit s; t2 \<in> orbit s; t1 \<noteq> t2 \<rbrakk>
    \<Longrightarrow> {g \<in> G. ?f g = t1} \<inter> {g \<in> G. ?f g = t2} = {}"
    by auto
  have fin_orbit: "finite (orbit s)"
    using fin surj by (metis finite_imageI)
  have "card G = card (\<Union>t \<in> orbit s. {g \<in> G. ?f g = t})"
    using decomp by simp
  also have "\<dots> = (\<Sum>t \<in> orbit s. card {g \<in> G. ?f g = t})"
    using fin fin_orbit disj by (intro card_UN_disjoint) auto
  also have "\<dots> = (\<Sum>t \<in> orbit s. card (stabilizer s))"
    using fiber_card
    by (intro sum.cong; force simp: orbit_def)
  also have "\<dots> = card (orbit s) * card (stabilizer s)"
    by simp
  finally show ?thesis .
qed


subsection \<open>Connection to Transformation Groups\<close>

text \<open>The image @{term "\<phi> ` G"} is a subgroup of the symmetric group on @{term S},
  and therefore forms a transformation group.  This connects the orbit defined
  here with the orbit equivalence relation of @{locale transformation_group}.\<close>

lemma image_is_subgroup: "Subgroup (\<phi> ` G) Sym (compose S) (identity S)"
proof (rule symmetric.subgroupI)
  show "\<phi> ` G \<subseteq> Sym"
    using hom_closed by auto
next
  show "identity S \<in> \<phi> ` G"
    using hom_unit grp.unit_closed by (metis image_eqI)
next
  fix g h
  assume "g \<in> \<phi> ` G" "h \<in> \<phi> ` G"
  then obtain a b where "a \<in> G" "g = \<phi> a" "b \<in> G" "h = \<phi> b" by auto
  then show "compose S g h \<in> \<phi> ` G"
    using hom_compose by (metis grp.composition_closed image_eqI)
next
  fix g
  assume "g \<in> \<phi> ` G"
  then obtain a where a: "a \<in> G" "g = \<phi> a" by auto
  show "\<And>g. g \<in> \<phi> ` G \<Longrightarrow> symmetric.invertible g"
    using hom_closed by blast
  have inv_eq: "inverse (\<phi> a) = \<phi> (grp.inverse a)"
  proof (intro inverse_equality)
    show "compose S (\<phi> a) (\<phi> (grp.inverse a)) = identity S"
         "compose S (\<phi> (grp.inverse a)) (\<phi> a) = identity S"
      using \<open>a \<in> G\<close> hom_compose [symmetric] hom_unit by auto
  qed (use \<open>a \<in> G\<close> hom_closed Units_bijective in blast)+
  have "symmetric.inverse g \<in> S \<rightarrow>\<^sub>E S"
    by (metis a hom_closed mem_UnitsD symmetric.invertible symmetric.invertible_inverse_closed)
  then have "inverse (\<phi> a) = symmetric.inverse g"
    using \<open>a \<in> G\<close> \<open>g = \<phi> a\<close> hom_closed
    by (metis (no_types, lifting) inverse_equality mem_UnitsD symmetric.invertible
        symmetric.invertible_left_inverse symmetric.invertible_right_inverse)
  then show "symmetric.inverse g \<in> \<phi> ` G"
    by (metis \<open>a \<in> G\<close> grp.invertible grp.invertible_inverse_closed image_iff inv_eq)
qed

sublocale tg: transformation_group "\<phi> ` G" S
  using image_is_subgroup transformation_group_def by blast

lemma orbit_eq_Class:
  assumes "s \<in> S"
  shows "orbit s = tg.orbit.Class s"
  using assms tg.orbit_equality by (auto simp: orbit_def)


subsection \<open>The permutation representation\<close>

text \<open>
  A group action is, by definition, a homomorphism into the symmetric group on @{term S}.
  We make this explicit, identify its kernel with the set of elements acting trivially on
  every point, and deduce that a \<^emph>\<open>faithful\<close> action embeds the group as a subgroup of the
  symmetric group: the permutation representation.  This is what turns an action on a
  finite set into a concrete subgroup of permutations (e.g.\ a Galois group acting on the
  roots of a polynomial becomes a subgroup of @{term "Sym"} of the root set).
\<close>

text \<open>The action, restricted to @{term G} for extensionality, is a group homomorphism into the
  symmetric group.\<close>
interpretation action_hom:
  group_homomorphism "restrict \<phi> G" G "(\<cdot>)" \<one> Sym "compose S" "identity S"
proof 
  show "restrict \<phi> G \<in> G \<rightarrow>\<^sub>E Sym" using hom_closed by auto
next
  fix x y assume "x \<in> G" "y \<in> G"
  then show "restrict \<phi> G (x \<cdot> y) = compose S (restrict \<phi> G x) (restrict \<phi> G y)"
    by (simp add: hom_compose)
next
  show "restrict \<phi> G \<one> = identity S" by (simp add: hom_unit)
qed

text \<open>On @{term S}, the image of a group element is the identity exactly when it fixes every
  point.\<close>
lemma phi_eq_identity_iff:
  assumes "g \<in> G"
  shows "\<phi> g = identity S \<longleftrightarrow> (\<forall>s \<in> S. \<phi> g s = s)"
  using assms by auto

text \<open>The kernel of the permutation representation is the set of group elements that fix every
  point of @{term S}, i.e.\ the intersection of all the stabilizers.\<close>
lemma action_kernel_eq:
  "group_homomorphism.Ker (restrict \<phi> G) G (identity S) = {g \<in> G. \<forall>s \<in> S. \<phi> g s = s}"
proof -
  show ?thesis
    using action_hom.Ker_image by (auto simp: phi_eq_identity_iff)
qed

text \<open>An action is \<^emph>\<open>faithful\<close> if only the unit acts trivially on all of @{term S}.\<close>
definition faithful
  where "faithful \<longleftrightarrow> (\<forall>g \<in> G. (\<forall>s \<in> S. \<phi> g s = s) \<longrightarrow> g = \<one>)"

lemma faithful_iff_kernel_trivial:
  "faithful \<longleftrightarrow> group_homomorphism.Ker (restrict \<phi> G) G (identity S) = {\<one>}"
proof -
  have ker: "action_hom.Ker = {g \<in> G. \<forall>s \<in> S. \<phi> g s = s}" by (rule action_kernel_eq)
  have one_in: "\<one> \<in> action_hom.Ker" unfolding ker by simp
  show ?thesis
  proof
    assume faithful
    then have "action_hom.Ker \<subseteq> {\<one>}" unfolding ker faithful_def by blast
    with one_in show "action_hom.Ker = {\<one>}" by blast
  next
    assume "action_hom.Ker = {\<one>}"
    then show faithful unfolding faithful_def using ker by blast
  qed
qed

text \<open>A faithful action is injective.\<close>
lemma faithful_inj:
  assumes faithful
  shows "inj_on (restrict \<phi> G) G"
  using action_hom.injective_iff_kernel_unit assms faithful_iff_kernel_trivial
  by force

text \<open>The permutation representation of a faithful action is a group isomorphism onto its
  image, exhibiting @{term G} as a subgroup of the symmetric group on @{term S}.\<close>
theorem faithful_action_embeds:
  assumes faithful
  shows "group_isomorphism (restrict \<phi> G) G (\<cdot>) \<one> (\<phi> ` G) (compose S) (identity S)"
proof
  show "bij_betw (restrict \<phi> G) G (\<phi> ` G)"
    using assms bij_betw_def faithful_inj by auto
qed (auto simp: hom_closed hom_unit hom_compose)


subsection \<open>Orbit Partition\<close>

text \<open>The orbits of a group action partition @{term S}.  Using the connection to
  @{locale transformation_group}, these facts follow from the general theory of
  equivalence relations.\<close>

text \<open>If @{term t} is in the orbit of @{term s}, then @{term s} is in the orbit of @{term t}.\<close>

lemma orbit_symmetric:
  assumes "s \<in> S" "t \<in> orbit s"
  shows "s \<in> orbit t"
proof -
  from assms have "t \<in> tg.orbit.Class s"
    by (simp add: orbit_eq_Class)
  then have "(t, s) \<in> tg.Orbit_Relation"
    using assms(1) by auto
  then have "(s, t) \<in> tg.Orbit_Relation"
    by (rule tg.orbit.symmetric)
  then show "s \<in> orbit t"
    using orbit_eq_Class by blast
qed

text \<open>If @{term t} is in the orbit of @{term s}, the two orbits are equal.\<close>

lemma orbit_subset_mem:
  assumes "s \<in> S" "t \<in> orbit s"
  shows "orbit t \<subseteq> orbit s"
  using action_mult assms orbit_mem_iff by fastforce

lemma orbit_eq_mem:
  assumes "s \<in> S" "t \<in> orbit s"
  shows "orbit t = orbit s"
  by (meson antisym assms orbit_subset_mem orbit_subset orbit_symmetric subsetD)

text \<open>Two orbits are either equal or disjoint.\<close>

lemma orbit_disjoint:
  assumes "s \<in> S" "t \<in> S" "orbit s \<noteq> orbit t"
  shows "orbit s \<inter> orbit t = {}"
  by (metis Int_emptyI assms orbit_eq_mem)

text \<open>The set of all orbits.\<close>

definition orbits :: "'b set set"
  where "orbits = orbit ` S"

lemma orbits_coverI:
  assumes "s \<in> S"
  shows "orbit s \<in> orbits"
  using assms unfolding orbits_def by auto

lemma orbits_coverE:
  assumes "X \<in> orbits"
  obtains s where "s \<in> S" "X = orbit s"
  using assms unfolding orbits_def by auto

text \<open>The orbits cover @{term S}.\<close>

lemma orbits_cover: "\<Union> orbits = S"
  by (simp add: orbit_eq_Class orbits_def)

text \<open>The orbits are pairwise disjoint.\<close>

lemma orbits_disjoint: "disjoint orbits"
  by (simp add: disjnt_def orbit_disjoint orbits_def pairwise_imageI)

text \<open>The nontrivial orbits are the orbits containing more than one point.\<close>

definition nontrivial_orbits :: "'b set set"
  where "nontrivial_orbits = {X \<in> orbits. \<not> is_singleton X}"

lemma nontrivial_orbits_subset: "nontrivial_orbits \<subseteq> orbits"
  by (auto simp: nontrivial_orbits_def)

text \<open>The nontrivial orbits cover exactly the points that are not fixed.\<close>

lemma nontrivial_orbits_cover:
  "\<Union> nontrivial_orbits = S - fixed_points"
proof (rule set_eqI)
  fix x
  show "x \<in> \<Union> nontrivial_orbits \<longleftrightarrow> x \<in> S - fixed_points"
  proof
    assume "x \<in> \<Union> nontrivial_orbits"
    then obtain X where X: "X \<in> nontrivial_orbits" "x \<in> X" by auto
    then obtain s where s: "s \<in> S" "X = orbit s"
      using nontrivial_orbits_def orbits_coverE by auto
    have xS: "x \<in> S" using X s orbit_subset by auto
    have "orbit x = X" using orbit_eq_mem[OF s(1)] X(2) s(2) by simp
    moreover have "\<not> is_singleton X" using X by (simp add: nontrivial_orbits_def)
    ultimately have "x \<notin> fixed_points"
      using fixed_point_iff_orbit_singleton[OF xS] by (auto simp: is_singleton_def)
    with xS show "x \<in> S - fixed_points" by simp
  next
    assume x: "x \<in> S - fixed_points"
    have xS: "x \<in> S" using x by simp
    have "orbit x \<noteq> {x}"
      using fixed_point_iff_orbit_singleton[of x] x by simp
    then have "\<not> is_singleton (orbit x)"
      using orbit_self[OF xS] by (auto simp: is_singleton_def)
    then have "orbit x \<in> nontrivial_orbits"
      using x orbits_coverI by (simp add: nontrivial_orbits_def)
    then show "x \<in> \<Union> nontrivial_orbits" using x orbit_self by auto
  qed
qed

text \<open>Cardinality of @{term S} as a sum over orbits.\<close>

lemma card_S_sum_orbits:
  assumes "finite S"
  shows "card S = (\<Sum>X \<in> orbits. card X)"
proof -
  have "card (\<Union> orbits) = (\<Sum>X \<in> orbits. card X)"
  proof (rule card_Union_disjoint)
    show "disjoint orbits" by (rule orbits_disjoint)
    show "\<And>A. A \<in> orbits \<Longrightarrow> finite A"
      by (metis Union_upper assms orbits_cover rev_finite_subset)
  qed
  then show ?thesis by (simp add: orbits_cover)
qed

text \<open>Splitting the orbit partition into fixed points and nontrivial orbits gives the
  fixed-point form of the class equation.\<close>

lemma fixed_point_class_equation:
  assumes fin: "finite S"
  shows "card S = card fixed_points + (\<Sum>X \<in> nontrivial_orbits. card X)"
proof -
  have card_nontrivial:
      "card (\<Union> nontrivial_orbits) = (\<Sum>X \<in> nontrivial_orbits. card X)"
  proof (rule card_Union_disjoint)
    show "disjoint nontrivial_orbits"
      using orbits_disjoint nontrivial_orbits_subset
      by (auto simp: disjoint_def)
    show "\<And>X. X \<in> nontrivial_orbits \<Longrightarrow> finite X"
    proof -
      fix X assume "X \<in> nontrivial_orbits"
      then obtain s where "s \<in> S" "X = orbit s"
        using nontrivial_orbits_def orbits_coverE by auto
      then show "finite X"
        using orbit_subset[OF \<open>s \<in> S\<close>] fin by (meson finite_subset)
    qed
  qed
  have fin_fixed: "finite fixed_points"
    using fixed_points_subset fin by (rule finite_subset)
  have fin_nonfixed: "finite (S - fixed_points)" using fin by simp
  have split: "fixed_points \<union> (S - fixed_points) = S"
    using fixed_points_subset by auto
  have "card S = card fixed_points + card (S - fixed_points)"
    using card_Un_disjoint[OF fin_fixed fin_nonfixed] split by simp
  also have "\<dots> = card fixed_points + card (\<Union> nontrivial_orbits)"
    by (simp add: nontrivial_orbits_cover)
  also have "\<dots> = card fixed_points + (\<Sum>X \<in> nontrivial_orbits. card X)"
    by (simp add: card_nontrivial)
  finally show ?thesis .
qed

text \<open>If every nontrivial orbit has cardinality divisible by @{term k}, then the same is true
  of the set of non-fixed points.  This is the divisibility form of the fixed-point congruence.\<close>

lemma dvd_card_nonfixed_points:
  assumes fin: "finite S"
    and dvd: "\<And>s. \<lbrakk>s \<in> S; s \<notin> fixed_points\<rbrakk> \<Longrightarrow> k dvd card (orbit s)"
  shows "k dvd card (S - fixed_points)"
proof -
  have "k dvd card (\<Union> nontrivial_orbits)"
  proof (intro dvd_partition strip)
    show "finite (\<Union> nontrivial_orbits)"
      using fin nontrivial_orbits_cover by simp
    show "k dvd card X" if X: "X \<in> nontrivial_orbits" for X
    proof -
      obtain s where s: "s \<in> S" "X = orbit s"
        using X nontrivial_orbits_def orbits_coverE by auto
      have "s \<notin> fixed_points"
        using X s fixed_point_iff_orbit_singleton[OF s(1)]
        by (auto simp: nontrivial_orbits_def)
      then show ?thesis using dvd[OF s(1)] s(2) by simp
    qed
  qed (use orbits_disjoint nontrivial_orbits_subset in \<open>auto simp: disjoint_def\<close>)
  then show ?thesis by (simp add: nontrivial_orbits_cover)
qed

text \<open>If @{term k} divides the cardinality of every orbit, then @{term k} divides
  @{term "card S"}.\<close>

lemma dvd_orbits_dvd_S:
  assumes "finite S" "\<And>X. X \<in> orbits \<Longrightarrow> k dvd card X"
  shows "k dvd card S"
proof -
  have "k dvd card (\<Union> orbits)"
    using orbits_disjoint unfolding disjoint_def
    by (metis assms dvd_partition orbits_cover)
  then show ?thesis by (simp add: orbits_cover)
qed


end

section \<open>Sylow's Theorem\<close>

context Monoid
begin

definition power :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "power a n \<equiv> (((\<cdot>) a)^^ n) \<one>"

definition element_order :: "'a \<Rightarrow> nat"
  where "element_order a \<equiv> (LEAST n. n > 0 \<and> power a n = \<one>)"

lemma power_0 [simp]: "power a 0 = \<one>"
  by (simp add: power_def)

lemma power_Suc [simp]: "power a (Suc n) = a \<cdot> power a n"
  by (simp add: power_def)

lemma power_1 [simp]: "a \<in> M \<Longrightarrow> power a 1 = a"
  by simp

lemma power_closed [intro, simp]: "a \<in> M \<Longrightarrow> power a n \<in> M"
  by (induction n) auto

lemma power_add: "a \<in> M \<Longrightarrow> power a (m + n) = power a m \<cdot> power a n"
  by (induction m) (simp_all add: associative)

lemma power_mult: "a \<in> M \<Longrightarrow> power a (m * n) = power (power a m) n"
  by (induction n) (simp_all add: power_add)

lemma power_unit [simp]: "power \<one> n = \<one>"
  by (induction n) simp_all

lemma power_Suc_right: "a \<in> M \<Longrightarrow> power a (Suc n) = power a n \<cdot> a"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n) then show ?case
    using Suc_eq_plus1 local.power_add power_1 by presburger
qed

lemma power_commutes: "a \<in> M \<Longrightarrow> a \<cdot> power a n = power a n \<cdot> a"
  by (metis power_Suc power_Suc_right)

lemma power_commutes_power:
  "a \<in> M \<Longrightarrow> power a m \<cdot> power a n = power a n \<cdot> power a m"
  by (simp add: power_add[symmetric] add.commute)

lemma element_order_unit [simp]: "element_order \<one> = 1"
  unfolding element_order_def by (rule Least_equality) auto

end

context Group begin

lemma power_inverse:
  assumes "g \<in> G"
  shows "power (inverse g) n = inverse (power g n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "inverse g \<cdot> inverse (power g n) = inverse (power g n) \<cdot> inverse g"
    using power_commutes[of "inverse g" n] assms Suc by simp
  then have "power (inverse g) (Suc n) = inverse (power g n) \<cdot> inverse g"
    using Suc by simp
  also have "\<dots> = inverse (power g (Suc n))"
    using inverse_composition_commute[of g "power g n"] assms by simp
  finally show ?case .
qed

lemma finite_power_order_exists:
  assumes "finite G" "g \<in> G"
  shows "\<exists>n>0. power g n = \<one>"
proof -
  have False if "inj_on (power g) {..card G}"
  proof -
    have "card (power g ` {..card G}) = Suc (card G)"
      by (simp add: card_image that) 
    then show False
      using card_mono assms by (metis Suc_n_not_le_n imageE power_closed subsetI)
  qed
  then obtain i j where "i \<le> card G" "j \<le> card G" "i < j" and ij_eq: "power g i = power g j"
    by (metis (mono_tags, opaque_lifting) inj_on_def linorder_cases atMost_iff)
  then have "j = i + (j - i)" by simp
  then have eq: "power g j = power g i \<cdot> power g (j - i)"
    using power_add assms(2) by metis
  have "power g (j - i) = \<one>"
    by (metis Monoid.invertible_left_cancel Monoid_axioms assms(2) eq ij_eq invertible
        power_closed right_unit unit_closed)
  with \<open>i < j\<close> show ?thesis by (intro exI[of _ "j - i"]) auto
qed

lemma element_order_pos:
  assumes "finite G" "g \<in> G"
  shows "element_order g > 0"
proof -
  obtain n where "n > 0" "power g n = \<one>"
    using finite_power_order_exists[OF assms] by auto
  then show ?thesis
    unfolding element_order_def using LeastI[of "\<lambda>n. n > 0 \<and> power g n = \<one>" n] by auto
qed

lemma power_element_order:
  assumes "finite G" "g \<in> G"
  shows "power g (element_order g) = \<one>"
proof -
  obtain n where "n > 0" "power g n = \<one>"
    using finite_power_order_exists[OF assms] by auto
  then show ?thesis
    unfolding element_order_def using LeastI[of "\<lambda>n. n > 0 \<and> power g n = \<one>" n] 
    by auto
qed

lemma element_order_minimal:
  assumes "finite G" "g \<in> G" "n > 0" "power g n = \<one>"
  shows "element_order g \<le> n"
  unfolding element_order_def by (rule Least_le) (use assms in auto)

lemma element_order_dvd:
  assumes "finite G" "g \<in> G" "power g n = \<one>"
  shows "element_order g dvd n"
proof (rule ccontr)
  assume ndvd: "\<not> element_order g dvd n"
  have ord_pos: "element_order g > 0"
    using element_order_pos[OF assms(1,2)] .
  have mod_pos: "n mod element_order g > 0"
    using ndvd ord_pos by (metis dvd_eq_mod_eq_0 gr0I)
  have "power g n = power g (element_order g * (n div element_order g) + n mod element_order g)"
    by simp
  also have "\<dots> = power g (element_order g * (n div element_order g)) \<cdot> power g (n mod element_order g)"
    using assms(2) power_add by blast
  also have "power g (element_order g * (n div element_order g)) = power (power g (element_order g)) (n div element_order g)"
    using assms(2) power_mult by blast
  also have "\<dots> = power \<one> (n div element_order g)"
    using power_element_order[OF assms(1,2)] by simp
  also have "\<dots> = \<one>" by simp
  finally have "power g (n mod element_order g) = \<one>"
    using assms by simp
  moreover have "n mod element_order g < element_order g"
    using ord_pos by simp
  ultimately show False
    using element_order_minimal[OF assms(1,2) mod_pos] by linarith
qed

lemma power_mod_order:
  assumes "finite G" "g \<in> G"
  shows "power g n = power g (n mod element_order g)"
proof -
  have "n = element_order g * (n div element_order g) + n mod element_order g"
    by simp
  then have "power g n = power g (element_order g * (n div element_order g)) \<cdot> power g (n mod element_order g)"
    using assms(2) power_add by metis
  also have "power g (element_order g * (n div element_order g)) = power (power g (element_order g)) (n div element_order g)"
    using assms(2) power_mult by blast
  also have "\<dots> = \<one>"
    using power_element_order[OF assms] by simp
  finally show ?thesis using assms(2) by simp
qed

lemma power_eq_order_False:
  assumes "finite G" "g \<in> G"
    and "i < j" "j < element_order g"
    and "power g i = power g j"
  shows False
proof -
  from \<open>i < j\<close> have "j = i + (j - i)" by simp
  then have "power g j = power g i \<cdot> power g (j - i)"
    using power_add \<open>g \<in> G\<close> by metis
  with assms(5) have "power g i = power g i \<cdot> power g (j - i)" by simp
  then have "power g (j - i) = \<one>"
    using \<open>g \<in> G\<close>
    by (metis invertible invertible_left_inverse invertible_left_inverse2 power_closed)
  moreover from assms have "0 < j - i" "j - i < element_order g" by auto
  ultimately show False
    using assms element_order_dvd nat_dvd_not_less by blast
qed

lemma power_inj_on_order:
  assumes "finite G" "g \<in> G"
  shows "inj_on (power g) {..<element_order g}"
  unfolding inj_on_def
  by (metis assms lessThan_iff linorder_neqE_nat power_eq_order_False)

end


subsection \<open>Cyclic subgroups\<close>

text \<open>The cyclic subgroup generated by an element @{term g}: the set of its powers.
  For @{term g} of finite order this is @{term "power g ` {..<element_order g}"}.\<close>

definition (in Group) cyclic_subgroup :: "'a \<Rightarrow> 'a set"
  where "cyclic_subgroup g = power g ` {..<element_order g}"

context Group
begin

lemma cyclic_subgroup_eq_range:
  assumes fin: "finite G" and gG: "g \<in> G"
  shows "cyclic_subgroup g = range (power g)"
proof (rule set_eqI)
  fix x
  show "x \<in> cyclic_subgroup g \<longleftrightarrow> x \<in> range (power g)"
  proof
    assume "x \<in> range (power g)"
    then obtain n where "x = power g n" by auto
    then have "x = power g (n mod element_order g)"
      using power_mod_order[OF fin gG] by simp
    moreover have "n mod element_order g < element_order g" 
      using element_order_pos[OF fin gG] by simp
    ultimately show "x \<in> cyclic_subgroup g" unfolding cyclic_subgroup_def by auto
  qed (auto simp: cyclic_subgroup_def)
qed

lemma cyclic_subgroup_subset:
  assumes "g \<in> G" shows "cyclic_subgroup g \<subseteq> G"
  unfolding cyclic_subgroup_def using assms by auto

lemma power_mem_cyclic_subgroup:
  assumes fin: "finite G" and gG: "g \<in> G"
  shows "power g i \<in> cyclic_subgroup g"
  using cyclic_subgroup_eq_range[OF fin gG] by blast

text \<open>The cyclic subgroup is indeed a subgroup.\<close>
theorem cyclic_subgroup_is_subgroup:
  assumes fin: "finite G" and gG: "g \<in> G"
  shows "Subgroup (cyclic_subgroup g) G (\<cdot>) \<one>"
proof -
  have ord_pos: "element_order g > 0" using element_order_pos[OF fin gG] .
  note C_alt = cyclic_subgroup_eq_range[OF fin gG]
  have unit_C: "\<one> \<in> cyclic_subgroup g" unfolding C_alt
    by (metis local.power_0 rangeI)
  have comp_C: "\<And>a b. a \<in> cyclic_subgroup g \<Longrightarrow> b \<in> cyclic_subgroup g \<Longrightarrow> a \<cdot> b \<in> cyclic_subgroup g"
  proof -
    fix a b assume "a \<in> cyclic_subgroup g" "b \<in> cyclic_subgroup g"
    then obtain i j where "a = power g i" "b = power g j" unfolding C_alt by auto
    then have "a \<cdot> b = power g (i + j)" using gG power_add by auto
    then show "a \<cdot> b \<in> cyclic_subgroup g" unfolding C_alt by blast
  qed
  have inv_g: "inverse g = power g (element_order g - 1)"
  proof (rule inverse_equality)
    show "g \<cdot> power g (element_order g - 1) = \<one>"
      using power_element_order[OF fin gG] ord_pos
      by (metis Suc_diff_1 local.power_Suc)
    then show "power g (element_order g - 1) \<cdot> g = \<one>"
      using power_element_order[OF fin gG] ord_pos gG local.power_commutes by auto
    show "g \<in> G" by fact
    show "power g (element_order g - 1) \<in> G" using gG by simp
  qed
  have inv_C: "\<And>a. a \<in> cyclic_subgroup g \<Longrightarrow> inverse a \<in> cyclic_subgroup g"
  proof -
    fix a assume "a \<in> cyclic_subgroup g"
    then obtain i where a: "a = power g i" unfolding C_alt by auto
    have "inverse a = power (inverse g) i" using a power_inverse[OF gG] by simp
    also have "\<dots> = power (power g (element_order g - 1)) i" using inv_g by simp
    also have "\<dots> = power g ((element_order g - 1) * i)" using gG power_mult by simp
    finally have "inverse a = power g ((element_order g - 1) * i)" .
    then show "inverse a \<in> cyclic_subgroup g" unfolding C_alt by blast
  qed
  show ?thesis
    using subgroupI[of "cyclic_subgroup g"] cyclic_subgroup_subset[OF gG] unit_C comp_C inv_C
    by auto
qed

text \<open>Its cardinality is the order of the generator.\<close>
theorem card_cyclic_subgroup:
  assumes fin: "finite G" and gG: "g \<in> G"
  shows "card (cyclic_subgroup g) = element_order g"
proof -
  have "card (cyclic_subgroup g) = card (power g ` {..<element_order g})"
    unfolding cyclic_subgroup_def by simp
  also have "\<dots> = card {..<element_order g}"
    using card_image power_inj_on_order[OF fin gG] by blast
  also have "\<dots> = element_order g" by simp
  finally show ?thesis .
qed

end (* Group *)

lemma (in Group) element_order_dvd_card:
  assumes fin: "finite G" and gG: "g \<in> G"
  shows "element_order g dvd (card G)"
proof -
  interpret CG: subgroup_of_group "cyclic_subgroup g" G "(\<cdot>)" \<one>
    by (simp add: Group_axioms cyclic_subgroup_is_subgroup[OF fin gG] subgroup_of_group_def)
  from CG.lagrange[OF fin]
  have "card G = element_order g * CG.index"
    using card_cyclic_subgroup[OF fin gG] by simp
  then show ?thesis by auto
qed

lemma (in Group) power_order_eq_1 [simp]: "g\<in>G \<Longrightarrow> finite G \<Longrightarrow> power g (card G) = \<one>"
  by (simp add: element_order_dvd_card power_mod_order)


lemma (in Monoid_homomorphism) commutes_with_power:
  assumes "g \<in> M"
  shows "\<eta> (source.power g n) = target.power (\<eta> g) n"
  by (induction n) (simp_all add: commutes_with_unit commutes_with_composition assms)

lemma (in group_homomorphism) element_order_image_dvd:
  assumes "finite G" "finite G'" "g \<in> G"
  shows "target.element_order (\<eta> g) dvd source.element_order g"
  by (metis assms commutes_with_power commutes_with_unit map_closed
      source.power_element_order target.element_order_dvd)

lemma (in group_isomorphism) element_order_preserved:
  assumes "finite G" "finite G'" "g \<in> G"
  shows "target.element_order (\<eta> g) = source.element_order g"
proof (rule dvd_antisym)
  show "target.element_order (\<eta> g) dvd source.element_order g"
    using element_order_image_dvd assms by blast
  show "source.element_order g dvd target.element_order (\<eta> g)"
  proof -
    have eta_g: "\<eta> g \<in> G'" using assms map_closed by blast
    have "target.power (\<eta> g) (target.element_order (\<eta> g)) = \<one>'"
      using target.power_element_order[OF assms(2) eta_g] .
    then have img_eq: "\<eta> (source.power g (target.element_order (\<eta> g))) = \<eta> \<one>"
      using commutes_with_power assms commutes_with_unit by simp
    have inj: "inj_on \<eta> G" using bij_betw_def bijective by blast
    have "source.power g (target.element_order (\<eta> g)) = \<one>"
      using inj_onD[OF inj img_eq _ source.unit_closed] assms by simp
    then show ?thesis
      using source.element_order_dvd[OF assms(1,3)] by blast
  qed
qed

text \<open>The same fact stated with the raw \<open>Monoid.element_order\<close> applied to the explicit
  operations and units, rather than the locale-qualified \<open>source.element_order\<close> /
  \<open>target.element_order\<close>.  This is the form a caller working with concrete groups (e.g.\ the
  symmetric group under \<open>(\<circ>)\<close>/\<open>id\<close>) can unify against directly --- the prefixed versions are
  definitionally equal but do not match by name across interpretations.\<close>
lemma (in group_isomorphism) element_order_preserved':
  assumes "finite G" "finite G'" "g \<in> G"
  shows "Monoid.element_order (\<cdot>') (\<one>') (\<eta> g) = Monoid.element_order (\<cdot>) \<one> g"
  using element_order_preserved[OF assms] .

lemma (in Group) element_order_power_prime:
  assumes fin: "finite G" and gG: "g \<in> G" and prime: "prime p" and dvd: "p dvd element_order g"
  shows "element_order (power g (element_order g div p)) = p"
proof -
  define k where "k = element_order g div p"
  have ord_eq: "element_order g = p * k"
    using dvd by (simp add: k_def)
  have k_pos: "k > 0"
    using element_order_pos[OF fin gG] ord_eq prime by (metis gr0I mult_is_0)
  have gk: "power g k \<in> G" using gG by simp
  have "power (power g k) p = power g (element_order g)"
    by (simp add: gG local.power_mult mult.commute ord_eq)
  then have dvd_p: "element_order (power g k) dvd p"
    using element_order_dvd[OF fin gk]
    by (simp add: fin gG power_element_order)
  have "element_order (power g k) \<noteq> 1"
    using power_element_order[of "power g k"] fin gG gk k_pos
    by (metis dvd_mult_cancel2 element_order_dvd not_prime_1 ord_eq power_1 prime)
  with dvd_p prime show ?thesis
    unfolding k_def by (metis prime_nat_iff)
qed

end
