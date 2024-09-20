theory Left_Coset
imports Coset

(*This instance of Coset.thy but for left cosets is due to Jonas Rädle and has been imported
  from the AFP entry Orbit_Stabiliser. *)

begin

definition
  LCOSETS  :: "[_, 'a set] \<Rightarrow> ('a set)set"   (\<open>lcosets\<index> _\<close> [81] 80)
  where "lcosets\<^bsub>G\<^esub> H = (\<Union>a\<in>carrier G. {a <#\<^bsub>G\<^esub> H})"

definition
  LFactGroup :: "[('a,'b) monoid_scheme, 'a set] \<Rightarrow> ('a set) monoid" (infixl \<open>LMod\<close> 65)
    \<comment> \<open>Actually defined for groups rather than monoids\<close>
   where "LFactGroup G H = \<lparr>carrier = lcosets\<^bsub>G\<^esub> H, mult = set_mult G, one = H\<rparr>"

lemma (in group) lcos_self: "[| x \<in> carrier G; subgroup H G |] ==> x \<in> x <# H"
  by (simp add: group_l_invI subgroup.lcos_module_rev subgroup.one_closed)

text \<open>Elements of a left coset are in the carrier\<close>
lemma (in subgroup) elemlcos_carrier:
  assumes "group G" "a \<in> carrier G" "a' \<in> a <# H"
  shows "a' \<in> carrier G"
  by (meson assms group.l_coset_carrier subgroup_axioms)

text \<open>Step one for lemma \<open>rcos_module\<close>\<close>
lemma (in subgroup) lcos_module_imp:
  assumes "group G"
  assumes xcarr: "x \<in> carrier G"
      and x'cos: "x' \<in> x <# H"
  shows "(inv x \<otimes> x') \<in> H"
proof -
  interpret group G by fact
  obtain h
    where hH: "h \<in> H" and x': "x' = x \<otimes> h" and hcarr: "h \<in> carrier G"
    using assms by (auto simp: l_coset_def)
  have "(inv x) \<otimes> x' = (inv x) \<otimes> (x \<otimes> h)"
    by (simp add: x')
  have "\<dots> = (x \<otimes> inv x) \<otimes> h"
    by (metis hcarr inv_closed inv_inv l_inv m_assoc xcarr)
  also have "\<dots> = h"
    by (simp add: hcarr xcarr)
  finally have "(inv x) \<otimes> x' = h"
    using x' by metis
  then show "(inv x) \<otimes> x' \<in> H"
    using hH by force
qed

text \<open>Left cosets are subsets of the carrier.\<close> 
lemma (in subgroup) lcosets_carrier:
  assumes "group G"
  assumes XH: "X \<in> lcosets H"
  shows "X \<subseteq> carrier G"
proof -
  interpret group G by fact
  show "X \<subseteq> carrier G"
    using XH l_coset_subset_G subset by (auto simp: LCOSETS_def)
qed

lemma (in group) lcosets_part_G:
  assumes "subgroup H G"
  shows "\<Union>(lcosets H) = carrier G"
proof -
  interpret subgroup H G by fact
  show ?thesis
  proof
    show "\<Union> (lcosets H) \<subseteq> carrier G"
      by (force simp add: LCOSETS_def l_coset_def)
    show "carrier G \<subseteq> \<Union> (lcosets H)"
      by (auto simp add: LCOSETS_def intro: lcos_self assms)
  qed
qed

lemma (in group) lcosets_subset_PowG:
     "subgroup H G  \<Longrightarrow> lcosets H \<subseteq> Pow(carrier G)"
  using lcosets_part_G subset_Pow_Union by blast

lemma (in group) lcos_disjoint:
  assumes "subgroup H G"
  assumes p: "a \<in> lcosets H" "b \<in> lcosets H" "a\<noteq>b"
  shows "a \<inter> b = {}"
proof -
  interpret subgroup H G by fact
  show ?thesis
    using p l_repr_independence subgroup_axioms unfolding LCOSETS_def disjoint_iff
    by blast
qed

text\<open>The next two lemmas support the proof of \<open>card_cosets_equal\<close>.\<close>
lemma (in group) inj_on_f':
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. y \<otimes> inv a) (a <# H)"
  by (simp add: inj_on_g l_coset_subset_G)

lemma (in group) inj_on_f'':
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. inv a \<otimes> y) (a <# H)"
  by (meson inj_on_cmult inv_closed l_coset_subset_G subset_inj_on)

lemma (in group) inj_on_g':
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. a \<otimes> y) H"
  using inj_on_cmult inj_on_subset by blast

lemma (in group) l_card_cosets_equal:
  assumes "c \<in> lcosets H" and H: "H \<subseteq> carrier G" and fin: "finite(carrier G)"
  shows "card H = card c"
proof -
  obtain x where x: "x \<in> carrier G" and c: "c = x <# H"
    using assms by (auto simp add: LCOSETS_def)
  have "inj_on ((\<otimes>) x) H"
    by (simp add: H group.inj_on_g' x)
  moreover
  have "(\<otimes>) x ` H \<subseteq> x <# H"
    by (force simp add: m_assoc subsetD l_coset_def)
  moreover
  have "inj_on ((\<otimes>) (inv x)) (x <# H)"
    by (simp add: H group.inj_on_f'' x)
  moreover
  have "\<And>h. h \<in> H \<Longrightarrow> inv x \<otimes> (x \<otimes> h) \<in> H"
    by (metis H in_mono inv_solve_left m_closed x)
  then have "(\<otimes>) (inv x) ` (x <# H) \<subseteq> H"
    by (auto simp: l_coset_def)
  ultimately show ?thesis
    by (metis H fin c card_bij_eq finite_imageD finite_subset)
qed

theorem (in group) l_lagrange:
  assumes "finite(carrier G)" "subgroup H G"
  shows "card(lcosets H) * card(H) = order(G)"
proof -
  have "card H * card (lcosets H) = card (\<Union> (lcosets H))"
    using card_partition
    by (metis (no_types, lifting) assms finite_UnionD l_card_cosets_equal lcos_disjoint lcosets_part_G subgroup.subset)
  then show ?thesis
    by (simp add: assms(2) lcosets_part_G mult.commute order_def)
qed

end
