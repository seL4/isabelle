section \<open>The Derived Series and Solvable Groups\<close>

theory Derived_Series
  imports Commutator
begin

text \<open>
  The derived series of a group is obtained by iterating the derived-subgroup
  construction.  A group is solvable when its derived series reaches the trivial
  subgroup.  As a first milestone we show that every abelian group is solvable.
\<close>

context Group
begin

text \<open>The derived series, as a sequence of subsets of the carrier.\<close>
primrec derivedSeries :: "nat \<Rightarrow> 'a set"
  where
    "derivedSeries 0 = G"
  | "derivedSeries (Suc n) = commutator_subgroup (derivedSeries n) (derivedSeries n)"

text \<open>A group is solvable if its derived series reaches the trivial subgroup.\<close>
definition solvable :: bool
  where "solvable \<equiv> (\<exists>n. derivedSeries n = {\<one>})"

text \<open>Each term of the derived series is a subgroup.\<close>
lemma derivedSeries_subgroup: "Subgroup (derivedSeries n) G (\<cdot>) \<one>"
  by (cases n) (auto simp: commutator_subgroup_is_subgroup group_self_subgroup)

lemma derivedSeries_subset: "derivedSeries n \<subseteq> G" and derivedSeries_unit_closed: "\<one> \<in> derivedSeries n"
proof -
  interpret S: Subgroup "derivedSeries n" G "(\<cdot>)" \<one> by (rule derivedSeries_subgroup)
  show "derivedSeries n \<subseteq> G" by (rule S.subset)
  show "\<one> \<in> derivedSeries n" by (rule S.sub_unit_closed)
qed

text \<open>The commutator subgroup of a subgroup @{term H} (with itself) is contained in @{term H}: the
  commutator generators lie in @{term H} (closed under the operation and inverse), and @{term H}, being
  a subgroup, contains the subgroup they generate.\<close>
lemma commutator_subgroup_self_subset:
  assumes H: "Subgroup H G (\<cdot>) \<one>"
  shows "commutator_subgroup H H \<subseteq> H"
proof -
  interpret S: Subgroup H G "(\<cdot>)" \<one> by (rule H)
  show ?thesis
    using S.sub.commutator_subgroup_subset assms commutator_subgroup_subset_subgroup
    by blast
qed

text \<open>The derived series is decreasing: @{term "derivedSeries (Suc n) \<subseteq> derivedSeries n"}.\<close>
lemma derivedSeries_Suc_subset: "derivedSeries (Suc n) \<subseteq> derivedSeries n"
  using commutator_subgroup_self_subset[OF derivedSeries_subgroup] by simp

lemma derivedSeries_antimono: "m \<le> n \<Longrightarrow> derivedSeries n \<subseteq> derivedSeries m"
  by (induction n) (use derivedSeries_Suc_subset not_less_eq_eq in fastforce)+

text \<open>In an abelian group every commutator is the unit.\<close>
lemma commutator_elt_abelian:
  assumes "commutative_monoid G (\<cdot>) \<one>" and "a \<in> G" "b \<in> G"
  shows "commutator_elt a b = \<one>"
proof -
  interpret comm: commutative_monoid G "(\<cdot>)" \<one> by (rule assms(1))
  show ?thesis
    using assms(2,3) comm.commutative commutator_elt_def commute_iff_inverse by auto
qed

text \<open>In an abelian group the derived subgroup is trivial.\<close>
lemma derived_trivial_if_abelian:
  assumes "commutative_monoid G (\<cdot>) \<one>"
  shows "derived = {\<one>}"
proof -
  interpret D: Subgroup derived G "(\<cdot>)" \<one> by (rule derived_is_subgroup)
  have "derived \<subseteq> {\<one>}"
    unfolding derived_def commutator_subgroup_def
    using commutator_elt_abelian[OF assms]  
    by (intro Gen_minimal[OF trivial_subgroup]) auto
  then show ?thesis using D.sub_unit_closed by auto
qed

text \<open>Milestone: every abelian group is solvable.\<close>
theorem abelian_imp_solvable:
  assumes "commutative_monoid G (\<cdot>) \<one>"
  shows solvable
  unfolding solvable_def
  by (metis assms derivedSeries.simps derived_def derived_trivial_if_abelian)

end (* Group *)

end
