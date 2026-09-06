theory Simple_Group
  imports Group_Theory
begin

section \<open>Simple groups\<close>

text \<open>
  A simple group is a non-trivial group whose only normal subgroups are the
  trivial subgroup and the whole group.  This theory states the definition in
  the set-based group language used by \<open>Group_Theory\<close>.
  The resulting locale is the foundation for the composition-series
  development that follows.
\<close>

locale Simple_Group = Group G "(\<cdot>)" \<one>
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  assumes nontrivial: "G \<noteq> {\<one>}"
    and normal_subgroup_eq_trivial_or_top:
      "\<And>K. normal_subgroup K G (\<cdot>) \<one> \<Longrightarrow> K = {\<one>} \<or> K = G"
begin

text \<open>Simple groups have no proper non-trivial normal subgroups.\<close>

lemma proper_normal_subgroup_is_trivial:
  assumes K: "normal_subgroup K G (\<cdot>) \<one>" and proper: "K \<noteq> G"
  shows "K = {\<one>}"
  using normal_subgroup_eq_trivial_or_top[OF K] proper by blast

lemma nontrivial_normal_subgroup_is_top:
  assumes K: "normal_subgroup K G (\<cdot>) \<one>" and K_nontrivial: "K \<noteq> {\<one>}"
  shows "K = G"
  using normal_subgroup_eq_trivial_or_top[OF K] K_nontrivial by blast

end

end
