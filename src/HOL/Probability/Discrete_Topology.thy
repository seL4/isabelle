(*  Title:      HOL/Probability/Discrete_Topology.thy
    Author:     Fabian Immler, TU München
*)

theory Discrete_Topology
imports "HOL-Analysis.Analysis"
begin

text \<open>Copy of discrete types with discrete topology. This space is polish.\<close>

typedef 'a discrete = "UNIV::'a set"
morphisms of_discrete discrete
..

instantiation discrete :: (type) metric_space
begin

definition dist_discrete :: "'a discrete \<Rightarrow> 'a discrete \<Rightarrow> real"
  where "dist_discrete n m = (if n = m then 0 else 1)"

definition uniformity_discrete :: "('a discrete \<times> 'a discrete) filter" where
  "(uniformity::('a discrete \<times> 'a discrete) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition "open_discrete" :: "'a discrete set \<Rightarrow> bool" where
  "(open::'a discrete set \<Rightarrow> bool) U \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance proof qed (auto simp: uniformity_discrete_def open_discrete_def dist_discrete_def intro: exI[where x=1])
end

lemma open_discrete: "open (S :: 'a discrete set)"
  unfolding open_dist dist_discrete_def by (auto intro!: exI[of _ "1 / 2"])

instance discrete :: (type) complete_space
proof
  fix X::"nat\<Rightarrow>'a discrete"
  assume "Cauchy X"
  then obtain n where "\<forall>m\<ge>n. X n = X m"
    by (force simp: dist_discrete_def Cauchy_def split: if_split_asm dest:spec[where x=1])
  thus "convergent X"
    by (intro convergentI[where L="X n"] tendstoI eventually_sequentiallyI[of n])
       (simp add: dist_discrete_def)
qed

instance discrete :: (countable) countable
proof
  have "inj (\<lambda>c::'a discrete. to_nat (of_discrete c))"
    by (simp add: inj_on_def of_discrete_inject)
  thus "\<exists>f::'a discrete \<Rightarrow> nat. inj f" by blast
qed

instance discrete :: (countable) second_countable_topology
proof
  let ?B = "range (\<lambda>n::'a discrete. {n})"
  have "\<And>S. generate_topology ?B (\<Union>x\<in>S. {x})"
    by (intro generate_topology_Union) (auto intro: generate_topology.intros)
  then have "open = generate_topology ?B"
    by (auto intro!: ext simp: open_discrete)
  moreover have "countable ?B" by simp
  ultimately show "\<exists>B::'a discrete set set. countable B \<and> open = generate_topology B" by blast
qed

instance discrete :: (countable) polish_space ..

end
