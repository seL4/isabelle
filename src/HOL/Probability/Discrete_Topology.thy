(*  Title:      HOL/Probability/Discrete_Topology.thy
    Author:     Fabian Immler, TU München
*)

theory Discrete_Topology
imports "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

text \<open>Copy of discrete types with discrete topology. This space is polish.\<close>

typedef 'a discrete = "UNIV::'a set"
morphisms of_discrete discrete
..

instantiation discrete :: (type) topological_space
begin

definition open_discrete::"'a discrete set \<Rightarrow> bool"
  where "open_discrete s = True"

instance proof qed (auto simp: open_discrete_def)
end

instantiation discrete :: (type) metric_space
begin

definition dist_discrete::"'a discrete \<Rightarrow> 'a discrete \<Rightarrow> real"
  where "dist_discrete n m = (if n = m then 0 else 1)"

instance proof qed (auto simp: open_discrete_def dist_discrete_def intro: exI[where x=1])
end

instance discrete :: (type) complete_space
proof
  fix X::"nat\<Rightarrow>'a discrete" assume "Cauchy X"
  hence "\<exists>n. \<forall>m\<ge>n. X n = X m"
    by (force simp: dist_discrete_def Cauchy_def split: split_if_asm dest:spec[where x=1])
  then guess n ..
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
    by (auto intro!: ext simp: open_discrete_def)
  moreover have "countable ?B" by simp
  ultimately show "\<exists>B::'a discrete set set. countable B \<and> open = generate_topology B" by blast
qed

instance discrete :: (countable) polish_space ..

end
