(*  Title:      HOL/Probability/Discrete_Topology.thy
    Author:     Fabian Immler, TU München
*)

theory Discrete_Topology
imports Multivariate_Analysis
begin

text {* Copy of discrete types with discrete topology. This space is polish. *}

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
  let ?B = "(range (\<lambda>n::nat. {from_nat n::'a discrete}))"
  have "topological_basis ?B"
  proof (intro topological_basisI)
    fix x::"'a discrete" and O' assume "open O'" "x \<in> O'"
    thus "\<exists>B'\<in>range (\<lambda>n. {from_nat n}). x \<in> B' \<and> B' \<subseteq> O'"
      by (auto intro: exI[where x="to_nat x"])
  qed (simp add: open_discrete_def)
  moreover have "countable ?B" by simp
  ultimately show "\<exists>B::'a discrete set set. countable B \<and> topological_basis B" by blast
qed

instance discrete :: (countable) polish_space ..

end
