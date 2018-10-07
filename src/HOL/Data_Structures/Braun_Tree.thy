(* Author: Tobias Nipkow *)

section \<open>Braun Trees\<close>

theory Braun_Tree
imports "HOL-Library.Tree_Real"
begin

text \<open>Braun Trees were studied by Braun and Rem~\cite{BraunRem}
and later Hoogerwoord~\cite{Hoogerwoord} who gave them their name.\<close>

fun braun :: "'a tree \<Rightarrow> bool" where
"braun Leaf = True" |
"braun (Node l x r) = (size r \<le> size l \<and> size l \<le> size r + 1 \<and> braun l \<and> braun r)"

text \<open>The shape of a Braun-tree is uniquely determined by its size:\<close>

lemma braun_unique: "\<lbrakk> braun (t1::unit tree); braun t2; size t1 = size t2 \<rbrakk> \<Longrightarrow> t1 = t2"
proof (induction t1 arbitrary: t2)
  case Leaf thus ?case by simp
next
  case (Node l1 _ r1)
  from Node.prems(3) have "t2 \<noteq> Leaf" by auto
  then obtain l2 x2 r2 where [simp]: "t2 = Node l2 x2 r2" by (meson neq_Leaf_iff)
  with Node.prems have "size l1 = size l2 \<and> size r1 = size r2" by simp
  thus ?case using Node.prems(1,2) Node.IH by auto
qed

text \<open>Braun trees are balanced:\<close>

lemma balanced_if_braun: "braun t \<Longrightarrow> balanced t"
proof(induction t)
  case Leaf show ?case by (simp add: balanced_def)
next
  case (Node l x r)
  have "size l = size r \<or> size l = size r + 1" (is "?A \<or> ?B")
    using Node.prems by auto
  thus ?case
  proof
    assume "?A"
    thus ?thesis using Node
      apply(simp add: balanced_def min_def max_def)
      by (metis Node.IH balanced_optimal le_antisym le_refl)
  next
    assume "?B"
    thus ?thesis using Node by(intro balanced_Node_if_wbal1) auto
  qed
qed

end