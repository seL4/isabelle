(* Author: Tobias Nipkow *)

section \<open>Tree Rotations\<close>

theory Tree_Rotations
imports "HOL-Library.Tree"
begin

text \<open>How to transform a tree into a list and into any other tree (with the same @{const inorder})
by rotations.\<close>

fun is_list :: "'a tree \<Rightarrow> bool" where
"is_list (Node l _ r) = (l = Leaf \<and> is_list r)" |
"is_list Leaf = True"

text \<open>Termination proof via measure function. NB @{term "size t - rlen t"} works for
the actual rotation equation but not for the second equation.\<close>

fun rlen :: "'a tree \<Rightarrow> nat" where
"rlen Leaf = 0" |
"rlen (Node l x r) = rlen r + 1"

lemma rlen_le_size: "rlen t \<le> size t"
by(induction t) auto


subsection \<open>Without positions\<close>

function (sequential) list_of :: "'a tree \<Rightarrow> 'a tree" where
"list_of (Node (Node A a B) b C) = list_of (Node A a (Node B b C))" |
"list_of (Node Leaf a A) = Node Leaf a (list_of A)" |
"list_of Leaf = Leaf"
by pat_completeness auto

termination
proof
  let ?R = "measure(\<lambda>t. 2*size t - rlen t)"
  show "wf ?R" by (auto simp add: mlex_prod_def)

  fix A a B b C
  show "(Node A a (Node B b C), Node (Node A a B) b C) \<in> ?R"
    using rlen_le_size[of C] by(simp)

  fix a A show "(A, Node Leaf a A) \<in> ?R" using rlen_le_size[of A] by(simp)
qed

lemma is_list_rot: "is_list(list_of t)"
by (induction t rule: list_of.induct) auto

lemma inorder_rot: "inorder(list_of t) = inorder t"
by (induction t rule: list_of.induct) auto


subsection \<open>With positions\<close>

datatype dir = L | R

type_synonym "pos" = "dir list"

function (sequential) rotR_poss :: "'a tree \<Rightarrow> pos list" where
"rotR_poss (Node (Node A a B) b C) = [] # rotR_poss (Node A a (Node B b C))" |
"rotR_poss (Node Leaf a A) = map (Cons R) (rotR_poss A)" |
"rotR_poss Leaf = []"
by pat_completeness auto

termination
proof
  let ?R = "measure(\<lambda>t. 2*size t - rlen t)"
  show "wf ?R" by (auto simp add: mlex_prod_def)

  fix A a B b C
  show "(Node A a (Node B b C), Node (Node A a B) b C) \<in> ?R"
    using rlen_le_size[of C] by(simp)

  fix a A show "(A, Node Leaf a A) \<in> ?R" using rlen_le_size[of A] by(simp)
qed

fun rotR :: "'a tree \<Rightarrow> 'a tree" where
"rotR (Node (Node A a B) b C) = Node A a (Node B b C)"

fun rotL :: "'a tree \<Rightarrow> 'a tree" where
"rotL (Node A a (Node B b C)) = Node (Node A a B) b C"

fun apply_at :: "('a tree \<Rightarrow> 'a tree) \<Rightarrow> pos \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "apply_at f [] t = f t"
| "apply_at f (L # ds) (Node l a r) = Node (apply_at f ds l) a r"
| "apply_at f (R # ds) (Node l a r) = Node l a (apply_at f ds r)"

fun apply_ats :: "('a tree \<Rightarrow> 'a tree) \<Rightarrow> pos list \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"apply_ats _ [] t = t" |
"apply_ats f (p#ps) t = apply_ats f ps (apply_at f p t)"

lemma apply_ats_append:
  "apply_ats f (ps\<^sub>1 @ ps\<^sub>2) t = apply_ats f ps\<^sub>2 (apply_ats f ps\<^sub>1 t)"
by (induction ps\<^sub>1 arbitrary: t) auto

abbreviation "rotRs \<equiv> apply_ats rotR"
abbreviation "rotLs \<equiv> apply_ats rotL"

lemma apply_ats_map_R: "apply_ats f (map ((#) R) ps) \<langle>l, a, r\<rangle> = Node l a (apply_ats f ps r)"
by(induction ps arbitrary: r) auto

lemma inorder_rotRs_poss: "inorder (rotRs (rotR_poss t) t) = inorder t"
apply(induction t rule: rotR_poss.induct)
apply(auto simp: apply_ats_map_R)
done

lemma is_list_rotRs: "is_list (rotRs (rotR_poss t) t)"
apply(induction t rule: rotR_poss.induct)
apply(auto simp: apply_ats_map_R)
done

lemma "is_list (rotRs ps t) \<longrightarrow> length ps \<le> length(rotR_poss t)"
quickcheck[expect=counterexample]
oops

lemma length_rotRs_poss: "length (rotR_poss t) = size t - rlen t"
proof(induction t rule: rotR_poss.induct)
  case (1 A a B b C)
  then show ?case using rlen_le_size[of C] by simp
qed auto

lemma is_list_inorder_same:
  "is_list t1 \<Longrightarrow> is_list t2 \<Longrightarrow> inorder t1 = inorder t2 \<Longrightarrow> t1 = t2"
proof(induction t1 arbitrary: t2)
  case Leaf
  then show ?case by simp
next
  case Node
  then show ?case by (cases t2) simp_all
qed

lemma rot_id: "rotLs (rev (rotR_poss t)) (rotRs (rotR_poss t) t) = t"
apply(induction t rule: rotR_poss.induct)
apply(auto simp: apply_ats_map_R rev_map apply_ats_append)
done

corollary tree_to_tree_rotations: assumes "inorder t1 = inorder t2"
shows "rotLs (rev (rotR_poss t2)) (rotRs (rotR_poss t1) t1) = t2"
proof -
  have "rotRs (rotR_poss t1) t1 = rotRs (rotR_poss t2) t2" (is "?L = ?R")
    by (simp add: assms inorder_rotRs_poss is_list_inorder_same is_list_rotRs)
  hence "rotLs (rev (rotR_poss t2)) ?L = rotLs (rev (rotR_poss t2)) ?R"
    by simp
  also have "\<dots> = t2" by(rule rot_id)
  finally show ?thesis .
qed

lemma size_rlen_better_ub: "size t - rlen t \<le> size t - 1"
by (cases t) auto

end
