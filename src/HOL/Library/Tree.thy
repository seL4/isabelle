(* Author: Tobias Nipkow *)

section \<open>Binary Tree\<close>

theory Tree
imports Main
begin

datatype 'a tree =
  is_Leaf: Leaf ("\<langle>\<rangle>") |
  Node (left: "'a tree") (val: 'a) (right: "'a tree") ("(1\<langle>_,/ _,/ _\<rangle>)")
  where
    "left Leaf = Leaf"
  | "right Leaf = Leaf"
datatype_compat tree

text\<open>Can be seen as counting the number of leaves rather than nodes:\<close>

definition size1 :: "'a tree \<Rightarrow> nat" where
"size1 t = size t + 1"

lemma size1_simps[simp]:
  "size1 \<langle>\<rangle> = 1"
  "size1 \<langle>l, x, r\<rangle> = size1 l + size1 r"
by (simp_all add: size1_def)

lemma size1_ge0[simp]: "0 < size1 t"
by (simp add: size1_def)

lemma size_0_iff_Leaf: "size t = 0 \<longleftrightarrow> t = Leaf"
by(cases t) auto

lemma neq_Leaf_iff: "(t \<noteq> \<langle>\<rangle>) = (\<exists>l a r. t = \<langle>l, a, r\<rangle>)"
by (cases t) auto

lemma finite_set_tree[simp]: "finite(set_tree t)"
by(induction t) auto

lemma size_map_tree[simp]: "size (map_tree f t) = size t"
by (induction t) auto

lemma size1_map_tree[simp]: "size1 (map_tree f t) = size1 t"
by (simp add: size1_def)


subsection "The Height"

class height = fixes height :: "'a \<Rightarrow> nat"

instantiation tree :: (type)height
begin

fun height_tree :: "'a tree => nat" where
"height Leaf = 0" |
"height (Node t1 a t2) = max (height t1) (height t2) + 1"

instance ..

end

lemma height_map_tree[simp]: "height (map_tree f t) = height t"
by (induction t) auto

lemma size1_height: "size t + 1 \<le> 2 ^ height (t::'a tree)"
proof(induction t)
  case (Node l a r)
  show ?case
  proof (cases "height l \<le> height r")
    case True
    have "size(Node l a r) + 1 = (size l + 1) + (size r + 1)" by simp
    also have "size l + 1 \<le> 2 ^ height l" by(rule Node.IH(1))
    also have "size r + 1 \<le> 2 ^ height r" by(rule Node.IH(2))
    also have "(2::nat) ^ height l \<le> 2 ^ height r" using True by simp
    finally show ?thesis using True by (auto simp: max_def mult_2)
  next
    case False
    have "size(Node l a r) + 1 = (size l + 1) + (size r + 1)" by simp
    also have "size l + 1 \<le> 2 ^ height l" by(rule Node.IH(1))
    also have "size r + 1 \<le> 2 ^ height r" by(rule Node.IH(2))
    also have "(2::nat) ^ height r \<le> 2 ^ height l" using False by simp
    finally show ?thesis using False by (auto simp: max_def mult_2)
  qed
qed simp


fun min_height :: "'a tree \<Rightarrow> nat" where
"min_height Leaf = 0" |
"min_height (Node l _ r) = min (min_height l) (min_height r) + 1"

lemma min_hight_le_height: "min_height t \<le> height t"
by(induction t) auto

lemma min_height_map_tree[simp]: "min_height (map_tree f t) = min_height t"
by (induction t) auto

lemma min_height_le_size1: "2 ^ min_height t \<le> size t + 1"
proof(induction t)
  case (Node l a r)
  have "(2::nat) ^ min_height (Node l a r) \<le> 2 ^ min_height l + 2 ^ min_height r"
    by (simp add: min_def)
  also have "\<dots> \<le> size(Node l a r) + 1" using Node.IH by simp
  finally show ?case .
qed simp


subsection "Balanced"

fun balanced :: "'a tree \<Rightarrow> bool" where
"balanced Leaf = True" |
"balanced (Node l x r) = (balanced l \<and> balanced r \<and> height l = height r)"

lemma balanced_iff_min_height: "balanced t \<longleftrightarrow> (min_height t = height t)"
apply(induction t)
 apply simp
apply (simp add: min_def max_def)
by (metis le_antisym le_trans min_hight_le_height)

lemma balanced_size1: "balanced t \<Longrightarrow> size1 t = 2 ^ height t"
by (induction t) auto

lemma balanced_size: "balanced t \<Longrightarrow> size t = 2 ^ height t - 1"
using balanced_size1[simplified size1_def] by fastforce


subsection \<open>Path length\<close>

text \<open>The internal path length of a tree:\<close>

fun path_len :: "'a tree \<Rightarrow> nat" where
"path_len Leaf = 0 " |
"path_len (Node l _ r) = path_len l + size l + path_len r + size r"

lemma path_len_if_bal: "balanced t
  \<Longrightarrow> path_len t = (let n = height t in 2 + n*2^n - 2^(n+1))"
proof(induction t)
  case (Node l x r)
  have *: "2^(n+1) \<le> 2 + n*2^n" for n :: nat
    by(induction n) auto
  have **: "(0::nat) < 2^n" for n :: nat by simp
  let ?h = "height r"
  show ?case using Node *[of ?h] **[of ?h] by (simp add: balanced_size Let_def)
qed simp


subsection "The set of subtrees"

fun subtrees :: "'a tree \<Rightarrow> 'a tree set" where
"subtrees \<langle>\<rangle> = {\<langle>\<rangle>}" |
"subtrees (\<langle>l, a, r\<rangle>) = insert \<langle>l, a, r\<rangle> (subtrees l \<union> subtrees r)"

lemma set_treeE: "a \<in> set_tree t \<Longrightarrow> \<exists>l r. \<langle>l, a, r\<rangle> \<in> subtrees t"
by (induction t)(auto)

lemma Node_notin_subtrees_if[simp]: "a \<notin> set_tree t \<Longrightarrow> Node l a r \<notin> subtrees t"
by (induction t) auto

lemma in_set_tree_if: "\<langle>l, a, r\<rangle> \<in> subtrees t \<Longrightarrow> a \<in> set_tree t"
by (metis Node_notin_subtrees_if)


subsection "List of entries"

fun preorder :: "'a tree \<Rightarrow> 'a list" where
"preorder \<langle>\<rangle> = []" |
"preorder \<langle>l, x, r\<rangle> = x # preorder l @ preorder r"

fun inorder :: "'a tree \<Rightarrow> 'a list" where
"inorder \<langle>\<rangle> = []" |
"inorder \<langle>l, x, r\<rangle> = inorder l @ [x] @ inorder r"

lemma set_inorder[simp]: "set (inorder t) = set_tree t"
by (induction t) auto

lemma set_preorder[simp]: "set (preorder t) = set_tree t"
by (induction t) auto

lemma length_preorder[simp]: "length (preorder t) = size t"
by (induction t) auto

lemma length_inorder[simp]: "length (inorder t) = size t"
by (induction t) auto

lemma preorder_map: "preorder (map_tree f t) = map f (preorder t)"
by (induction t) auto

lemma inorder_map: "inorder (map_tree f t) = map f (inorder t)"
by (induction t) auto


subsection \<open>Binary Search Tree predicate\<close>

fun (in linorder) bst :: "'a tree \<Rightarrow> bool" where
"bst \<langle>\<rangle> \<longleftrightarrow> True" |
"bst \<langle>l, a, r\<rangle> \<longleftrightarrow> bst l \<and> bst r \<and> (\<forall>x\<in>set_tree l. x < a) \<and> (\<forall>x\<in>set_tree r. a < x)"

text\<open>In case there are duplicates:\<close>

fun (in linorder) bst_eq :: "'a tree \<Rightarrow> bool" where
"bst_eq \<langle>\<rangle> \<longleftrightarrow> True" |
"bst_eq \<langle>l,a,r\<rangle> \<longleftrightarrow>
 bst_eq l \<and> bst_eq r \<and> (\<forall>x\<in>set_tree l. x \<le> a) \<and> (\<forall>x\<in>set_tree r. a \<le> x)"

lemma (in linorder) bst_eq_if_bst: "bst t \<Longrightarrow> bst_eq t"
by (induction t) (auto)

lemma (in linorder) bst_eq_imp_sorted: "bst_eq t \<Longrightarrow> sorted (inorder t)"
apply (induction t)
 apply(simp)
by (fastforce simp: sorted_append sorted_Cons intro: less_imp_le less_trans)

lemma (in linorder) distinct_preorder_if_bst: "bst t \<Longrightarrow> distinct (preorder t)"
apply (induction t)
 apply simp
apply(fastforce elim: order.asym)
done

lemma (in linorder) distinct_inorder_if_bst: "bst t \<Longrightarrow> distinct (inorder t)"
apply (induction t)
 apply simp
apply(fastforce elim: order.asym)
done


subsection "The heap predicate"

fun heap :: "'a::linorder tree \<Rightarrow> bool" where
"heap Leaf = True" |
"heap (Node l m r) =
  (heap l \<and> heap r \<and> (\<forall>x \<in> set_tree l \<union> set_tree r. m \<le> x))"


subsection "Function \<open>mirror\<close>"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror \<langle>\<rangle> = Leaf" |
"mirror \<langle>l,x,r\<rangle> = \<langle>mirror r, x, mirror l\<rangle>"

lemma mirror_Leaf[simp]: "mirror t = \<langle>\<rangle> \<longleftrightarrow> t = \<langle>\<rangle>"
by (induction t) simp_all

lemma size_mirror[simp]: "size(mirror t) = size t"
by (induction t) simp_all

lemma size1_mirror[simp]: "size1(mirror t) = size1 t"
by (simp add: size1_def)

lemma height_mirror[simp]: "height(mirror t) = height t"
by (induction t) simp_all

lemma inorder_mirror: "inorder(mirror t) = rev(inorder t)"
by (induction t) simp_all

lemma map_mirror: "map_tree f (mirror t) = mirror (map_tree f t)"
by (induction t) simp_all

lemma mirror_mirror[simp]: "mirror(mirror t) = t"
by (induction t) simp_all

end
