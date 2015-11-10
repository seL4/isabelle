(* Author: Tobias Nipkow *)

section \<open>Binary Tree\<close>

theory Tree
imports Main
begin

datatype 'a tree =
  Leaf ("\<langle>\<rangle>") |
  Node (left: "'a tree") (val: 'a) (right: "'a tree") ("\<langle>_, _, _\<rangle>")
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
