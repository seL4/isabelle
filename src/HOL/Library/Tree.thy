(* Author: Tobias Nipkow *)
(* Todo:
 (min_)height of balanced trees via floorlog
 minimal path_len of balanced trees
*)

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

fun subtrees :: "'a tree \<Rightarrow> 'a tree set" where
"subtrees \<langle>\<rangle> = {\<langle>\<rangle>}" |
"subtrees (\<langle>l, a, r\<rangle>) = insert \<langle>l, a, r\<rangle> (subtrees l \<union> subtrees r)"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror \<langle>\<rangle> = Leaf" |
"mirror \<langle>l,x,r\<rangle> = \<langle>mirror r, x, mirror l\<rangle>"

class height = fixes height :: "'a \<Rightarrow> nat"

instantiation tree :: (type)height
begin

fun height_tree :: "'a tree => nat" where
"height Leaf = 0" |
"height (Node t1 a t2) = max (height t1) (height t2) + 1"

instance ..

end

fun min_height :: "'a tree \<Rightarrow> nat" where
"min_height Leaf = 0" |
"min_height (Node l _ r) = min (min_height l) (min_height r) + 1"

fun complete :: "'a tree \<Rightarrow> bool" where
"complete Leaf = True" |
"complete (Node l x r) = (complete l \<and> complete r \<and> height l = height r)"

definition balanced :: "'a tree \<Rightarrow> bool" where
"balanced t = (height t - min_height t \<le> 1)"

text \<open>Weight balanced:\<close>
fun wbalanced :: "'a tree \<Rightarrow> bool" where
"wbalanced Leaf = True" |
"wbalanced (Node l x r) = (abs(int(size l) - int(size r)) \<le> 1 \<and> wbalanced l \<and> wbalanced r)"

text \<open>Internal path length:\<close>
fun path_len :: "'a tree \<Rightarrow> nat" where
"path_len Leaf = 0 " |
"path_len (Node l _ r) = path_len l + size l + path_len r + size r"

fun preorder :: "'a tree \<Rightarrow> 'a list" where
"preorder \<langle>\<rangle> = []" |
"preorder \<langle>l, x, r\<rangle> = x # preorder l @ preorder r"

fun inorder :: "'a tree \<Rightarrow> 'a list" where
"inorder \<langle>\<rangle> = []" |
"inorder \<langle>l, x, r\<rangle> = inorder l @ [x] @ inorder r"

text\<open>A linear version avoiding append:\<close>
fun inorder2 :: "'a tree \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"inorder2 \<langle>\<rangle> xs = xs" |
"inorder2 \<langle>l, x, r\<rangle> xs = inorder2 l (x # inorder2 r xs)"

text\<open>Binary Search Tree:\<close>
fun (in linorder) bst :: "'a tree \<Rightarrow> bool" where
"bst \<langle>\<rangle> \<longleftrightarrow> True" |
"bst \<langle>l, a, r\<rangle> \<longleftrightarrow> bst l \<and> bst r \<and> (\<forall>x\<in>set_tree l. x < a) \<and> (\<forall>x\<in>set_tree r. a < x)"

text\<open>Binary Search Tree with duplicates:\<close>
fun (in linorder) bst_eq :: "'a tree \<Rightarrow> bool" where
"bst_eq \<langle>\<rangle> \<longleftrightarrow> True" |
"bst_eq \<langle>l,a,r\<rangle> \<longleftrightarrow>
 bst_eq l \<and> bst_eq r \<and> (\<forall>x\<in>set_tree l. x \<le> a) \<and> (\<forall>x\<in>set_tree r. a \<le> x)"

fun (in linorder) heap :: "'a tree \<Rightarrow> bool" where
"heap Leaf = True" |
"heap (Node l m r) =
  (heap l \<and> heap r \<and> (\<forall>x \<in> set_tree l \<union> set_tree r. m \<le> x))"


subsection \<open>@{const size}\<close>

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


subsection \<open>@{const subtrees}\<close>

lemma set_treeE: "a \<in> set_tree t \<Longrightarrow> \<exists>l r. \<langle>l, a, r\<rangle> \<in> subtrees t"
by (induction t)(auto)

lemma Node_notin_subtrees_if[simp]: "a \<notin> set_tree t \<Longrightarrow> Node l a r \<notin> subtrees t"
by (induction t) auto

lemma in_set_tree_if: "\<langle>l, a, r\<rangle> \<in> subtrees t \<Longrightarrow> a \<in> set_tree t"
by (metis Node_notin_subtrees_if)


subsection \<open>@{const height} and @{const min_height}\<close>

lemma height_0_iff_Leaf: "height t = 0 \<longleftrightarrow> t = Leaf"
by(cases t) auto

lemma height_map_tree[simp]: "height (map_tree f t) = height t"
by (induction t) auto

lemma height_le_size_tree: "height t \<le> size (t::'a tree)"
by (induction t) auto

lemma size1_height: "size1 t \<le> 2 ^ height (t::'a tree)"
proof(induction t)
  case (Node l a r)
  show ?case
  proof (cases "height l \<le> height r")
    case True
    have "size1(Node l a r) = size1 l + size1 r" by simp
    also have "size1 l \<le> 2 ^ height l" by(rule Node.IH(1))
    also have "size1 r \<le> 2 ^ height r" by(rule Node.IH(2))
    also have "(2::nat) ^ height l \<le> 2 ^ height r" using True by simp
    finally show ?thesis using True by (auto simp: max_def mult_2)
  next
    case False
    have "size1(Node l a r) = size1 l + size1 r" by simp
    also have "size1 l \<le> 2 ^ height l" by(rule Node.IH(1))
    also have "size1 r \<le> 2 ^ height r" by(rule Node.IH(2))
    also have "(2::nat) ^ height r \<le> 2 ^ height l" using False by simp
    finally show ?thesis using False by (auto simp: max_def mult_2)
  qed
qed simp

corollary size_height: "size t \<le> 2 ^ height (t::'a tree) - 1"
using size1_height[of t, unfolded size1_def] by(arith)

lemma height_subtrees: "s \<in> subtrees t \<Longrightarrow> height s \<le> height t"
by (induction t) auto


lemma min_height_le_height: "min_height t \<le> height t"
by(induction t) auto

lemma min_height_map_tree[simp]: "min_height (map_tree f t) = min_height t"
by (induction t) auto

lemma min_height_size1: "2 ^ min_height t \<le> size1 t"
proof(induction t)
  case (Node l a r)
  have "(2::nat) ^ min_height (Node l a r) \<le> 2 ^ min_height l + 2 ^ min_height r"
    by (simp add: min_def)
  also have "\<dots> \<le> size1(Node l a r)" using Node.IH by simp
  finally show ?case .
qed simp


subsection \<open>@{const complete}\<close>

lemma complete_iff_height: "complete t \<longleftrightarrow> (min_height t = height t)"
apply(induction t)
 apply simp
apply (simp add: min_def max_def)
by (metis le_antisym le_trans min_height_le_height)

lemma size1_if_complete: "complete t \<Longrightarrow> size1 t = 2 ^ height t"
by (induction t) auto

lemma size_if_complete: "complete t \<Longrightarrow> size t = 2 ^ height t - 1"
using size1_if_complete[simplified size1_def] by fastforce

lemma complete_if_size1_height: "size1 t = 2 ^ height t \<Longrightarrow> complete t"
proof (induct "height t" arbitrary: t)
  case 0 thus ?case by (simp add: height_0_iff_Leaf)
next
  case (Suc h)
  hence "t \<noteq> Leaf" by auto
  then obtain l a r where [simp]: "t = Node l a r"
    by (auto simp: neq_Leaf_iff)
  have 1: "height l \<le> h" and 2: "height r \<le> h" using Suc(2) by(auto)
  have 3: "\<not> height l < h"
  proof
    assume 0: "height l < h"
    have "size1 t = size1 l + size1 r" by simp
    also note size1_height[of l]
    also note size1_height[of r]
    also have "(2::nat) ^ height l < 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also have "(2::nat) ^ height r \<le> 2 ^ h" using 2 by simp
    also have "(2::nat) ^ h  + 2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size1 t" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  have 4: "~ height r < h"
  proof
    assume 0: "height r < h"
    have "size1 t = size1 l + size1 r" by simp
    also note size1_height[of r]
    also note size1_height[of l]
    also have "(2::nat) ^ height r < 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also have "(2::nat) ^ height l \<le> 2 ^ h" using 1 by simp
    also have "(2::nat) ^ h +2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size1 t" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  from 1 2 3 4 have *: "height l = h" "height r = h" by linarith+
  hence "size1 l = 2 ^ height l" "size1 r = 2 ^ height r"
    using Suc(3) size1_height[of l] size1_height[of r] by (auto)
  with * Suc(1) show ?case by simp
qed

text\<open>The following proof involves \<open>\<ge>\<close>/\<open>>\<close> chains rather than the standard
\<open>\<le>\<close>/\<open><\<close> chains. To chain the elements together the transitivity rules \<open>xtrans\<close>
are used.\<close>

lemma complete_if_size1_min_height: "size1 t = 2 ^ min_height t \<Longrightarrow> complete t"
proof (induct "min_height t" arbitrary: t)
  case 0 thus ?case by (simp add: size_0_iff_Leaf size1_def)
next
  case (Suc h)
  hence "t \<noteq> Leaf" by auto
  then obtain l a r where [simp]: "t = Node l a r"
    by (auto simp: neq_Leaf_iff)
  have 1: "h \<le> min_height l" and 2: "h \<le> min_height r" using Suc(2) by(auto)
  have 3: "\<not> h < min_height l"
  proof
    assume 0: "h < min_height l"
    have "size1 t = size1 l + size1 r" by simp
    also note min_height_size1[of l]
    also(xtrans) note min_height_size1[of r]
    also(xtrans) have "(2::nat) ^ min_height l > 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also(xtrans) have "(2::nat) ^ min_height r \<ge> 2 ^ h" using 2 by simp
    also(xtrans) have "(2::nat) ^ h + 2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size1 t" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  have 4: "\<not> h < min_height r"
  proof
    assume 0: "h < min_height r"
    have "size1 t = size1 l + size1 r" by simp
    also note min_height_size1[of l]
    also(xtrans) note min_height_size1[of r]
    also(xtrans) have "(2::nat) ^ min_height r > 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also(xtrans) have "(2::nat) ^ min_height l \<ge> 2 ^ h" using 1 by simp
    also(xtrans) have "(2::nat) ^ h + 2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size1 t" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  from 1 2 3 4 have *: "min_height l = h" "min_height r = h" by linarith+
  hence "size1 l = 2 ^ min_height l" "size1 r = 2 ^ min_height r"
    using Suc(3) min_height_size1[of l] min_height_size1[of r] by (auto)
  with * Suc(1) show ?case
    by (simp add: complete_iff_height)
qed

lemma complete_iff_size1: "complete t \<longleftrightarrow> size1 t = 2 ^ height t"
using complete_if_size1_height size1_if_complete by blast

text\<open>Better bounds for incomplete trees:\<close>

lemma size1_height_if_incomplete:
  "\<not> complete t \<Longrightarrow> size1 t < 2 ^ height t"
by (meson antisym_conv complete_iff_size1 not_le size1_height)

lemma min_height_size1_if_incomplete:
  "\<not> complete t \<Longrightarrow> 2 ^ min_height t < size1 t"
by (metis complete_if_size1_min_height le_less min_height_size1)


subsection \<open>@{const balanced}\<close>

lemma balanced_subtreeL: "balanced (Node l x r) \<Longrightarrow> balanced l"
by(simp add: balanced_def)

lemma balanced_subtreeR: "balanced (Node l x r) \<Longrightarrow> balanced r"
by(simp add: balanced_def)

lemma balanced_subtrees: "\<lbrakk> balanced t; s \<in> subtrees t \<rbrakk> \<Longrightarrow> balanced s"
using [[simp_depth_limit=1]]
by(induction t arbitrary: s)
  (auto simp add: balanced_subtreeL balanced_subtreeR)

text\<open>Balanced trees have optimal height:\<close>

lemma balanced_optimal:
fixes t :: "'a tree" and t' :: "'b tree"
assumes "balanced t" "size t \<le> size t'" shows "height t \<le> height t'"
proof (cases "complete t")
  case True
  have "(2::nat) ^ height t - 1 \<le> 2 ^ height t' - 1"
  proof -
    have "(2::nat) ^ height t - 1 = size t"
      using True by (simp add: complete_iff_height size_if_complete)
    also note assms(2)
    also have "size t' \<le> 2 ^ height t' - 1" by (rule size_height)
    finally show ?thesis .
  qed
  thus ?thesis by (simp add: le_diff_iff)
next
  case False
  have "(2::nat) ^ min_height t < 2 ^ height t'"
  proof -
    have "(2::nat) ^ min_height t < size1 t"
      by(rule min_height_size1_if_incomplete[OF False])
    also have "size1 t \<le> size1 t'" using assms(2) by (simp add: size1_def)
    also have "size1 t' \<le> 2 ^ height t'"  by(rule size1_height)
    finally show ?thesis
      using power_eq_0_iff[of "2::nat" "height t'"] by linarith
  qed
  hence *: "min_height t < height t'" by simp
  have "min_height t + 1 = height t"
    using min_height_le_height[of t] assms(1) False
    by (simp add: complete_iff_height balanced_def)
  with * show ?thesis by arith
qed


subsection \<open>@{const wbalanced}\<close>

lemma wbalanced_subtrees: "\<lbrakk> wbalanced t; s \<in> subtrees t \<rbrakk> \<Longrightarrow> wbalanced s"
using [[simp_depth_limit=1]] by(induction t arbitrary: s) auto


subsection \<open>@{const path_len}\<close>

text \<open>The internal path length of a tree:\<close>

lemma path_len_if_bal: "complete t
  \<Longrightarrow> path_len t = (let n = height t in 2 + n*2^n - 2^(n+1))"
proof(induction t)
  case (Node l x r)
  have *: "2^(n+1) \<le> 2 + n*2^n" for n :: nat
    by(induction n) auto
  have **: "(0::nat) < 2^n" for n :: nat by simp
  let ?h = "height r"
  show ?case using Node *[of ?h] **[of ?h] by (simp add: size_if_complete Let_def)
qed simp


subsection "List of entries"

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

lemma inorder2_inorder: "inorder2 t xs = inorder t @ xs"
by (induction t arbitrary: xs) auto


subsection \<open>Binary Search Tree\<close>

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


subsection \<open>@{const heap}\<close>


subsection \<open>@{const mirror}\<close>

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
