(* Author: Tobias Nipkow *)

section \<open>Leftist Heap\<close>

theory Leftist_Heap
imports
  "HOL-Library.Pattern_Aliases"
  Tree2
  Priority_Queue_Specs
  Complex_Main
begin

fun mset_tree :: "('a*'b) tree \<Rightarrow> 'a multiset" where
"mset_tree Leaf = {#}" |
"mset_tree (Node l (a, _) r) = {#a#} + mset_tree l + mset_tree r"

type_synonym 'a lheap = "('a*nat)tree"

fun mht :: "'a lheap \<Rightarrow> nat" where
"mht Leaf = 0" |
"mht (Node _ (_, n) _) = n"

text\<open>The invariants:\<close>

fun (in linorder) heap :: "('a*'b) tree \<Rightarrow> bool" where
"heap Leaf = True" |
"heap (Node l (m, _) r) =
  ((\<forall>x \<in> set_tree l \<union> set_tree r. m \<le> x) \<and> heap l \<and> heap r)"

fun ltree :: "'a lheap \<Rightarrow> bool" where
"ltree Leaf = True" |
"ltree (Node l (a, n) r) =
 (min_height l \<ge> min_height r \<and> n = min_height r + 1 \<and> ltree l & ltree r)"

definition empty :: "'a lheap" where
"empty = Leaf"

definition node :: "'a lheap \<Rightarrow> 'a \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"node l a r =
 (let mhl = mht l; mhr = mht r
  in if mhl \<ge> mhr then Node l (a,mhr+1) r else Node r (a,mhl+1) l)"

fun get_min :: "'a lheap \<Rightarrow> 'a" where
"get_min(Node l (a, n) r) = a"

text \<open>For function \<open>merge\<close>:\<close>
unbundle pattern_aliases

fun merge :: "'a::ord lheap \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"merge Leaf t = t" |
"merge t Leaf = t" |
"merge (Node l1 (a1, n1) r1 =: t1) (Node l2 (a2, n2) r2 =: t2) =
   (if a1 \<le> a2 then node l1 a1 (merge r1 t2)
    else node l2 a2 (merge t1 r2))"

text \<open>Termination of @{const merge}: by sum or lexicographic product of the sizes
of the two arguments. Isabelle uses a lexicographic product.\<close>

lemma merge_code: "merge t1 t2 = (case (t1,t2) of
  (Leaf, _) \<Rightarrow> t2 |
  (_, Leaf) \<Rightarrow> t1 |
  (Node l1 (a1, n1) r1, Node l2 (a2, n2) r2) \<Rightarrow>
    if a1 \<le> a2 then node l1 a1 (merge r1 t2) else node l2 a2 (merge t1 r2))"
by(induction t1 t2 rule: merge.induct) (simp_all split: tree.split)

hide_const (open) insert

definition insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"insert x t = merge (Node Leaf (x,1) Leaf) t"

fun del_min :: "'a::ord lheap \<Rightarrow> 'a lheap" where
"del_min Leaf = Leaf" |
"del_min (Node l _ r) = merge l r"


subsection "Lemmas"

lemma mset_tree_empty: "mset_tree t = {#} \<longleftrightarrow> t = Leaf"
by(cases t) auto

lemma mht_eq_min_height: "ltree t \<Longrightarrow> mht t = min_height t"
by(cases t) auto

lemma ltree_node: "ltree (node l a r) \<longleftrightarrow> ltree l \<and> ltree r"
by(auto simp add: node_def mht_eq_min_height)

lemma heap_node: "heap (node l a r) \<longleftrightarrow>
  heap l \<and> heap r \<and> (\<forall>x \<in> set_tree l \<union> set_tree r. a \<le> x)"
by(auto simp add: node_def)

lemma set_tree_mset: "set_tree t = set_mset(mset_tree t)"
by(induction t) auto

subsection "Functional Correctness"

lemma mset_merge: "mset_tree (merge t1 t2) = mset_tree t1 + mset_tree t2"
by (induction t1 t2 rule: merge.induct) (auto simp add: node_def ac_simps)

lemma mset_insert: "mset_tree (insert x t) = mset_tree t + {#x#}"
by (auto simp add: insert_def mset_merge)

lemma get_min: "\<lbrakk> heap t;  t \<noteq> Leaf \<rbrakk> \<Longrightarrow> get_min t = Min(set_tree t)"
by (cases t) (auto simp add: eq_Min_iff)

lemma mset_del_min: "mset_tree (del_min t) = mset_tree t - {# get_min t #}"
by (cases t) (auto simp: mset_merge)

lemma ltree_merge: "\<lbrakk> ltree l; ltree r \<rbrakk> \<Longrightarrow> ltree (merge l r)"
by(induction l r rule: merge.induct)(auto simp: ltree_node)

lemma heap_merge: "\<lbrakk> heap l; heap r \<rbrakk> \<Longrightarrow> heap (merge l r)"
proof(induction l r rule: merge.induct)
  case 3 thus ?case by(auto simp: heap_node mset_merge ball_Un set_tree_mset)
qed simp_all

lemma ltree_insert: "ltree t \<Longrightarrow> ltree(insert x t)"
by(simp add: insert_def ltree_merge del: merge.simps split: tree.split)

lemma heap_insert: "heap t \<Longrightarrow> heap(insert x t)"
by(simp add: insert_def heap_merge del: merge.simps split: tree.split)

lemma ltree_del_min: "ltree t \<Longrightarrow> ltree(del_min t)"
by(cases t)(auto simp add: ltree_merge simp del: merge.simps)

lemma heap_del_min: "heap t \<Longrightarrow> heap(del_min t)"
by(cases t)(auto simp add: heap_merge simp del: merge.simps)

text \<open>Last step of functional correctness proof: combine all the above lemmas
to show that leftist heaps satisfy the specification of priority queues with merge.\<close>

interpretation lheap: Priority_Queue_Merge
where empty = empty and is_empty = "\<lambda>t. t = Leaf"
and insert = insert and del_min = del_min
and get_min = get_min and merge = merge
and invar = "\<lambda>t. heap t \<and> ltree t" and mset = mset_tree
proof(standard, goal_cases)
  case 1 show ?case by (simp add: empty_def)
next
  case (2 q) show ?case by (cases q) auto
next
  case 3 show ?case by(rule mset_insert)
next
  case 4 show ?case by(rule mset_del_min)
next
  case 5 thus ?case by(simp add: get_min mset_tree_empty set_tree_mset)
next
  case 6 thus ?case by(simp add: empty_def)
next
  case 7 thus ?case by(simp add: heap_insert ltree_insert)
next
  case 8 thus ?case by(simp add: heap_del_min ltree_del_min)
next
  case 9 thus ?case by (simp add: mset_merge)
next
  case 10 thus ?case by (simp add: heap_merge ltree_merge)
qed


subsection "Complexity"

text\<open>Explicit termination argument: sum of sizes\<close>

fun T_merge :: "'a::ord lheap \<Rightarrow> 'a lheap \<Rightarrow> nat" where
"T_merge Leaf t = 1" |
"T_merge t Leaf = 1" |
"T_merge (Node l1 (a1, n1) r1 =: t1) (Node l2 (a2, n2) r2 =: t2) =
  (if a1 \<le> a2 then T_merge r1 t2
   else T_merge t1 r2) + 1"

definition T_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> nat" where
"T_insert x t = T_merge (Node Leaf (x, 1) Leaf) t + 1"

fun T_del_min :: "'a::ord lheap \<Rightarrow> nat" where
"T_del_min Leaf = 1" |
"T_del_min (Node l _ r) = T_merge l r + 1"

lemma T_merge_min_height: "ltree l \<Longrightarrow> ltree r \<Longrightarrow> T_merge l r \<le> min_height l + min_height r + 1"
proof(induction l r rule: merge.induct)
  case 3 thus ?case by(auto)
qed simp_all

corollary T_merge_log: assumes "ltree l" "ltree r"
  shows "T_merge l r \<le> log 2 (size1 l) + log 2 (size1 r) + 1"
using le_log2_of_power[OF min_height_size1[of l]]
  le_log2_of_power[OF min_height_size1[of r]] T_merge_min_height[of l r] assms
by linarith

corollary T_insert_log: "ltree t \<Longrightarrow> T_insert x t \<le> log 2 (size1 t) + 3"
using T_merge_log[of "Node Leaf (x, 1) Leaf" t]
by(simp add: T_insert_def split: tree.split)

(* FIXME mv ? *)
lemma ld_ld_1_less:
  assumes "x > 0" "y > 0" shows "log 2 x + log 2 y + 1 < 2 * log 2 (x+y)"
proof -
  have "2 powr (log 2 x + log 2 y + 1) = 2*x*y"
    using assms by(simp add: powr_add)
  also have "\<dots> < (x+y)^2" using assms
    by(simp add: numeral_eq_Suc algebra_simps add_pos_pos)
  also have "\<dots> = 2 powr (2 * log 2 (x+y))"
    using assms by(simp add: powr_add log_powr[symmetric])
  finally show ?thesis by simp
qed

corollary T_del_min_log: assumes "ltree t"
  shows "T_del_min t \<le> 2 * log 2 (size1 t) + 1"
proof(cases t rule: tree2_cases)
  case Leaf thus ?thesis using assms by simp
next
  case [simp]: (Node l _ _ r)
  have "T_del_min t = T_merge l r + 1" by simp
  also have "\<dots> \<le> log 2 (size1 l) + log 2 (size1 r) + 2"
    using \<open>ltree t\<close> T_merge_log[of l r] by (auto simp del: T_merge.simps)
  also have "\<dots> \<le> 2 * log 2 (size1 t) + 1"
    using ld_ld_1_less[of "size1 l" "size1 r"] by (simp)
  finally show ?thesis .
qed

end
