(* Author: Tobias Nipkow *)

section \<open>Leftist Heap\<close>

theory Leftist_Heap
imports
  Base_FDS
  Tree2
  Priority_Queue
  Complex_Main
begin

fun mset_tree :: "('a,'b) tree \<Rightarrow> 'a multiset" where
"mset_tree Leaf = {#}" |
"mset_tree (Node _ l a r) = {#a#} + mset_tree l + mset_tree r"

type_synonym 'a lheap = "('a,nat)tree"

fun rank :: "'a lheap \<Rightarrow> nat" where
"rank Leaf = 0" |
"rank (Node _ _ _ r) = rank r + 1"

fun rk :: "'a lheap \<Rightarrow> nat" where
"rk Leaf = 0" |
"rk (Node n _ _ _) = n"

text\<open>The invariants:\<close>

fun (in linorder) heap :: "('a,'b) tree \<Rightarrow> bool" where
"heap Leaf = True" |
"heap (Node _ l m r) =
  (heap l \<and> heap r \<and> (\<forall>x \<in> set_mset(mset_tree l + mset_tree r). m \<le> x))"

fun ltree :: "'a lheap \<Rightarrow> bool" where
"ltree Leaf = True" |
"ltree (Node n l a r) =
 (n = rank r + 1 \<and> rank l \<ge> rank r \<and> ltree l & ltree r)"

definition node :: "'a lheap \<Rightarrow> 'a \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"node l a r =
 (let rl = rk l; rr = rk r
  in if rl \<ge> rr then Node (rr+1) l a r else Node (rl+1) r a l)"

fun get_min :: "'a lheap \<Rightarrow> 'a" where
"get_min(Node n l a r) = a"

text \<open>For function \<open>merge\<close>:\<close>
unbundle pattern_aliases
declare size_prod_measure[measure_function]

fun merge :: "'a::ord lheap \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"merge Leaf t2 = t2" |
"merge t1 Leaf = t1" |
"merge (Node n1 l1 a1 r1 =: t1) (Node n2 l2 a2 r2 =: t2) =
   (if a1 \<le> a2 then node l1 a1 (merge r1 t2)
    else node l2 a2 (merge r2 t1))"

lemma merge_code: "merge t1 t2 = (case (t1,t2) of
  (Leaf, _) \<Rightarrow> t2 |
  (_, Leaf) \<Rightarrow> t1 |
  (Node n1 l1 a1 r1, Node n2 l2 a2 r2) \<Rightarrow>
    if a1 \<le> a2 then node l1 a1 (merge r1 t2) else node l2 a2 (merge r2 t1))"
by(induction t1 t2 rule: merge.induct) (simp_all split: tree.split)

hide_const (open) insert

definition insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"insert x t = merge (Node 1 Leaf x Leaf) t"

fun split_min :: "'a::ord lheap \<Rightarrow> 'a lheap" where
"split_min Leaf = Leaf" |
"split_min (Node n l x r) = merge l r"


subsection "Lemmas"

lemma mset_tree_empty: "mset_tree t = {#} \<longleftrightarrow> t = Leaf"
by(cases t) auto

lemma rk_eq_rank[simp]: "ltree t \<Longrightarrow> rk t = rank t"
by(cases t) auto

lemma ltree_node: "ltree (node l a r) \<longleftrightarrow> ltree l \<and> ltree r"
by(auto simp add: node_def)

lemma heap_node: "heap (node l a r) \<longleftrightarrow>
  heap l \<and> heap r \<and> (\<forall>x \<in> set_mset(mset_tree l + mset_tree r). a \<le> x)"
by(auto simp add: node_def)


subsection "Functional Correctness"

lemma mset_merge: "mset_tree (merge h1 h2) = mset_tree h1 + mset_tree h2"
by (induction h1 h2 rule: merge.induct) (auto simp add: node_def ac_simps)

lemma mset_insert: "mset_tree (insert x t) = mset_tree t + {#x#}"
by (auto simp add: insert_def mset_merge)

lemma get_min: "\<lbrakk> heap h;  h \<noteq> Leaf \<rbrakk> \<Longrightarrow> get_min h = Min_mset (mset_tree h)"
by (induction h) (auto simp add: eq_Min_iff)

lemma mset_split_min: "mset_tree (split_min h) = mset_tree h - {# get_min h #}"
by (cases h) (auto simp: mset_merge)

lemma ltree_merge: "\<lbrakk> ltree l; ltree r \<rbrakk> \<Longrightarrow> ltree (merge l r)"
proof(induction l r rule: merge.induct)
  case (3 n1 l1 a1 r1 n2 l2 a2 r2)
  show ?case (is "ltree(merge ?t1 ?t2)")
  proof cases
    assume "a1 \<le> a2"
    hence "ltree (merge ?t1 ?t2) = ltree (node l1 a1 (merge r1 ?t2))" by simp
    also have "\<dots> = (ltree l1 \<and> ltree(merge r1 ?t2))"
      by(simp add: ltree_node)
    also have "..." using "3.prems" "3.IH"(1)[OF \<open>a1 \<le> a2\<close>] by (simp)
    finally show ?thesis .
  next (* analogous but automatic *)
    assume "\<not> a1 \<le> a2"
    thus ?thesis using 3 by(simp)(auto simp: ltree_node)
  qed
qed simp_all

lemma heap_merge: "\<lbrakk> heap l; heap r \<rbrakk> \<Longrightarrow> heap (merge l r)"
proof(induction l r rule: merge.induct)
  case 3 thus ?case by(auto simp: heap_node mset_merge ball_Un)
qed simp_all

lemma ltree_insert: "ltree t \<Longrightarrow> ltree(insert x t)"
by(simp add: insert_def ltree_merge del: merge.simps split: tree.split)

lemma heap_insert: "heap t \<Longrightarrow> heap(insert x t)"
by(simp add: insert_def heap_merge del: merge.simps split: tree.split)

lemma ltree_split_min: "ltree t \<Longrightarrow> ltree(split_min t)"
by(cases t)(auto simp add: ltree_merge simp del: merge.simps)

lemma heap_split_min: "heap t \<Longrightarrow> heap(split_min t)"
by(cases t)(auto simp add: heap_merge simp del: merge.simps)

text \<open>Last step of functional correctness proof: combine all the above lemmas
to show that leftist heaps satisfy the specification of priority queues with merge.\<close>

interpretation lheap: Priority_Queue_Merge
where empty = Leaf and is_empty = "\<lambda>h. h = Leaf"
and insert = insert and split_min = split_min
and get_min = get_min and merge = merge
and invar = "\<lambda>h. heap h \<and> ltree h" and mset = mset_tree
proof(standard, goal_cases)
  case 1 show ?case by simp
next
  case (2 q) show ?case by (cases q) auto
next
  case 3 show ?case by(rule mset_insert)
next
  case 4 show ?case by(rule mset_split_min)
next
  case 5 thus ?case by(simp add: get_min mset_tree_empty)
next
  case 6 thus ?case by(simp)
next
  case 7 thus ?case by(simp add: heap_insert ltree_insert)
next
  case 8 thus ?case by(simp add: heap_split_min ltree_split_min)
next
  case 9 thus ?case by (simp add: mset_merge)
next
  case 10 thus ?case by (simp add: heap_merge ltree_merge)
qed


subsection "Complexity"

lemma pow2_rank_size1: "ltree t \<Longrightarrow> 2 ^ rank t \<le> size1 t"
proof(induction t)
  case Leaf show ?case by simp
next
  case (Node n l a r)
  hence "rank r \<le> rank l" by simp
  hence *: "(2::nat) ^ rank r \<le> 2 ^ rank l" by simp
  have "(2::nat) ^ rank \<langle>n, l, a, r\<rangle> = 2 ^ rank r + 2 ^ rank r"
    by(simp add: mult_2)
  also have "\<dots> \<le> size1 l + size1 r"
    using Node * by (simp del: power_increasing_iff)
  also have "\<dots> = size1 \<langle>n, l, a, r\<rangle>" by simp
  finally show ?case .
qed

text\<open>Explicit termination argument: sum of sizes\<close>

fun t_merge :: "'a::ord lheap \<Rightarrow> 'a lheap \<Rightarrow> nat" where
"t_merge Leaf t2 = 1" |
"t_merge t2 Leaf = 1" |
"t_merge (Node n1 l1 a1 r1 =: t1) (Node n2 l2 a2 r2 =: t2) =
  (if a1 \<le> a2 then 1 + t_merge r1 t2
   else 1 + t_merge r2 t1)"

definition t_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> nat" where
"t_insert x t = t_merge (Node 1 Leaf x Leaf) t"

fun t_split_min :: "'a::ord lheap \<Rightarrow> nat" where
"t_split_min Leaf = 1" |
"t_split_min (Node n l a r) = t_merge l r"

lemma t_merge_rank: "t_merge l r \<le> rank l + rank r + 1"
proof(induction l r rule: merge.induct)
  case 3 thus ?case
    by(simp)(fastforce split: tree.splits simp del: t_merge.simps)
qed simp_all

corollary t_merge_log: assumes "ltree l" "ltree r"
  shows "t_merge l r \<le> log 2 (size1 l) + log 2 (size1 r) + 1"
using le_log2_of_power[OF pow2_rank_size1[OF assms(1)]]
  le_log2_of_power[OF pow2_rank_size1[OF assms(2)]] t_merge_rank[of l r]
by linarith

corollary t_insert_log: "ltree t \<Longrightarrow> t_insert x t \<le> log 2 (size1 t) + 2"
using t_merge_log[of "Node 1 Leaf x Leaf" t]
by(simp add: t_insert_def split: tree.split)

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

corollary t_split_min_log: assumes "ltree t"
  shows "t_split_min t \<le> 2 * log 2 (size1 t) + 1"
proof(cases t)
  case Leaf thus ?thesis using assms by simp
next
  case [simp]: (Node _ t1 _ t2)
  have "t_split_min t = t_merge t1 t2" by simp
  also have "\<dots> \<le> log 2 (size1 t1) + log 2 (size1 t2) + 1"
    using \<open>ltree t\<close> by (auto simp: t_merge_log simp del: t_merge.simps)
  also have "\<dots> \<le> 2 * log 2 (size1 t) + 1"
    using ld_ld_1_less[of "size1 t1" "size1 t2"] by (simp)
  finally show ?thesis .
qed

end
