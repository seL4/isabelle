(* Author: Tobias Nipkow *)

theory Leftist_Heap_List
imports
  Leftist_Heap
  Complex_Main
begin

subsection "Converting a list into a leftist heap"

fun merge_adj :: "('a::ord) lheap list \<Rightarrow> 'a lheap list" where
"merge_adj [] = []" |
"merge_adj [t] = [t]" |
"merge_adj (t1 # t2 # ts) = merge t1 t2 # merge_adj ts"

text \<open>For the termination proof of \<open>merge_all\<close> below.\<close>
lemma length_merge_adjacent[simp]: "length (merge_adj ts) = (length ts + 1) div 2"
by (induction ts rule: merge_adj.induct) auto

fun merge_all :: "('a::ord) lheap list \<Rightarrow> 'a lheap" where
"merge_all [] = Leaf" |
"merge_all [t] = t" |
"merge_all ts = merge_all (merge_adj ts)"


subsubsection \<open>Functional correctness\<close>

lemma heap_merge_adj: "\<forall>t \<in> set ts. heap t \<Longrightarrow> \<forall>t \<in> set (merge_adj ts). heap t"
by(induction ts rule: merge_adj.induct) (auto simp: heap_merge)

lemma ltree_merge_adj: "\<forall>t \<in> set ts. ltree t \<Longrightarrow> \<forall>t \<in> set (merge_adj ts). ltree t"
by(induction ts rule: merge_adj.induct) (auto simp: ltree_merge)

lemma heap_merge_all: "\<forall>t \<in> set ts. heap t \<Longrightarrow> heap (merge_all ts)"
apply(induction ts rule: merge_all.induct)
using [[simp_depth_limit=3]] by (auto simp add: heap_merge_adj)

lemma ltree_merge_all: "\<forall>t \<in> set ts. ltree t \<Longrightarrow> ltree (merge_all ts)"
apply(induction ts rule: merge_all.induct)
using [[simp_depth_limit=3]] by (auto simp add: ltree_merge_adj)

lemma mset_merge_adj:
  "\<Sum>\<^sub># (image_mset mset_tree (mset (merge_adj ts))) =
   \<Sum>\<^sub># (image_mset mset_tree (mset ts))"
by(induction ts rule: merge_adj.induct) (auto simp: mset_merge)

lemma mset_merge_all:
  "mset_tree (merge_all ts) = \<Sum>\<^sub># (mset (map mset_tree ts))"
by(induction ts rule: merge_all.induct) (auto simp: mset_merge mset_merge_adj)

fun lheap_list :: "'a::ord list \<Rightarrow> 'a lheap" where
"lheap_list xs = merge_all (map (\<lambda>x. Node Leaf (x,1) Leaf) xs)"

lemma mset_lheap_list: "mset_tree (lheap_list xs) = mset xs"
by (simp add: mset_merge_all o_def)

lemma ltree_lheap_list: "ltree (lheap_list ts)"
by(simp add: ltree_merge_all)

lemma heap_lheap_list: "heap (lheap_list ts)"
by(simp add: heap_merge_all)

lemma size_merge: "size(merge t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: merge.induct) (auto simp: node_def)


subsubsection \<open>Running time\<close>

text \<open>Not defined automatically because we only count the time for @{const merge}.\<close>

fun T_merge_adj :: "('a::ord) lheap list \<Rightarrow> nat" where
"T_merge_adj [] = 0" |
"T_merge_adj [t] = 0" |
"T_merge_adj (t1 # t2 # ts) = T_merge t1 t2 + T_merge_adj ts"

fun T_merge_all :: "('a::ord) lheap list  \<Rightarrow> nat" where
"T_merge_all [] = 0" |
"T_merge_all [t] = 0" |
"T_merge_all ts = T_merge_adj ts + T_merge_all (merge_adj ts)"

fun T_lheap_list :: "'a::ord list \<Rightarrow> nat" where
"T_lheap_list xs = T_merge_all (map (\<lambda>x. Node Leaf (x,1) Leaf) xs)"

abbreviation Tm where
"Tm n == 2 * log 2 (n+1) + 1"

lemma T_merge_adj: "\<lbrakk> \<forall>t \<in> set ts. ltree t; \<forall>t \<in> set ts. size t = n \<rbrakk>
  \<Longrightarrow> T_merge_adj ts \<le> (length ts div 2) * Tm n"
proof(induction ts rule: T_merge_adj.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 t1 t2) thus ?case using T_merge_log[of t1 t2] by (simp add: algebra_simps size1_size)
qed

lemma size_merge_adj:
  "\<lbrakk> even(length ts); \<forall>t \<in> set ts. ltree t; \<forall>t \<in> set ts. size t = n \<rbrakk>
   \<Longrightarrow> \<forall>t \<in> set (merge_adj ts). size t = 2*n"
by(induction ts rule: merge_adj.induct) (auto simp: size_merge)

lemma T_merge_all:
 "\<lbrakk> \<forall>t \<in> set ts. ltree t; \<forall>t \<in> set ts. size t = n; length ts = 2^k \<rbrakk>
  \<Longrightarrow> T_merge_all ts \<le> (\<Sum>i=1..k. 2^(k-i) * Tm(2 ^ (i-1) * n))"
proof (induction ts arbitrary: k n rule: merge_all.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 t1 t2 ts)
  let ?ts = "t1 # t2 # ts"
  let ?ts2 = "merge_adj ?ts"
  obtain k' where k': "k = Suc k'" using "3.prems"(3)
    by (metis length_Cons nat.inject nat_power_eq_Suc_0_iff nat.exhaust)
  have 1: "\<forall>x \<in> set(merge_adj ?ts). ltree x"
    by(rule ltree_merge_adj[OF "3.prems"(1)])
  have "even (length ts)" using "3.prems"(3) even_Suc_Suc_iff by fastforce
  from "3.prems"(2) size_merge_adj[OF this] "3.prems"(1)
  have 2: "\<forall>x \<in> set(merge_adj ?ts). size x = 2*n" by(auto simp: size_merge)
  have 3: "length ?ts2 = 2 ^ k'" using "3.prems"(3) k' by auto
  have 4: "length ?ts div 2 = 2 ^ k'"
    using "3.prems"(3) k' by(simp add: power_eq_if[of 2 k] split: if_splits)
  have "T_merge_all ?ts = T_merge_adj ?ts + T_merge_all ?ts2" by simp
  also have "\<dots> \<le> 2^k' * Tm n + T_merge_all ?ts2"
    using 4 T_merge_adj[OF "3.prems"(1,2)] by auto
  also have "\<dots> \<le> 2^k' * Tm n + (\<Sum>i=1..k'. 2^(k'-i) * Tm(2 ^ (i-1) * (2*n)))"
    using "3.IH"[OF 1 2 3] by simp
  also have "\<dots> = 2^k' * Tm n + (\<Sum>i=1..k'. 2^(k'-i) * Tm(2 ^ (Suc(i-1)) * n))"
    by (simp add: mult_ac cong del: sum.cong)
  also have "\<dots> = 2^k' * Tm n + (\<Sum>i=1..k'. 2^(k'-i) * Tm(2 ^ i * n))"
     by (simp)
  also have "\<dots> = (\<Sum>i=1..k. 2^(k-i) * Tm(2 ^ (i-1) * real n))"
    by(simp add: sum.atLeast_Suc_atMost[of "Suc 0" "Suc k'"] sum.atLeast_Suc_atMost_Suc_shift[of _ "Suc 0"] k'
        del: sum.cl_ivl_Suc)
  finally show ?case .
qed

lemma summation: "(\<Sum>i=1..k. 2^(k-i) * ((2::real)*i+1)) = 5*2^k - (2::real)*k - 5"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have "(\<Sum>i=1..Suc k. 2^(Suc k - i) * ((2::real)*i+1))
    = (\<Sum>i=1..k. 2^(k+1-i) * ((2::real)*i+1)) + 2*k+3"
    by(simp)
  also have "\<dots> = (\<Sum>i=1..k. (2::real)*(2^(k-i) * ((2::real)*i+1))) + 2*k+3"
    by (simp add: Suc_diff_le mult.assoc)
  also have "\<dots> = 2*(\<Sum>i=1..k. 2^(k-i) * ((2::real)*i+1)) + 2*k+3"
    by(simp add: sum_distrib_left)
  also have "\<dots> = (2::real)*(5*2^k - (2::real)*k - 5) + 2*k+3"
    using Suc.IH by simp
  also have "\<dots> = 5*2^(Suc k) - (2::real)*(Suc k) - 5"
    by simp
  finally show ?case .
qed

lemma T_lheap_list: assumes "length xs = 2 ^ k"
shows "T_lheap_list xs \<le> 5 * length xs - 2 * log 2 (length xs)"
proof -
  let ?ts = "map (\<lambda>x. Node Leaf (x,1) Leaf) xs"
  have "T_lheap_list xs = T_merge_all ?ts" by simp
  also have "\<dots> \<le> (\<Sum>i = 1..k. 2^(k-i) * (2 * log 2 (2^(i-1) + 1) + 1))"
    using T_merge_all[of ?ts 1 k] assms by (simp)
  also have "\<dots> \<le> (\<Sum>i = 1..k. 2^(k-i) * (2 * log 2 (2*2^(i-1)) + 1))"
    apply(rule sum_mono)
    using zero_le_power[of "2::real"] by (simp add: add_pos_nonneg)
  also have "\<dots> = (\<Sum>i = 1..k. 2^(k-i) * (2 * log 2 (2^(1+(i-1))) + 1))"
    by (simp del: Suc_pred)
  also have "\<dots> = (\<Sum>i = 1..k. 2^(k-i) * (2 * log 2 (2^i) + 1))"
    by (simp)
  also have "\<dots> = (\<Sum>i = 1..k. 2^(k-i) * ((2::real)*i+1))"
    by (simp add:log_nat_power algebra_simps)
  also have "\<dots> = 5*(2::real)^k - (2::real)*k - 5"
    using summation by (simp)
  finally show ?thesis
    using assms of_nat_le_iff by simp
qed

end