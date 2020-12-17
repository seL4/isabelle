(* Author: Peter Lammich
           Tobias Nipkow (tuning)
*)

section \<open>Binomial Heap\<close>

theory Binomial_Heap
imports
  "HOL-Library.Pattern_Aliases"
  Complex_Main
  Priority_Queue_Specs
begin

text \<open>
  We formalize the binomial heap presentation from Okasaki's book.
  We show the functional correctness and complexity of all operations.

  The presentation is engineered for simplicity, and most
  proofs are straightforward and automatic.
\<close>

subsection \<open>Binomial Tree and Heap Datatype\<close>

datatype 'a tree = Node (rank: nat) (root: 'a) (children: "'a tree list")

type_synonym 'a heap = "'a tree list"

subsubsection \<open>Multiset of elements\<close>

fun mset_tree :: "'a::linorder tree \<Rightarrow> 'a multiset" where
  "mset_tree (Node _ a ts) = {#a#} + (\<Sum>t\<in>#mset ts. mset_tree t)"

definition mset_heap :: "'a::linorder heap \<Rightarrow> 'a multiset" where
  "mset_heap ts = (\<Sum>t\<in>#mset ts. mset_tree t)"

lemma mset_tree_simp_alt[simp]:
  "mset_tree (Node r a ts) = {#a#} + mset_heap ts"
  unfolding mset_heap_def by auto
declare mset_tree.simps[simp del]

lemma mset_tree_nonempty[simp]: "mset_tree t \<noteq> {#}"
by (cases t) auto

lemma mset_heap_Nil[simp]:
  "mset_heap [] = {#}"
by (auto simp: mset_heap_def)

lemma mset_heap_Cons[simp]: "mset_heap (t#ts) = mset_tree t + mset_heap ts"
by (auto simp: mset_heap_def)

lemma mset_heap_empty_iff[simp]: "mset_heap ts = {#} \<longleftrightarrow> ts=[]"
by (auto simp: mset_heap_def)

lemma root_in_mset[simp]: "root t \<in># mset_tree t"
by (cases t) auto

lemma mset_heap_rev_eq[simp]: "mset_heap (rev ts) = mset_heap ts"
by (auto simp: mset_heap_def)

subsubsection \<open>Invariants\<close>

text \<open>Binomial tree\<close>
fun invar_btree :: "'a::linorder tree \<Rightarrow> bool" where
"invar_btree (Node r x ts) \<longleftrightarrow>
   (\<forall>t\<in>set ts. invar_btree t) \<and> map rank ts = rev [0..<r]"

text \<open>Ordering (heap) invariant\<close>
fun invar_otree :: "'a::linorder tree \<Rightarrow> bool" where
"invar_otree (Node _ x ts) \<longleftrightarrow> (\<forall>t\<in>set ts. invar_otree t \<and> x \<le> root t)"

definition "invar_tree t \<longleftrightarrow> invar_btree t \<and> invar_otree t"

text \<open>Binomial Heap invariant\<close>
definition "invar ts \<longleftrightarrow> (\<forall>t\<in>set ts. invar_tree t) \<and> (sorted_wrt (<) (map rank ts))"


text \<open>The children of a node are a valid heap\<close>
lemma invar_children:
  "invar_tree (Node r v ts) \<Longrightarrow> invar (rev ts)"
  by (auto simp: invar_tree_def invar_def rev_map[symmetric])


subsection \<open>Operations and Their Functional Correctness\<close>

subsubsection \<open>\<open>link\<close>\<close>

context
includes pattern_aliases
begin

fun link :: "('a::linorder) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "link (Node r x\<^sub>1 ts\<^sub>1 =: t\<^sub>1) (Node r' x\<^sub>2 ts\<^sub>2 =: t\<^sub>2) =
    (if x\<^sub>1\<le>x\<^sub>2 then Node (r+1) x\<^sub>1 (t\<^sub>2#ts\<^sub>1) else Node (r+1) x\<^sub>2 (t\<^sub>1#ts\<^sub>2))"

end

lemma invar_link:
  assumes "invar_tree t\<^sub>1"
  assumes "invar_tree t\<^sub>2"
  assumes "rank t\<^sub>1 = rank t\<^sub>2"
  shows "invar_tree (link t\<^sub>1 t\<^sub>2)"
using assms unfolding invar_tree_def
by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) auto

lemma rank_link[simp]: "rank (link t\<^sub>1 t\<^sub>2) = rank t\<^sub>1 + 1"
by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) simp

lemma mset_link[simp]: "mset_tree (link t\<^sub>1 t\<^sub>2) = mset_tree t\<^sub>1 + mset_tree t\<^sub>2"
by (cases "(t\<^sub>1, t\<^sub>2)" rule: link.cases) simp

subsubsection \<open>\<open>ins_tree\<close>\<close>

fun ins_tree :: "'a::linorder tree \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "ins_tree t [] = [t]"
| "ins_tree t\<^sub>1 (t\<^sub>2#ts) =
  (if rank t\<^sub>1 < rank t\<^sub>2 then t\<^sub>1#t\<^sub>2#ts else ins_tree (link t\<^sub>1 t\<^sub>2) ts)"

lemma invar_tree0[simp]: "invar_tree (Node 0 x [])"
unfolding invar_tree_def by auto

lemma invar_Cons[simp]:
  "invar (t#ts)
  \<longleftrightarrow> invar_tree t \<and> invar ts \<and> (\<forall>t'\<in>set ts. rank t < rank t')"
by (auto simp: invar_def)

lemma invar_ins_tree:
  assumes "invar_tree t"
  assumes "invar ts"
  assumes "\<forall>t'\<in>set ts. rank t \<le> rank t'"
  shows "invar (ins_tree t ts)"
using assms
by (induction t ts rule: ins_tree.induct) (auto simp: invar_link less_eq_Suc_le[symmetric])

lemma mset_heap_ins_tree[simp]:
  "mset_heap (ins_tree t ts) = mset_tree t + mset_heap ts"
by (induction t ts rule: ins_tree.induct) auto

lemma ins_tree_rank_bound:
  assumes "t' \<in> set (ins_tree t ts)"
  assumes "\<forall>t'\<in>set ts. rank t\<^sub>0 < rank t'"
  assumes "rank t\<^sub>0 < rank t"
  shows "rank t\<^sub>0 < rank t'"
using assms
by (induction t ts rule: ins_tree.induct) (auto split: if_splits)

subsubsection \<open>\<open>insert\<close>\<close>

hide_const (open) insert

definition insert :: "'a::linorder \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"insert x ts = ins_tree (Node 0 x []) ts"

lemma invar_insert[simp]: "invar t \<Longrightarrow> invar (insert x t)"
by (auto intro!: invar_ins_tree simp: insert_def)

lemma mset_heap_insert[simp]: "mset_heap (insert x t) = {#x#} + mset_heap t"
by(auto simp: insert_def)

subsubsection \<open>\<open>merge\<close>\<close>

context
includes pattern_aliases
begin

fun merge :: "'a::linorder heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "merge ts\<^sub>1 [] = ts\<^sub>1"
| "merge [] ts\<^sub>2 = ts\<^sub>2"
| "merge (t\<^sub>1#ts\<^sub>1 =: h\<^sub>1) (t\<^sub>2#ts\<^sub>2 =: h\<^sub>2) = (
    if rank t\<^sub>1 < rank t\<^sub>2 then t\<^sub>1 # merge ts\<^sub>1 h\<^sub>2 else
    if rank t\<^sub>2 < rank t\<^sub>1 then t\<^sub>2 # merge h\<^sub>1 ts\<^sub>2
    else ins_tree (link t\<^sub>1 t\<^sub>2) (merge ts\<^sub>1 ts\<^sub>2)
  )"

end

lemma merge_simp2[simp]: "merge [] ts\<^sub>2 = ts\<^sub>2"
by (cases ts\<^sub>2) auto

lemma merge_rank_bound:
  assumes "t' \<in> set (merge ts\<^sub>1 ts\<^sub>2)"
  assumes "\<forall>t\<^sub>1\<in>set ts\<^sub>1. rank t < rank t\<^sub>1"
  assumes "\<forall>t\<^sub>2\<in>set ts\<^sub>2. rank t < rank t\<^sub>2"
  shows "rank t < rank t'"
using assms
by (induction ts\<^sub>1 ts\<^sub>2 arbitrary: t' rule: merge.induct)
   (auto split: if_splits simp: ins_tree_rank_bound)

lemma invar_merge[simp]:
  assumes "invar ts\<^sub>1"
  assumes "invar ts\<^sub>2"
  shows "invar (merge ts\<^sub>1 ts\<^sub>2)"
using assms
by (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
   (auto 0 3 simp: Suc_le_eq intro!: invar_ins_tree invar_link elim!: merge_rank_bound)


text \<open>Longer, more explicit proof of @{thm [source] invar_merge}, 
      to illustrate the application of the @{thm [source] merge_rank_bound} lemma.\<close>
lemma 
  assumes "invar ts\<^sub>1"
  assumes "invar ts\<^sub>2"
  shows "invar (merge ts\<^sub>1 ts\<^sub>2)"
  using assms
proof (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  case (3 t\<^sub>1 ts\<^sub>1 t\<^sub>2 ts\<^sub>2)
  \<comment> \<open>Invariants of the parts can be shown automatically\<close>
  from "3.prems" have [simp]: 
    "invar_tree t\<^sub>1" "invar_tree t\<^sub>2"
    (*"invar (merge (t\<^sub>1#ts\<^sub>1) ts\<^sub>2)" 
    "invar (merge ts\<^sub>1 (t\<^sub>2#ts\<^sub>2))"
    "invar (merge ts\<^sub>1 ts\<^sub>2)"*)
    by auto

  \<comment> \<open>These are the three cases of the @{const merge} function\<close>
  consider (LT) "rank t\<^sub>1 < rank t\<^sub>2"
         | (GT) "rank t\<^sub>1 > rank t\<^sub>2"
         | (EQ) "rank t\<^sub>1 = rank t\<^sub>2"
    using antisym_conv3 by blast
  then show ?case proof cases
    case LT 
    \<comment> \<open>@{const merge} takes the first tree from the left heap\<close>
    then have "merge (t\<^sub>1 # ts\<^sub>1) (t\<^sub>2 # ts\<^sub>2) = t\<^sub>1 # merge ts\<^sub>1 (t\<^sub>2 # ts\<^sub>2)" by simp
    also have "invar \<dots>" proof (simp, intro conjI)
      \<comment> \<open>Invariant follows from induction hypothesis\<close>
      show "invar (merge ts\<^sub>1 (t\<^sub>2 # ts\<^sub>2))"
        using LT "3.IH" "3.prems" by simp

      \<comment> \<open>It remains to show that \<open>t\<^sub>1\<close> has smallest rank.\<close>
      show "\<forall>t'\<in>set (merge ts\<^sub>1 (t\<^sub>2 # ts\<^sub>2)). rank t\<^sub>1 < rank t'"
        \<comment> \<open>Which is done by auxiliary lemma @{thm [source] merge_rank_bound}\<close>
        using LT "3.prems" by (force elim!: merge_rank_bound)
    qed
    finally show ?thesis .
  next
    \<comment> \<open>@{const merge} takes the first tree from the right heap\<close>
    case GT 
    \<comment> \<open>The proof is anaologous to the \<open>LT\<close> case\<close>
    then show ?thesis using "3.prems" "3.IH" by (force elim!: merge_rank_bound)
  next
    case [simp]: EQ
    \<comment> \<open>@{const merge} links both first trees, and inserts them into the merged remaining heaps\<close>
    have "merge (t\<^sub>1 # ts\<^sub>1) (t\<^sub>2 # ts\<^sub>2) = ins_tree (link t\<^sub>1 t\<^sub>2) (merge ts\<^sub>1 ts\<^sub>2)" by simp
    also have "invar \<dots>" proof (intro invar_ins_tree invar_link) 
      \<comment> \<open>Invariant of merged remaining heaps follows by IH\<close>
      show "invar (merge ts\<^sub>1 ts\<^sub>2)"
        using EQ "3.prems" "3.IH" by auto

      \<comment> \<open>For insertion, we have to show that the rank of the linked tree is \<open>\<le>\<close> the 
          ranks in the merged remaining heaps\<close>
      show "\<forall>t'\<in>set (merge ts\<^sub>1 ts\<^sub>2). rank (link t\<^sub>1 t\<^sub>2) \<le> rank t'"
      proof -
        \<comment> \<open>Which is, again, done with the help of @{thm [source] merge_rank_bound}\<close>
        have "rank (link t\<^sub>1 t\<^sub>2) = Suc (rank t\<^sub>2)" by simp
        thus ?thesis using "3.prems" by (auto simp: Suc_le_eq elim!: merge_rank_bound)
      qed
    qed simp_all
    finally show ?thesis .
  qed
qed auto


lemma mset_heap_merge[simp]:
  "mset_heap (merge ts\<^sub>1 ts\<^sub>2) = mset_heap ts\<^sub>1 + mset_heap ts\<^sub>2"
by (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct) auto

subsubsection \<open>\<open>get_min\<close>\<close>

fun get_min :: "'a::linorder heap \<Rightarrow> 'a" where
  "get_min [t] = root t"
| "get_min (t#ts) = min (root t) (get_min ts)"

lemma invar_tree_root_min:
  assumes "invar_tree t"
  assumes "x \<in># mset_tree t"
  shows "root t \<le> x"
using assms unfolding invar_tree_def
by (induction t arbitrary: x rule: mset_tree.induct) (fastforce simp: mset_heap_def)

lemma get_min_mset:
  assumes "ts\<noteq>[]"
  assumes "invar ts"
  assumes "x \<in># mset_heap ts"
  shows "get_min ts \<le> x"
  using assms
apply (induction ts arbitrary: x rule: get_min.induct)
apply (auto
      simp: invar_tree_root_min min_def intro: order_trans;
      meson linear order_trans invar_tree_root_min
      )+
done

lemma get_min_member:
  "ts\<noteq>[] \<Longrightarrow> get_min ts \<in># mset_heap ts"
by (induction ts rule: get_min.induct) (auto simp: min_def)

lemma get_min:
  assumes "mset_heap ts \<noteq> {#}"
  assumes "invar ts"
  shows "get_min ts = Min_mset (mset_heap ts)"
using assms get_min_member get_min_mset
by (auto simp: eq_Min_iff)

subsubsection \<open>\<open>get_min_rest\<close>\<close>

fun get_min_rest :: "'a::linorder heap \<Rightarrow> 'a tree \<times> 'a heap" where
  "get_min_rest [t] = (t,[])"
| "get_min_rest (t#ts) = (let (t',ts') = get_min_rest ts
                     in if root t \<le> root t' then (t,ts) else (t',t#ts'))"

lemma get_min_rest_get_min_same_root:
  assumes "ts\<noteq>[]"
  assumes "get_min_rest ts = (t',ts')"
  shows "root t' = get_min ts"
using assms
by (induction ts arbitrary: t' ts' rule: get_min.induct) (auto simp: min_def split: prod.splits)

lemma mset_get_min_rest:
  assumes "get_min_rest ts = (t',ts')"
  assumes "ts\<noteq>[]"
  shows "mset ts = {#t'#} + mset ts'"
using assms
by (induction ts arbitrary: t' ts' rule: get_min.induct) (auto split: prod.splits if_splits)

lemma set_get_min_rest:
  assumes "get_min_rest ts = (t', ts')"
  assumes "ts\<noteq>[]"
  shows "set ts = Set.insert t' (set ts')"
using mset_get_min_rest[OF assms, THEN arg_cong[where f=set_mset]]
by auto

lemma invar_get_min_rest:
  assumes "get_min_rest ts = (t',ts')"
  assumes "ts\<noteq>[]"
  assumes "invar ts"
  shows "invar_tree t'" and "invar ts'"
proof -
  have "invar_tree t' \<and> invar ts'"
    using assms
    proof (induction ts arbitrary: t' ts' rule: get_min.induct)
      case (2 t v va)
      then show ?case
        apply (clarsimp split: prod.splits if_splits)
        apply (drule set_get_min_rest; fastforce)
        done
    qed auto
  thus "invar_tree t'" and "invar ts'" by auto
qed

subsubsection \<open>\<open>del_min\<close>\<close>

definition del_min :: "'a::linorder heap \<Rightarrow> 'a::linorder heap" where
"del_min ts = (case get_min_rest ts of
   (Node r x ts\<^sub>1, ts\<^sub>2) \<Rightarrow> merge (rev ts\<^sub>1) ts\<^sub>2)"

lemma invar_del_min[simp]:
  assumes "ts \<noteq> []"
  assumes "invar ts"
  shows "invar (del_min ts)"
using assms
unfolding del_min_def
by (auto
      split: prod.split tree.split
      intro!: invar_merge invar_children 
      dest: invar_get_min_rest
    )

lemma mset_heap_del_min:
  assumes "ts \<noteq> []"
  shows "mset_heap ts = mset_heap (del_min ts) + {# get_min ts #}"
using assms
unfolding del_min_def
apply (clarsimp split: tree.split prod.split)
apply (frule (1) get_min_rest_get_min_same_root)
apply (frule (1) mset_get_min_rest)
apply (auto simp: mset_heap_def)
done


subsubsection \<open>Instantiating the Priority Queue Locale\<close>

text \<open>Last step of functional correctness proof: combine all the above lemmas
to show that binomial heaps satisfy the specification of priority queues with merge.\<close>

interpretation binheap: Priority_Queue_Merge
  where empty = "[]" and is_empty = "(=) []" and insert = insert
  and get_min = get_min and del_min = del_min and merge = merge
  and invar = invar and mset = mset_heap
proof (unfold_locales, goal_cases)
  case 1 thus ?case by simp
next
  case 2 thus ?case by auto
next
  case 3 thus ?case by auto
next
  case (4 q)
  thus ?case using mset_heap_del_min[of q] get_min[OF _ \<open>invar q\<close>]
    by (auto simp: union_single_eq_diff)
next
  case (5 q) thus ?case using get_min[of q] by auto
next
  case 6 thus ?case by (auto simp add: invar_def)
next
  case 7 thus ?case by simp
next
  case 8 thus ?case by simp
next
  case 9 thus ?case by simp
next
  case 10 thus ?case by simp
qed


subsection \<open>Complexity\<close>

text \<open>The size of a binomial tree is determined by its rank\<close>
lemma size_mset_btree:
  assumes "invar_btree t"
  shows "size (mset_tree t) = 2^rank t"
  using assms
proof (induction t)
  case (Node r v ts)
  hence IH: "size (mset_tree t) = 2^rank t" if "t \<in> set ts" for t
    using that by auto

  from Node have COMPL: "map rank ts = rev [0..<r]" by auto

  have "size (mset_heap ts) = (\<Sum>t\<leftarrow>ts. size (mset_tree t))"
    by (induction ts) auto
  also have "\<dots> = (\<Sum>t\<leftarrow>ts. 2^rank t)" using IH
    by (auto cong: map_cong)
  also have "\<dots> = (\<Sum>r\<leftarrow>map rank ts. 2^r)"
    by (induction ts) auto
  also have "\<dots> = (\<Sum>i\<in>{0..<r}. 2^i)"
    unfolding COMPL
    by (auto simp: rev_map[symmetric] interv_sum_list_conv_sum_set_nat)
  also have "\<dots> = 2^r - 1"
    by (induction r) auto
  finally show ?case
    by (simp)
qed

lemma size_mset_tree:
  assumes "invar_tree t"
  shows "size (mset_tree t) = 2^rank t"
using assms unfolding invar_tree_def
by (simp add: size_mset_btree)

text \<open>The length of a binomial heap is bounded by the number of its elements\<close>
lemma size_mset_heap:
  assumes "invar ts"
  shows "length ts \<le> log 2 (size (mset_heap ts) + 1)"
proof -
  from \<open>invar ts\<close> have
    ASC: "sorted_wrt (<) (map rank ts)" and
    TINV: "\<forall>t\<in>set ts. invar_tree t"
    unfolding invar_def by auto

  have "(2::nat)^length ts = (\<Sum>i\<in>{0..<length ts}. 2^i) + 1"
    by (simp add: sum_power2)
  also have "\<dots> \<le> (\<Sum>t\<leftarrow>ts. 2^rank t) + 1"
    using sorted_wrt_less_sum_mono_lowerbound[OF _ ASC, of "(^) (2::nat)"]
    using power_increasing[where a="2::nat"]
    by (auto simp: o_def)
  also have "\<dots> = (\<Sum>t\<leftarrow>ts. size (mset_tree t)) + 1" using TINV
    by (auto cong: map_cong simp: size_mset_tree)
  also have "\<dots> = size (mset_heap ts) + 1"
    unfolding mset_heap_def by (induction ts) auto
  finally have "2^length ts \<le> size (mset_heap ts) + 1" .
  then show ?thesis using le_log2_of_power by blast
qed

subsubsection \<open>Timing Functions\<close>

text \<open>
  We define timing functions for each operation, and provide
  estimations of their complexity.
\<close>
definition T_link :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> nat" where
[simp]: "T_link _ _ = 1"

text \<open>This function is non-canonical: we omitted a \<open>+1\<close> in the \<open>else\<close>-part,
  to keep the following analysis simpler and more to the point.
\<close>
fun T_ins_tree :: "'a::linorder tree \<Rightarrow> 'a heap \<Rightarrow> nat" where
  "T_ins_tree t [] = 1"
| "T_ins_tree t\<^sub>1 (t\<^sub>2 # rest) = (
    (if rank t\<^sub>1 < rank t\<^sub>2 then 1
     else T_link t\<^sub>1 t\<^sub>2 + T_ins_tree (link t\<^sub>1 t\<^sub>2) rest)
  )"

definition T_insert :: "'a::linorder \<Rightarrow> 'a heap \<Rightarrow> nat" where
"T_insert x ts = T_ins_tree (Node 0 x []) ts + 1"

lemma T_ins_tree_simple_bound: "T_ins_tree t ts \<le> length ts + 1"
by (induction t ts rule: T_ins_tree.induct) auto

subsubsection \<open>\<open>T_insert\<close>\<close>

lemma T_insert_bound:
  assumes "invar ts"
  shows "T_insert x ts \<le> log 2 (size (mset_heap ts) + 1) + 2"
proof -
  have "real (T_insert x ts) \<le> real (length ts) + 2"
    unfolding T_insert_def using T_ins_tree_simple_bound 
    using of_nat_mono by fastforce
  also note size_mset_heap[OF \<open>invar ts\<close>]
  finally show ?thesis by simp
qed

subsubsection \<open>\<open>T_merge\<close>\<close>

context
includes pattern_aliases
begin

fun T_merge :: "'a::linorder heap \<Rightarrow> 'a heap \<Rightarrow> nat" where
  "T_merge ts\<^sub>1 [] = 1"
| "T_merge [] ts\<^sub>2 = 1"
| "T_merge (t\<^sub>1#ts\<^sub>1 =: h\<^sub>1) (t\<^sub>2#ts\<^sub>2 =: h\<^sub>2) = 1 + (
    if rank t\<^sub>1 < rank t\<^sub>2 then T_merge ts\<^sub>1 h\<^sub>2
    else if rank t\<^sub>2 < rank t\<^sub>1 then T_merge h\<^sub>1 ts\<^sub>2
    else T_ins_tree (link t\<^sub>1 t\<^sub>2) (merge ts\<^sub>1 ts\<^sub>2) + T_merge ts\<^sub>1 ts\<^sub>2
  )"

end

text \<open>A crucial idea is to estimate the time in correlation with the
  result length, as each carry reduces the length of the result.\<close>

lemma T_ins_tree_length:
  "T_ins_tree t ts + length (ins_tree t ts) = 2 + length ts"
by (induction t ts rule: ins_tree.induct) auto

lemma T_merge_length:
  "length (merge ts\<^sub>1 ts\<^sub>2) + T_merge ts\<^sub>1 ts\<^sub>2 \<le> 2 * (length ts\<^sub>1 + length ts\<^sub>2) + 1"
by (induction ts\<^sub>1 ts\<^sub>2 rule: T_merge.induct)
   (auto simp: T_ins_tree_length algebra_simps)

text \<open>Finally, we get the desired logarithmic bound\<close>
lemma T_merge_bound:
  fixes ts\<^sub>1 ts\<^sub>2
  defines "n\<^sub>1 \<equiv> size (mset_heap ts\<^sub>1)"
  defines "n\<^sub>2 \<equiv> size (mset_heap ts\<^sub>2)"
  assumes "invar ts\<^sub>1" "invar ts\<^sub>2"
  shows "T_merge ts\<^sub>1 ts\<^sub>2 \<le> 4*log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 1"
proof -
  note n_defs = assms(1,2)

  have "T_merge ts\<^sub>1 ts\<^sub>2 \<le> 2 * real (length ts\<^sub>1) + 2 * real (length ts\<^sub>2) + 1"
    using T_merge_length[of ts\<^sub>1 ts\<^sub>2] by simp
  also note size_mset_heap[OF \<open>invar ts\<^sub>1\<close>]
  also note size_mset_heap[OF \<open>invar ts\<^sub>2\<close>]
  finally have "T_merge ts\<^sub>1 ts\<^sub>2 \<le> 2 * log 2 (n\<^sub>1 + 1) + 2 * log 2 (n\<^sub>2 + 1) + 1"
    unfolding n_defs by (simp add: algebra_simps)
  also have "log 2 (n\<^sub>1 + 1) \<le> log 2 (n\<^sub>1 + n\<^sub>2 + 1)" 
    unfolding n_defs by (simp add: algebra_simps)
  also have "log 2 (n\<^sub>2 + 1) \<le> log 2 (n\<^sub>1 + n\<^sub>2 + 1)" 
    unfolding n_defs by (simp add: algebra_simps)
  finally show ?thesis by (simp add: algebra_simps)
qed

subsubsection \<open>\<open>T_get_min\<close>\<close>

fun T_get_min :: "'a::linorder heap \<Rightarrow> nat" where
  "T_get_min [t] = 1"
| "T_get_min (t#ts) = 1 + T_get_min ts"

lemma T_get_min_estimate: "ts\<noteq>[] \<Longrightarrow> T_get_min ts = length ts"
by (induction ts rule: T_get_min.induct) auto

lemma T_get_min_bound:
  assumes "invar ts"
  assumes "ts\<noteq>[]"
  shows "T_get_min ts \<le> log 2 (size (mset_heap ts) + 1)"
proof -
  have 1: "T_get_min ts = length ts" using assms T_get_min_estimate by auto
  also note size_mset_heap[OF \<open>invar ts\<close>]
  finally show ?thesis .
qed

subsubsection \<open>\<open>T_del_min\<close>\<close>

fun T_get_min_rest :: "'a::linorder heap \<Rightarrow> nat" where
  "T_get_min_rest [t] = 1"
| "T_get_min_rest (t#ts) = 1 + T_get_min_rest ts"

lemma T_get_min_rest_estimate: "ts\<noteq>[] \<Longrightarrow> T_get_min_rest ts = length ts"
  by (induction ts rule: T_get_min_rest.induct) auto

lemma T_get_min_rest_bound:
  assumes "invar ts"
  assumes "ts\<noteq>[]"
  shows "T_get_min_rest ts \<le> log 2 (size (mset_heap ts) + 1)"
proof -
  have 1: "T_get_min_rest ts = length ts" using assms T_get_min_rest_estimate by auto
  also note size_mset_heap[OF \<open>invar ts\<close>]
  finally show ?thesis .
qed

text\<open>Note that although the definition of function \<^const>\<open>rev\<close> has quadratic complexity,
it can and is implemented (via suitable code lemmas) as a linear time function.
Thus the following definition is justified:\<close>

definition "T_rev xs = length xs + 1"

definition T_del_min :: "'a::linorder heap \<Rightarrow> nat" where
  "T_del_min ts = T_get_min_rest ts + (case get_min_rest ts of (Node _ x ts\<^sub>1, ts\<^sub>2)
                    \<Rightarrow> T_rev ts\<^sub>1 + T_merge (rev ts\<^sub>1) ts\<^sub>2
  ) + 1"

lemma T_del_min_bound:
  fixes ts
  defines "n \<equiv> size (mset_heap ts)"
  assumes "invar ts" and "ts\<noteq>[]"
  shows "T_del_min ts \<le> 6 * log 2 (n+1) + 3"
proof -
  obtain r x ts\<^sub>1 ts\<^sub>2 where GM: "get_min_rest ts = (Node r x ts\<^sub>1, ts\<^sub>2)"
    by (metis surj_pair tree.exhaust_sel)

  have I1: "invar (rev ts\<^sub>1)" and I2: "invar ts\<^sub>2"
    using invar_get_min_rest[OF GM \<open>ts\<noteq>[]\<close> \<open>invar ts\<close>] invar_children
    by auto

  define n\<^sub>1 where "n\<^sub>1 = size (mset_heap ts\<^sub>1)"
  define n\<^sub>2 where "n\<^sub>2 = size (mset_heap ts\<^sub>2)"

  have "n\<^sub>1 \<le> n" "n\<^sub>1 + n\<^sub>2 \<le> n" unfolding n_def n\<^sub>1_def n\<^sub>2_def
    using mset_get_min_rest[OF GM \<open>ts\<noteq>[]\<close>]
    by (auto simp: mset_heap_def)

  have "T_del_min ts = real (T_get_min_rest ts) + real (T_rev ts\<^sub>1) + real (T_merge (rev ts\<^sub>1) ts\<^sub>2) + 1"
    unfolding T_del_min_def GM
    by simp
  also have "T_get_min_rest ts \<le> log 2 (n+1)" 
    using T_get_min_rest_bound[OF \<open>invar ts\<close> \<open>ts\<noteq>[]\<close>] unfolding n_def by simp
  also have "T_rev ts\<^sub>1 \<le> 1 + log 2 (n\<^sub>1 + 1)"
    unfolding T_rev_def n\<^sub>1_def using size_mset_heap[OF I1] by simp
  also have "T_merge (rev ts\<^sub>1) ts\<^sub>2 \<le> 4*log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 1"
    unfolding n\<^sub>1_def n\<^sub>2_def using T_merge_bound[OF I1 I2] by (simp add: algebra_simps)
  finally have "T_del_min ts \<le> log 2 (n+1) + log 2 (n\<^sub>1 + 1) + 4*log 2 (real (n\<^sub>1 + n\<^sub>2) + 1) + 3"
    by (simp add: algebra_simps)
  also note \<open>n\<^sub>1 + n\<^sub>2 \<le> n\<close>
  also note \<open>n\<^sub>1 \<le> n\<close>
  finally show ?thesis by (simp add: algebra_simps)
qed

end
