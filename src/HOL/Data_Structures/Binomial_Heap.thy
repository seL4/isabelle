(* Author: Peter Lammich
           Tobias Nipkow (tuning)
*)

section \<open>Binomial Heap\<close>

theory Binomial_Heap
imports
  Base_FDS
  Complex_Main
  Priority_Queue
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
  "mset_tree (Node _ a c) = {#a#} + (\<Sum>t\<in>#mset c. mset_tree t)"
  
definition mset_heap :: "'a::linorder heap \<Rightarrow> 'a multiset" where  
  "mset_heap c = (\<Sum>t\<in>#mset c. mset_tree t)"
  
lemma mset_tree_simp_alt[simp]: 
  "mset_tree (Node r a c) = {#a#} + mset_heap c"
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
  
text \<open>Binomial invariant\<close>  
fun invar_btree :: "'a::linorder tree \<Rightarrow> bool" where
"invar_btree (Node r x ts) \<longleftrightarrow> 
   (\<forall>t\<in>set ts. invar_btree t) \<and> map rank ts = rev [0..<r]"

definition invar_bheap :: "'a::linorder heap \<Rightarrow> bool" where
"invar_bheap ts
  \<longleftrightarrow> (\<forall>t\<in>set ts. invar_btree t) \<and> (sorted_wrt (op <) (map rank ts))"

text \<open>Ordering (heap) invariant\<close>
fun invar_otree :: "'a::linorder tree \<Rightarrow> bool" where
"invar_otree (Node _ x ts) \<longleftrightarrow> (\<forall>t\<in>set ts. invar_otree t \<and> x \<le> root t)"

definition invar_oheap :: "'a::linorder heap \<Rightarrow> bool" where
"invar_oheap ts \<longleftrightarrow> (\<forall>t\<in>set ts. invar_otree t)"
  
definition invar :: "'a::linorder heap \<Rightarrow> bool" where
"invar ts \<longleftrightarrow> invar_bheap ts \<and> invar_oheap ts"
  
text \<open>The children of a node are a valid heap\<close>
lemma invar_oheap_children: 
  "invar_otree (Node r v ts) \<Longrightarrow> invar_oheap (rev ts)"  
by (auto simp: invar_oheap_def)

lemma invar_bheap_children: 
  "invar_btree (Node r v ts) \<Longrightarrow> invar_bheap (rev ts)"  
by (auto simp: invar_bheap_def rev_map[symmetric])


subsection \<open>Operations and Their Functional Correctness\<close>  
    
subsubsection \<open>\<open>link\<close>\<close>

definition link :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "link t\<^sub>1 t\<^sub>2 = (case (t\<^sub>1,t\<^sub>2) of (Node r x\<^sub>1 c\<^sub>1, Node _ x\<^sub>2 c\<^sub>2) \<Rightarrow>
    if x\<^sub>1\<le>x\<^sub>2 then Node (r+1) x\<^sub>1 (t\<^sub>2#c\<^sub>1) else Node (r+1) x\<^sub>2 (t\<^sub>1#c\<^sub>2)
  )"

lemma invar_btree_link:
  assumes "invar_btree t\<^sub>1"
  assumes "invar_btree t\<^sub>2"
  assumes "rank t\<^sub>1 = rank t\<^sub>2"  
  shows "invar_btree (link t\<^sub>1 t\<^sub>2)"  
using assms 
by (auto simp: link_def split: tree.split)

lemma invar_link_otree:      
  assumes "invar_otree t\<^sub>1"
  assumes "invar_otree t\<^sub>2"
  shows "invar_otree (link t\<^sub>1 t\<^sub>2)"  
using assms 
by (auto simp: link_def split: tree.split)

lemma rank_link[simp]: "rank (link t\<^sub>1 t\<^sub>2) = rank t\<^sub>1 + 1"
by (auto simp: link_def split: tree.split)
    
lemma mset_link[simp]: "mset_tree (link t\<^sub>1 t\<^sub>2) = mset_tree t\<^sub>1 + mset_tree t\<^sub>2"
by (auto simp: link_def split: tree.split)
    
subsubsection \<open>\<open>ins_tree\<close>\<close>

fun ins_tree :: "'a::linorder tree \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "ins_tree t [] = [t]"
| "ins_tree t\<^sub>1 (t\<^sub>2#ts) =
  (if rank t\<^sub>1 < rank t\<^sub>2 then t\<^sub>1#t\<^sub>2#ts else ins_tree (link t\<^sub>1 t\<^sub>2) ts)"  
    
lemma invar_bheap_Cons[simp]: 
  "invar_bheap (t#ts) 
  \<longleftrightarrow> invar_btree t \<and> invar_bheap ts \<and> (\<forall>t'\<in>set ts. rank t < rank t')"
by (auto simp: sorted_wrt_Cons invar_bheap_def)
  
lemma invar_btree_ins_tree:
  assumes "invar_btree t" 
  assumes "invar_bheap ts"
  assumes "\<forall>t'\<in>set ts. rank t \<le> rank t'"  
  shows "invar_bheap (ins_tree t ts)"  
using assms
by (induction t ts rule: ins_tree.induct) (auto simp: invar_btree_link less_eq_Suc_le[symmetric])
    
lemma invar_oheap_Cons[simp]: 
  "invar_oheap (t#ts) \<longleftrightarrow> invar_otree t \<and> invar_oheap ts"    
by (auto simp: invar_oheap_def)

lemma invar_oheap_ins_tree:
  assumes "invar_otree t" 
  assumes "invar_oheap ts"
  shows "invar_oheap (ins_tree t ts)"  
using assms  
by (induction t ts rule: ins_tree.induct) (auto simp: invar_link_otree)
    
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
by (auto intro!: invar_btree_ins_tree simp: invar_oheap_ins_tree insert_def invar_def)  
    
lemma mset_heap_insert[simp]: "mset_heap (insert x t) = {#x#} + mset_heap t"
by(auto simp: insert_def)

subsubsection \<open>\<open>merge\<close>\<close>

fun merge :: "'a::linorder heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "merge ts\<^sub>1 [] = ts\<^sub>1"
| "merge [] ts\<^sub>2 = ts\<^sub>2"  
| "merge (t\<^sub>1#ts\<^sub>1) (t\<^sub>2#ts\<^sub>2) = (
    if rank t\<^sub>1 < rank t\<^sub>2 then t\<^sub>1 # merge ts\<^sub>1 (t\<^sub>2#ts\<^sub>2) else
    if rank t\<^sub>2 < rank t\<^sub>1 then t\<^sub>2 # merge (t\<^sub>1#ts\<^sub>1) ts\<^sub>2
    else ins_tree (link t\<^sub>1 t\<^sub>2) (merge ts\<^sub>1 ts\<^sub>2)
  )"

lemma merge_simp2[simp]: "merge [] ts\<^sub>2 = ts\<^sub>2"
by (cases ts\<^sub>2) auto
  
lemma merge_rank_bound:
  assumes "t' \<in> set (merge ts\<^sub>1 ts\<^sub>2)"
  assumes "\<forall>t'\<in>set ts\<^sub>1. rank t < rank t'"
  assumes "\<forall>t'\<in>set ts\<^sub>2. rank t < rank t'"
  shows "rank t < rank t'"
using assms
by (induction ts\<^sub>1 ts\<^sub>2 arbitrary: t' rule: merge.induct)
   (auto split: if_splits simp: ins_tree_rank_bound)

lemma invar_bheap_merge:
  assumes "invar_bheap ts\<^sub>1"
  assumes "invar_bheap ts\<^sub>2"
  shows "invar_bheap (merge ts\<^sub>1 ts\<^sub>2)"  
  using assms
proof (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  case (3 t\<^sub>1 ts\<^sub>1 t\<^sub>2 ts\<^sub>2)
    
  from "3.prems" have [simp]: "invar_btree t\<^sub>1" "invar_btree t\<^sub>2"  
    by auto
    
  consider (LT) "rank t\<^sub>1 < rank t\<^sub>2" 
         | (GT) "rank t\<^sub>1 > rank t\<^sub>2" 
         | (EQ) "rank t\<^sub>1 = rank t\<^sub>2"
    using antisym_conv3 by blast
  then show ?case proof cases
    case LT
    then show ?thesis using 3
      by (force elim!: merge_rank_bound)
  next
    case GT
    then show ?thesis using 3
      by (force elim!: merge_rank_bound)
  next
    case [simp]: EQ

    from "3.IH"(3) "3.prems" have [simp]: "invar_bheap (merge ts\<^sub>1 ts\<^sub>2)"
      by auto
      
    have "rank t\<^sub>2 < rank t'" if "t' \<in> set (merge ts\<^sub>1 ts\<^sub>2)" for t'
      using that
      apply (rule merge_rank_bound)
      using "3.prems" by auto
    with EQ show ?thesis
      by (auto simp: Suc_le_eq invar_btree_ins_tree invar_btree_link)
  qed
qed simp_all
  
lemma invar_oheap_merge:
  assumes "invar_oheap ts\<^sub>1"
  assumes "invar_oheap ts\<^sub>2"
  shows "invar_oheap (merge ts\<^sub>1 ts\<^sub>2)"  
using assms
by (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
   (auto simp: invar_oheap_ins_tree invar_link_otree)  
 
lemma invar_merge[simp]: "\<lbrakk> invar ts\<^sub>1; invar ts\<^sub>2 \<rbrakk> \<Longrightarrow> invar (merge ts\<^sub>1 ts\<^sub>2)"
by (auto simp: invar_def invar_bheap_merge invar_oheap_merge)
    
lemma mset_heap_merge[simp]: 
  "mset_heap (merge ts\<^sub>1 ts\<^sub>2) = mset_heap ts\<^sub>1 + mset_heap ts\<^sub>2"
by (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct) auto  
    
subsubsection \<open>\<open>get_min\<close>\<close>

fun get_min :: "'a::linorder heap \<Rightarrow> 'a" where
  "get_min [t] = root t"
| "get_min (t#ts) = min (root t) (get_min ts)"
  
lemma invar_otree_root_min:
  assumes "invar_otree t"
  assumes "x \<in># mset_tree t" 
  shows "root t \<le> x"  
using assms
by (induction t arbitrary: x rule: mset_tree.induct) (fastforce simp: mset_heap_def)
  
lemma get_min_mset_aux: 
  assumes "ts\<noteq>[]"    
  assumes "invar_oheap ts"
  assumes "x \<in># mset_heap ts"  
  shows "get_min ts \<le> x"
  using assms  
apply (induction ts arbitrary: x rule: get_min.induct)  
apply (auto 
      simp: invar_otree_root_min min_def intro: order_trans;
      meson linear order_trans invar_otree_root_min
      )+
done  

lemma get_min_mset: 
  assumes "ts\<noteq>[]"    
  assumes "invar ts"
  assumes "x \<in># mset_heap ts"  
  shows "get_min ts \<le> x"
using assms by (auto simp: invar_def get_min_mset_aux)

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

lemma invar_bheap_get_min_rest:    
  assumes "get_min_rest ts = (t',ts')"  
  assumes "ts\<noteq>[]"
  assumes "invar_bheap ts"  
  shows "invar_btree t'" and "invar_bheap ts'"
proof -
  have "invar_btree t' \<and> invar_bheap ts'"
    using assms  
    proof (induction ts arbitrary: t' ts' rule: get_min.induct)
      case (2 t v va)
      then show ?case
        apply (clarsimp split: prod.splits if_splits)
        apply (drule set_get_min_rest; fastforce)
        done  
    qed auto
  thus "invar_btree t'" and "invar_bheap ts'" by auto
qed

lemma invar_oheap_get_min_rest:    
  assumes "get_min_rest ts = (t',ts')"  
  assumes "ts\<noteq>[]"
  assumes "invar_oheap ts"  
  shows "invar_otree t'" and "invar_oheap ts'"
using assms  
by (induction ts arbitrary: t' ts' rule: get_min.induct) (auto split: prod.splits if_splits)

subsubsection \<open>\<open>del_min\<close>\<close>

definition del_min :: "'a::linorder heap \<Rightarrow> 'a::linorder heap" where
"del_min ts = (case get_min_rest ts of
   (Node r x ts\<^sub>1, ts\<^sub>2) \<Rightarrow> merge (rev ts\<^sub>1) ts\<^sub>2)"
  
lemma invar_del_min[simp]:
  assumes "ts \<noteq> []"
  assumes "invar ts"
  shows "invar (del_min ts)"
using assms  
unfolding invar_def del_min_def  
by (auto 
      split: prod.split tree.split 
      intro!: invar_bheap_merge invar_oheap_merge
      dest: invar_bheap_get_min_rest invar_oheap_get_min_rest
      intro!: invar_oheap_children invar_bheap_children
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

interpretation binheap: Priority_Queue
  where empty = "[]" and is_empty = "op = []" and insert = insert
  and get_min = get_min and del_min = del_min
  and invar = invar and mset = mset_heap
proof (unfold_locales, goal_cases)
  case 1
  then show ?case by simp
next
  case (2 q)
  then show ?case by auto
next
  case (3 q x)
  then show ?case by auto
next
  case (4 q)
  then show ?case using mset_heap_del_min[of q] get_min[OF _ \<open>invar q\<close>] 
    by (auto simp: union_single_eq_diff)
next
  case (5 q)
  then show ?case using get_min[of q] by auto
next 
  case 6 
  then show ?case by (auto simp add: invar_def invar_bheap_def invar_oheap_def)
next
  case (7 q x)
  then show ?case by simp
next
  case (8 q)
  then show ?case by simp
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
    by (auto cong: sum_list_cong)
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
   
text \<open>The length of a binomial heap is bounded by the number of its elements\<close>  
lemma size_mset_bheap:      
  assumes "invar_bheap ts"
  shows "2^length ts \<le> size (mset_heap ts) + 1"
proof -
  from \<open>invar_bheap ts\<close> have 
    ASC: "sorted_wrt (op <) (map rank ts)" and
    TINV: "\<forall>t\<in>set ts. invar_btree t"
    unfolding invar_bheap_def by auto
      
  have "(2::nat)^length ts = (\<Sum>i\<in>{0..<length ts}. 2^i) + 1" 
    by (simp add: sum_power2)
  also have "\<dots> \<le> (\<Sum>t\<leftarrow>ts. 2^rank t) + 1"
    using sorted_wrt_less_sum_mono_lowerbound[OF _ ASC, of "op ^ (2::nat)"]
    using power_increasing[where a="2::nat"]  
    by (auto simp: o_def)
  also have "\<dots> = (\<Sum>t\<leftarrow>ts. size (mset_tree t)) + 1" using TINV   
    by (auto cong: sum_list_cong simp: size_mset_btree)
  also have "\<dots> = size (mset_heap ts) + 1"
    unfolding mset_heap_def by (induction ts) auto
  finally show ?thesis .
qed      
  
subsubsection \<open>Timing Functions\<close>

text \<open>
  We define timing functions for each operation, and provide
  estimations of their complexity.
\<close>
definition t_link :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> nat" where
[simp]: "t_link _ _ = 1"  

fun t_ins_tree :: "'a::linorder tree \<Rightarrow> 'a heap \<Rightarrow> nat" where
  "t_ins_tree t [] = 1"
| "t_ins_tree t\<^sub>1 (t\<^sub>2 # rest) = (
    (if rank t\<^sub>1 < rank t\<^sub>2 then 1 
     else t_link t\<^sub>1 t\<^sub>2 + t_ins_tree (link t\<^sub>1 t\<^sub>2) rest)
  )"  

definition t_insert :: "'a::linorder \<Rightarrow> 'a heap \<Rightarrow> nat" where
"t_insert x ts = t_ins_tree (Node 0 x []) ts"

lemma t_ins_tree_simple_bound: "t_ins_tree t ts \<le> length ts + 1"
by (induction t ts rule: t_ins_tree.induct) auto

subsubsection \<open>\<open>t_insert\<close>\<close>

lemma t_insert_bound: 
  assumes "invar ts"
  shows "t_insert x ts \<le> log 2 (size (mset_heap ts) + 1) + 1"
proof -

  have 1: "t_insert x ts \<le> length ts + 1" 
    unfolding t_insert_def by (rule t_ins_tree_simple_bound)
  also have "\<dots> \<le> log 2 (2 * (size (mset_heap ts) + 1))" 
  proof -
    from size_mset_bheap[of ts] assms 
    have "2 ^ length ts \<le> size (mset_heap ts) + 1"
      unfolding invar_def by auto
    hence "2 ^ (length ts + 1) \<le> 2 * (size (mset_heap ts) + 1)" by auto
    thus ?thesis using le_log2_of_power by blast
  qed
  finally show ?thesis 
    by (simp only: log_mult of_nat_mult) auto
qed      

subsubsection \<open>\<open>t_merge\<close>\<close>

fun t_merge :: "'a::linorder heap \<Rightarrow> 'a heap \<Rightarrow> nat" where
  "t_merge ts\<^sub>1 [] = 1"
| "t_merge [] ts\<^sub>2 = 1"  
| "t_merge (t\<^sub>1#ts\<^sub>1) (t\<^sub>2#ts\<^sub>2) = 1 + (
    if rank t\<^sub>1 < rank t\<^sub>2 then t_merge ts\<^sub>1 (t\<^sub>2#ts\<^sub>2)
    else if rank t\<^sub>2 < rank t\<^sub>1 then t_merge (t\<^sub>1#ts\<^sub>1) ts\<^sub>2
    else t_ins_tree (link t\<^sub>1 t\<^sub>2) (merge ts\<^sub>1 ts\<^sub>2) + t_merge ts\<^sub>1 ts\<^sub>2
  )"  
  
text \<open>A crucial idea is to estimate the time in correlation with the 
  result length, as each carry reduces the length of the result.\<close>  

lemma t_ins_tree_length:
  "t_ins_tree t ts + length (ins_tree t ts) = 2 + length ts"
by (induction t ts rule: ins_tree.induct) auto

lemma t_merge_length: 
  "length (merge ts\<^sub>1 ts\<^sub>2) + t_merge ts\<^sub>1 ts\<^sub>2 \<le> 2 * (length ts\<^sub>1 + length ts\<^sub>2) + 1"
by (induction ts\<^sub>1 ts\<^sub>2 rule: t_merge.induct)  
   (auto simp: t_ins_tree_length algebra_simps)

text \<open>Finally, we get the desired logarithmic bound\<close>
lemma t_merge_bound_aux:
  fixes ts\<^sub>1 ts\<^sub>2
  defines "n\<^sub>1 \<equiv> size (mset_heap ts\<^sub>1)"    
  defines "n\<^sub>2 \<equiv> size (mset_heap ts\<^sub>2)"
  assumes BINVARS: "invar_bheap ts\<^sub>1" "invar_bheap ts\<^sub>2"
  shows "t_merge ts\<^sub>1 ts\<^sub>2 \<le> 4*log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 2"
proof -
  define n where "n = n\<^sub>1 + n\<^sub>2"  
      
  from t_merge_length[of ts\<^sub>1 ts\<^sub>2] 
  have "t_merge ts\<^sub>1 ts\<^sub>2 \<le> 2 * (length ts\<^sub>1 + length ts\<^sub>2) + 1" by auto
  hence "(2::nat)^t_merge ts\<^sub>1 ts\<^sub>2 \<le> 2^(2 * (length ts\<^sub>1 + length ts\<^sub>2) + 1)" 
    by (rule power_increasing) auto
  also have "\<dots> = 2*(2^length ts\<^sub>1)\<^sup>2*(2^length ts\<^sub>2)\<^sup>2"    
    by (auto simp: algebra_simps power_add power_mult)
  also note BINVARS(1)[THEN size_mset_bheap]
  also note BINVARS(2)[THEN size_mset_bheap]
  finally have "2 ^ t_merge ts\<^sub>1 ts\<^sub>2 \<le> 2 * (n\<^sub>1 + 1)\<^sup>2 * (n\<^sub>2 + 1)\<^sup>2" 
    by (auto simp: power2_nat_le_eq_le n\<^sub>1_def n\<^sub>2_def)
  from le_log2_of_power[OF this] have "t_merge ts\<^sub>1 ts\<^sub>2 \<le> log 2 \<dots>"    
    by simp
  also have "\<dots> = log 2 2 + 2*log 2 (n\<^sub>1 + 1) + 2*log 2 (n\<^sub>2 + 1)"
    by (simp add: log_mult log_nat_power)
  also have "n\<^sub>2 \<le> n" by (auto simp: n_def)
  finally have "t_merge ts\<^sub>1 ts\<^sub>2 \<le> log 2 2 + 2*log 2 (n\<^sub>1 + 1) + 2*log 2 (n + 1)"    
    by auto
  also have "n\<^sub>1 \<le> n" by (auto simp: n_def)
  finally have "t_merge ts\<^sub>1 ts\<^sub>2 \<le> log 2 2 + 4*log 2 (n + 1)"
    by auto
  also have "log 2 2 \<le> 2" by auto
  finally have "t_merge ts\<^sub>1 ts\<^sub>2 \<le> 4*log 2 (n + 1) + 2" by auto
  thus ?thesis unfolding n_def by (auto simp: algebra_simps)
qed      
    
lemma t_merge_bound:
  fixes ts\<^sub>1 ts\<^sub>2
  defines "n\<^sub>1 \<equiv> size (mset_heap ts\<^sub>1)"    
  defines "n\<^sub>2 \<equiv> size (mset_heap ts\<^sub>2)"
  assumes "invar ts\<^sub>1" "invar ts\<^sub>2"
  shows "t_merge ts\<^sub>1 ts\<^sub>2 \<le> 4*log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 2"
using assms t_merge_bound_aux unfolding invar_def by blast  

subsubsection \<open>\<open>t_get_min\<close>\<close>

fun t_get_min :: "'a::linorder heap \<Rightarrow> nat" where
  "t_get_min [t] = 1"
| "t_get_min (t#ts) = 1 + t_get_min ts"

lemma t_get_min_estimate: "ts\<noteq>[] \<Longrightarrow> t_get_min ts = length ts"  
by (induction ts rule: t_get_min.induct) auto
  
lemma t_get_min_bound: 
  assumes "invar ts"
  assumes "ts\<noteq>[]"
  shows "t_get_min ts \<le> log 2 (size (mset_heap ts) + 1)"
proof -
  have 1: "t_get_min ts = length ts" using assms t_get_min_estimate by auto
  also have "\<dots> \<le> log 2 (size (mset_heap ts) + 1)"
  proof -
    from size_mset_bheap[of ts] assms have "2 ^ length ts \<le> size (mset_heap ts) + 1"
      unfolding invar_def by auto
    thus ?thesis using le_log2_of_power by blast
  qed
  finally show ?thesis by auto 
qed  

subsubsection \<open>\<open>t_del_min\<close>\<close>

fun t_get_min_rest :: "'a::linorder heap \<Rightarrow> nat" where
  "t_get_min_rest [t] = 1"
| "t_get_min_rest (t#ts) = 1 + t_get_min_rest ts"

lemma t_get_min_rest_estimate: "ts\<noteq>[] \<Longrightarrow> t_get_min_rest ts = length ts"  
  by (induction ts rule: t_get_min_rest.induct) auto
  
lemma t_get_min_rest_bound_aux: 
  assumes "invar_bheap ts"
  assumes "ts\<noteq>[]"
  shows "t_get_min_rest ts \<le> log 2 (size (mset_heap ts) + 1)"
proof -
  have 1: "t_get_min_rest ts = length ts" using assms t_get_min_rest_estimate by auto
  also have "\<dots> \<le> log 2 (size (mset_heap ts) + 1)"
  proof -
    from size_mset_bheap[of ts] assms have "2 ^ length ts \<le> size (mset_heap ts) + 1"
      by auto
    thus ?thesis using le_log2_of_power by blast
  qed
  finally show ?thesis by auto 
qed  

lemma t_get_min_rest_bound: 
  assumes "invar ts"
  assumes "ts\<noteq>[]"
  shows "t_get_min_rest ts \<le> log 2 (size (mset_heap ts) + 1)"
using assms t_get_min_rest_bound_aux unfolding invar_def by blast  

text\<open>Note that although the definition of function @{const rev} has quadratic complexity,
it can and is implemented (via suitable code lemmas) as a linear time function.
Thus the following definition is justified:\<close>

definition "t_rev xs = length xs + 1"

definition t_del_min :: "'a::linorder heap \<Rightarrow> nat" where
  "t_del_min ts = t_get_min_rest ts + (case get_min_rest ts of (Node _ x ts\<^sub>1, ts\<^sub>2)
                    \<Rightarrow> t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2
  )"
  
lemma t_rev_ts1_bound_aux: 
  fixes ts
  defines "n \<equiv> size (mset_heap ts)"
  assumes BINVAR: "invar_bheap (rev ts)"
  shows "t_rev ts \<le> 1 + log 2 (n+1)"
proof -
  have "t_rev ts = length ts + 1" by (auto simp: t_rev_def)
  hence "2^t_rev ts = 2*2^length ts" by auto
  also have "\<dots> \<le> 2*n+2" using size_mset_bheap[OF BINVAR] by (auto simp: n_def)
  finally have "2 ^ t_rev ts \<le> 2 * n + 2" .
  from le_log2_of_power[OF this] have "t_rev ts \<le> log 2 (2 * (n + 1))"
    by auto
  also have "\<dots> = 1 + log 2 (n+1)"
    by (simp only: of_nat_mult log_mult) auto  
  finally show ?thesis by (auto simp: algebra_simps)
qed    

lemma t_del_min_bound_aux:
  fixes ts
  defines "n \<equiv> size (mset_heap ts)"
  assumes BINVAR: "invar_bheap ts"
  assumes "ts\<noteq>[]"
  shows "t_del_min ts \<le> 6 * log 2 (n+1) + 3"  
proof -
  obtain r x ts\<^sub>1 ts\<^sub>2 where GM: "get_min_rest ts = (Node r x ts\<^sub>1, ts\<^sub>2)"
    by (metis surj_pair tree.exhaust_sel)

  note BINVAR' = invar_bheap_get_min_rest[OF GM \<open>ts\<noteq>[]\<close> BINVAR]
  hence BINVAR1: "invar_bheap (rev ts\<^sub>1)" by (blast intro: invar_bheap_children)

  define n\<^sub>1 where "n\<^sub>1 = size (mset_heap ts\<^sub>1)"
  define n\<^sub>2 where "n\<^sub>2 = size (mset_heap ts\<^sub>2)"
      
  have t_rev_ts1_bound: "t_rev ts\<^sub>1 \<le> 1 + log 2 (n+1)"
  proof -
    note t_rev_ts1_bound_aux[OF BINVAR1, simplified, folded n\<^sub>1_def]
    also have "n\<^sub>1 \<le> n" 
      unfolding n\<^sub>1_def n_def
      using mset_get_min_rest[OF GM \<open>ts\<noteq>[]\<close>]
      by (auto simp: mset_heap_def)
    finally show ?thesis by (auto simp: algebra_simps)
  qed    
    
  have "t_del_min ts = t_get_min_rest ts + t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2"
    unfolding t_del_min_def by (simp add: GM)
  also have "\<dots> \<le> log 2 (n+1) + t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2"
    using t_get_min_rest_bound_aux[OF assms(2-)] by (auto simp: n_def)
  also have "\<dots> \<le> 2*log 2 (n+1) + t_merge (rev ts\<^sub>1) ts\<^sub>2 + 1"
    using t_rev_ts1_bound by auto
  also have "\<dots> \<le> 2*log 2 (n+1) + 4 * log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 3"
    using t_merge_bound_aux[OF \<open>invar_bheap (rev ts\<^sub>1)\<close> \<open>invar_bheap ts\<^sub>2\<close>]
    by (auto simp: n\<^sub>1_def n\<^sub>2_def algebra_simps)
  also have "n\<^sub>1 + n\<^sub>2 \<le> n"
    unfolding n\<^sub>1_def n\<^sub>2_def n_def
    using mset_get_min_rest[OF GM \<open>ts\<noteq>[]\<close>]
    by (auto simp: mset_heap_def)
  finally have "t_del_min ts \<le> 6 * log 2 (n+1) + 3" 
    by auto
  thus ?thesis by (simp add: algebra_simps)
qed      
  
lemma t_del_min_bound:
  fixes ts
  defines "n \<equiv> size (mset_heap ts)"
  assumes "invar ts"
  assumes "ts\<noteq>[]"
  shows "t_del_min ts \<le> 6 * log 2 (n+1) + 3"  
using assms t_del_min_bound_aux unfolding invar_def by blast

end
