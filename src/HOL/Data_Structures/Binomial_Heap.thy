(* Author: Peter Lammich *)

section \<open>Binomial Heap\<close>

theory Binomial_Heap
imports
  Complex_Main
  Priority_Queue
begin

lemma sum_power2: "(\<Sum>i\<in>{0..<k}. (2::nat)^i) = 2^k-1"    
by (induction k) auto

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
  unfolding mset_heap_def 
  by auto 
  
lemma mset_heap_Cons[simp]: "mset_heap (t#ts) = mset_tree t + mset_heap ts"
  unfolding mset_heap_def by auto 
  
lemma mset_heap_empty_iff[simp]: "mset_heap ts = {#} \<longleftrightarrow> ts=[]"
  unfolding mset_heap_def by auto 
    
lemma root_in_mset[simp]: "root t \<in># mset_tree t" by (cases t) auto    
    
lemma mset_heap_rev_eq[simp]: "mset_heap (rev ts) = mset_heap ts"    
  unfolding mset_heap_def by auto
    
subsubsection \<open>Invariants\<close>  
  
text \<open>Binomial invariant\<close>  
fun invar_btree :: "'a::linorder tree \<Rightarrow> bool" 
  where
    "invar_btree (Node r x ts) \<longleftrightarrow> 
      (\<forall>t\<in>set ts. invar_btree t) 
    \<and> (map rank ts = rev [0..<r])"

definition invar_bheap :: "'a::linorder heap \<Rightarrow> bool" where
  "invar_bheap ts
  \<longleftrightarrow> (\<forall>t\<in>set ts. invar_btree t) \<and> (sorted_wrt (op <) (map rank ts))"

text \<open>Ordering (heap) invariant\<close>
fun otree_invar :: "'a::linorder tree \<Rightarrow> bool"
  where
    "otree_invar (Node _ x ts) \<longleftrightarrow> (\<forall>t\<in>set ts. otree_invar t \<and> x \<le> root t)"

definition oheap_invar :: "'a::linorder heap \<Rightarrow> bool" where
  "oheap_invar ts \<longleftrightarrow> (\<forall>t\<in>set ts. otree_invar t)"
  
definition invar :: "'a::linorder heap \<Rightarrow> bool" where
  "invar ts \<longleftrightarrow> invar_bheap ts \<and> oheap_invar ts"
  
text \<open>The children of a node are a valid heap\<close>
lemma children_oheap_invar: 
  "otree_invar (Node r v ts) \<Longrightarrow> oheap_invar (rev ts)"  
  by (auto simp: oheap_invar_def)

lemma children_invar_bheap: 
  "invar_btree (Node r v ts) \<Longrightarrow> invar_bheap (rev ts)"  
  by (auto simp: invar_bheap_def rev_map[symmetric])
      
subsection \<open>Operations\<close>  
    
definition link :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "link t\<^sub>1 t\<^sub>2 = (case (t\<^sub>1,t\<^sub>2) of (Node r x\<^sub>1 c\<^sub>1, Node _ x\<^sub>2 c\<^sub>2) \<Rightarrow>
    if x\<^sub>1\<le>x\<^sub>2 then Node (r+1) x\<^sub>1 (t\<^sub>2#c\<^sub>1) else Node (r+1) x\<^sub>2 (t\<^sub>1#c\<^sub>2)
  )"
  
lemma link_invar_btree:
  assumes "invar_btree t\<^sub>1"
  assumes "invar_btree t\<^sub>2"
  assumes "rank t\<^sub>1 = rank t\<^sub>2"  
  shows "invar_btree (link t\<^sub>1 t\<^sub>2)"  
  using assms  
  unfolding link_def
  by (force split: tree.split )
    
lemma link_otree_invar:      
  assumes "otree_invar t\<^sub>1"
  assumes "otree_invar t\<^sub>2"
  shows "otree_invar (link t\<^sub>1 t\<^sub>2)"  
  using assms  
  unfolding link_def
  by (auto split: tree.split)
    
lemma link_rank[simp]: "rank (link t\<^sub>1 t\<^sub>2) = rank t\<^sub>1 + 1"
  unfolding link_def
  by (auto split: tree.split)
    
lemma link_mset[simp]: "mset_tree (link t\<^sub>1 t\<^sub>2) = mset_tree t\<^sub>1 + mset_tree t\<^sub>2"
  unfolding link_def
  by (auto split: tree.split)
    
fun ins_tree :: "'a::linorder tree \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "ins_tree t [] = [t]"
| "ins_tree t\<^sub>1 (t\<^sub>2#ts) = (
    if rank t\<^sub>1 < rank t\<^sub>2 then t\<^sub>1#t\<^sub>2#ts else ins_tree (link t\<^sub>1 t\<^sub>2) ts
  )"  
    
lemma invar_bheap_Cons[simp]: 
  "invar_bheap (t#ts) 
  \<longleftrightarrow> invar_btree t \<and> invar_bheap ts \<and> (\<forall>t'\<in>set ts. rank t < rank t')"
  unfolding invar_bheap_def
  by (auto simp: sorted_wrt_Cons)
  
lemma ins_tree_invar_btree:
  assumes "invar_btree t" 
  assumes "invar_bheap ts"
  assumes "\<forall>t'\<in>set ts. rank t \<le> rank t'"  
  shows "invar_bheap (ins_tree t ts)"  
  using assms
  apply (induction t ts rule: ins_tree.induct)  
  apply (auto simp: link_invar_btree less_eq_Suc_le[symmetric])
  done  
    
lemma oheap_invar_Cons[simp]: 
  "oheap_invar (t#ts) \<longleftrightarrow> otree_invar t \<and> oheap_invar ts"    
  unfolding oheap_invar_def by auto
    
lemma ins_tree_otree_invar:
  assumes "otree_invar t" 
  assumes "oheap_invar ts"
  shows "oheap_invar (ins_tree t ts)"  
  using assms  
  apply (induction t ts rule: ins_tree.induct)  
  apply (auto simp: link_otree_invar)
  done  
    
lemma ins_tree_mset[simp]: 
  "mset_heap (ins_tree t ts) = mset_tree t + mset_heap ts"    
  by (induction t ts rule: ins_tree.induct) auto  

lemma ins_tree_rank_bound:
  assumes "t' \<in> set (ins_tree t ts)"  
  assumes "\<forall>t'\<in>set ts. rank t\<^sub>0 < rank t'"
  assumes "rank t\<^sub>0 < rank t"  
  shows "rank t\<^sub>0 < rank t'"
  using assms  
  by (induction t ts rule: ins_tree.induct) (auto split: if_splits)
  
    
definition ins :: "'a::linorder \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "ins x ts = ins_tree (Node 0 x []) ts"
  
lemma ins_invar[simp]: "invar t \<Longrightarrow> invar (ins x t)"
  unfolding ins_def invar_def
  by (auto intro!: ins_tree_invar_btree simp: ins_tree_otree_invar)  
    
lemma ins_mset[simp]: "mset_heap (ins x t) = {#x#} + mset_heap t"
  unfolding ins_def
  by auto  
  
fun merge :: "'a::linorder heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "merge ts\<^sub>1 [] = ts\<^sub>1"
| "merge [] ts\<^sub>2 = ts\<^sub>2"  
| "merge (t\<^sub>1#ts\<^sub>1) (t\<^sub>2#ts\<^sub>2) = (
    if rank t\<^sub>1 < rank t\<^sub>2 then t\<^sub>1#merge ts\<^sub>1 (t\<^sub>2#ts\<^sub>2)
    else if rank t\<^sub>2 < rank t\<^sub>1 then t\<^sub>2#merge (t\<^sub>1#ts\<^sub>1) ts\<^sub>2
    else ins_tree (link t\<^sub>1 t\<^sub>2) (merge ts\<^sub>1 ts\<^sub>2)
  )"  
    
lemma merge_simp2[simp]: "merge [] ts\<^sub>2 = ts\<^sub>2" by (cases ts\<^sub>2) auto
  
lemma merge_rank_bound:
  assumes "t' \<in> set (merge ts\<^sub>1 ts\<^sub>2)"
  assumes "\<forall>t'\<in>set ts\<^sub>1. rank t < rank t'"
  assumes "\<forall>t'\<in>set ts\<^sub>2. rank t < rank t'"
  shows "rank t < rank t'"
  using assms
  apply (induction ts\<^sub>1 ts\<^sub>2 arbitrary: t' rule: merge.induct)
  apply (auto split: if_splits simp: ins_tree_rank_bound)
  done
    
lemma merge_invar_bheap:
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
      by (auto simp: Suc_le_eq ins_tree_invar_btree link_invar_btree)
  qed
qed simp_all
  
lemma merge_oheap_invar:
  assumes "oheap_invar ts\<^sub>1"
  assumes "oheap_invar ts\<^sub>2"
  shows "oheap_invar (merge ts\<^sub>1 ts\<^sub>2)"  
  using assms
  apply (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct)
  apply (auto simp: ins_tree_otree_invar link_otree_invar)  
  done
    
lemma merge_invar[simp]: "\<lbrakk> invar ts\<^sub>1; invar ts\<^sub>2 \<rbrakk> \<Longrightarrow> invar (merge ts\<^sub>1 ts\<^sub>2)"
  unfolding invar_def by (auto simp: merge_invar_bheap merge_oheap_invar)
    
lemma merge_mset[simp]: 
  "mset_heap (merge ts\<^sub>1 ts\<^sub>2) = mset_heap ts\<^sub>1 + mset_heap ts\<^sub>2"
  by (induction ts\<^sub>1 ts\<^sub>2 rule: merge.induct) auto  
    

fun find_min :: "'a::linorder heap \<Rightarrow> 'a" where
  "find_min [t] = root t"
| "find_min (t#ts) = (let x=root t; 
                          y=find_min ts
                      in if x\<le>y then x else y)"
  
lemma otree_invar_root_min:
  assumes "otree_invar t"
  assumes "x \<in># mset_tree t" 
  shows "root t \<le> x"  
  using assms
  apply (induction t arbitrary: x rule: mset_tree.induct)  
  apply (force simp: mset_heap_def)
  done  
    
  
lemma find_min_mset_aux: 
  assumes "ts\<noteq>[]"    
  assumes "oheap_invar ts"
  assumes "x \<in># mset_heap ts"  
  shows "find_min ts \<le> x"
  using assms  
  apply (induction ts arbitrary: x rule: find_min.induct)  
  apply (auto 
      simp: Let_def otree_invar_root_min intro: order_trans;
      meson linear order_trans otree_invar_root_min
      )+
  done  

lemma find_min_mset: 
  assumes "ts\<noteq>[]"    
  assumes "invar ts"
  assumes "x \<in># mset_heap ts"  
  shows "find_min ts \<le> x"
  using assms unfolding invar_def 
  by (auto simp: find_min_mset_aux)
    
    
lemma find_min_member:    
  assumes "ts\<noteq>[]"    
  shows "find_min ts \<in># mset_heap ts"  
  using assms  
  apply (induction ts rule: find_min.induct)  
  apply (auto simp: Let_def)
  done  

lemma find_min:    
  assumes "mset_heap ts \<noteq> {#}"
  assumes "invar ts"
  shows "find_min ts = Min_mset (mset_heap ts)"
  using assms find_min_member find_min_mset  
  by (auto simp: eq_Min_iff)
    

fun get_min :: "'a::linorder heap \<Rightarrow> 'a tree \<times> 'a heap" where
  "get_min [t] = (t,[])"
| "get_min (t#ts) = (let (t',ts') = get_min ts
                     in if root t \<le> root t' then (t,ts) else (t',t#ts'))"

  
lemma get_min_find_min_same_root: 
  assumes "ts\<noteq>[]"
  assumes "get_min ts = (t',ts')"  
  shows "root t' = find_min ts"  
  using assms  
  apply (induction ts arbitrary: t' ts' rule: find_min.induct)
  apply (auto simp: Let_def split: prod.splits)
  done  
  
lemma get_min_mset:    
  assumes "get_min ts = (t',ts')"  
  assumes "ts\<noteq>[]"
  shows "mset ts = {#t'#} + mset ts'"  
  using assms  
  apply (induction ts arbitrary: t' ts' rule: find_min.induct)
  apply (auto split: prod.splits if_splits)
  done  
    
lemma get_min_set:
  assumes "get_min ts = (t', ts')" 
  assumes "ts\<noteq>[]"
  shows "set ts = insert t' (set ts')" 
  using get_min_mset[OF assms, THEN arg_cong[where f=set_mset]]
  by auto  

    
lemma get_min_invar_bheap:    
  assumes "get_min ts = (t',ts')"  
  assumes "ts\<noteq>[]"
  assumes "invar_bheap ts"  
  shows "invar_btree t'" and "invar_bheap ts'"
proof -
  have "invar_btree t' \<and> invar_bheap ts'"
    using assms  
    proof (induction ts arbitrary: t' ts' rule: find_min.induct)
      case (2 t v va)
      then show ?case
        apply (clarsimp split: prod.splits if_splits)
        apply (drule get_min_set; fastforce)
        done  
    qed auto
  thus "invar_btree t'" and "invar_bheap ts'" by auto
qed
  
lemma get_min_oheap_invar:    
  assumes "get_min ts = (t',ts')"  
  assumes "ts\<noteq>[]"
  assumes "oheap_invar ts"  
  shows "otree_invar t'" and "oheap_invar ts'"
  using assms  
  apply (induction ts arbitrary: t' ts' rule: find_min.induct)
  apply (auto split: prod.splits if_splits)
  done  
    
definition del_min :: "'a::linorder heap \<Rightarrow> 'a::linorder heap" where
"del_min ts = (case get_min ts of
   (Node r x ts\<^sub>1, ts\<^sub>2) \<Rightarrow> merge (rev ts\<^sub>1) ts\<^sub>2)"
  
lemma del_min_invar[simp]:
  assumes "ts \<noteq> []"
  assumes "invar ts"
  shows "invar (del_min ts)"
  using assms  
  unfolding invar_def del_min_def  
  by (auto 
      split: prod.split tree.split 
      intro!: merge_invar_bheap merge_oheap_invar
      dest: get_min_invar_bheap get_min_oheap_invar
      intro!: children_oheap_invar children_invar_bheap
      )
    
lemma del_min_mset: 
  assumes "ts \<noteq> []"
  shows "mset_heap ts = mset_heap (del_min ts) + {# find_min ts #}"
  using assms
  unfolding del_min_def
  apply (clarsimp split: tree.split prod.split)
  apply (frule (1) get_min_find_min_same_root)  
  apply (frule (1) get_min_mset)  
  apply (auto simp: mset_heap_def)
  done  

subsection \<open>Complexity\<close>
  
text \<open>The size of a binomial tree is determined by its rank\<close>  
lemma size_btree:
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
lemma size_bheap:      
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
    by (auto cong: sum_list_cong simp: size_btree)
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
| "t_ins_tree t\<^sub>1 (t\<^sub>2#rest) = (
    (if rank t\<^sub>1 < rank t\<^sub>2 then 1 
     else t_link t\<^sub>1 t\<^sub>2 + t_ins_tree (link t\<^sub>1 t\<^sub>2) rest)
  )"  
    
  
definition t_ins :: "'a::linorder \<Rightarrow> 'a heap \<Rightarrow> nat" where
  "t_ins x ts = t_ins_tree (Node 0 x []) ts"

lemma t_ins_tree_simple_bound: "t_ins_tree t ts \<le> length ts + 1" for t 
  by (induction t ts rule: t_ins_tree.induct) auto
  
lemma t_ins_bound: 
  assumes "invar ts"
  shows "t_ins x ts \<le> log 2 (size (mset_heap ts) + 1) + 1"
proof -

  have 1: "t_ins x ts \<le> length ts + 1" 
    unfolding t_ins_def by (rule t_ins_tree_simple_bound)
  also have "\<dots> \<le> log 2 (2 * (size (mset_heap ts) + 1))" 
  proof -
    from size_bheap[of ts] assms 
    have "2 ^ length ts \<le> size (mset_heap ts) + 1"
      unfolding invar_def by auto
    hence "2 ^ (length ts + 1) \<le> 2 * (size (mset_heap ts) + 1)" by auto
    thus ?thesis using le_log2_of_power by blast
  qed
  finally show ?thesis 
    by (simp only: log_mult of_nat_mult) auto
qed      
  
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
lemma l_ins_tree_estimate: 
  "t_ins_tree t ts + length (ins_tree t ts) = 2 + length ts"
by (induction t ts rule: ins_tree.induct) auto

lemma l_merge_estimate: 
  "length (merge ts\<^sub>1 ts\<^sub>2) + t_merge ts\<^sub>1 ts\<^sub>2 \<le> 2 * (length ts\<^sub>1 + length ts\<^sub>2) + 1"
  apply (induction ts\<^sub>1 ts\<^sub>2 rule: t_merge.induct)  
  apply (auto simp: l_ins_tree_estimate algebra_simps)
  done
    
text \<open>Finally, we get the desired logarithmic bound\<close>
lemma t_merge_bound_aux:
  fixes ts\<^sub>1 ts\<^sub>2
  defines "n\<^sub>1 \<equiv> size (mset_heap ts\<^sub>1)"    
  defines "n\<^sub>2 \<equiv> size (mset_heap ts\<^sub>2)"
  assumes BINVARS: "invar_bheap ts\<^sub>1" "invar_bheap ts\<^sub>2"
  shows "t_merge ts\<^sub>1 ts\<^sub>2 \<le> 4*log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 2"
proof -
  define n where "n = n\<^sub>1 + n\<^sub>2"  
      
  from l_merge_estimate[of ts\<^sub>1 ts\<^sub>2] 
  have "t_merge ts\<^sub>1 ts\<^sub>2 \<le> 2 * (length ts\<^sub>1 + length ts\<^sub>2) + 1" by auto
  hence "(2::nat)^t_merge ts\<^sub>1 ts\<^sub>2 \<le> 2^(2 * (length ts\<^sub>1 + length ts\<^sub>2) + 1)" 
    by (rule power_increasing) auto
  also have "\<dots> = 2*(2^length ts\<^sub>1)\<^sup>2*(2^length ts\<^sub>2)\<^sup>2"    
    by (auto simp: algebra_simps power_add power_mult)
  also note BINVARS(1)[THEN size_bheap]
  also note BINVARS(2)[THEN size_bheap]
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
  
  
fun t_find_min :: "'a::linorder heap \<Rightarrow> nat" where
  "t_find_min [t] = 1"
| "t_find_min (t#ts) = 1 + t_find_min ts"

lemma t_find_min_estimate: "ts\<noteq>[] \<Longrightarrow> t_find_min ts = length ts"  
by (induction ts rule: t_find_min.induct) auto
  
lemma t_find_min_bound: 
  assumes "invar ts"
  assumes "ts\<noteq>[]"
  shows "t_find_min ts \<le> log 2 (size (mset_heap ts) + 1)"
proof -
  have 1: "t_find_min ts = length ts" using assms t_find_min_estimate by auto
  also have "\<dots> \<le> log 2 (size (mset_heap ts) + 1)"
  proof -
    from size_bheap[of ts] assms have "2 ^ length ts \<le> size (mset_heap ts) + 1"
      unfolding invar_def by auto
    thus ?thesis using le_log2_of_power by blast
  qed
  finally show ?thesis by auto 
qed  
    
fun t_get_min :: "'a::linorder heap \<Rightarrow> nat" where
  "t_get_min [t] = 1"
| "t_get_min (t#ts) = 1 + t_get_min ts"

lemma t_get_min_estimate: "ts\<noteq>[] \<Longrightarrow> t_get_min ts = length ts"  
  by (induction ts rule: t_get_min.induct) auto
  
lemma t_get_min_bound_aux: 
  assumes "invar_bheap ts"
  assumes "ts\<noteq>[]"
  shows "t_get_min ts \<le> log 2 (size (mset_heap ts) + 1)"
proof -
  have 1: "t_get_min ts = length ts" using assms t_get_min_estimate by auto
  also have "\<dots> \<le> log 2 (size (mset_heap ts) + 1)"
  proof -
    from size_bheap[of ts] assms have "2 ^ length ts \<le> size (mset_heap ts) + 1"
      by auto
    thus ?thesis using le_log2_of_power by blast
  qed
  finally show ?thesis by auto 
qed  

lemma t_get_min_bound: 
  assumes "invar ts"
  assumes "ts\<noteq>[]"
  shows "t_get_min ts \<le> log 2 (size (mset_heap ts) + 1)"
  using assms t_get_min_bound_aux unfolding invar_def by blast  
  
thm fold_simps -- \<open>Theorems used by code generator\<close>
fun t_fold :: "('a \<Rightarrow> 'b \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> nat" 
  where
  "t_fold t_f f [] s = 1"
| "t_fold t_f f (x # xs) s = t_f x s + t_fold t_f f xs (f x s)"
    
text \<open>Estimation for constant function is enough for our purpose\<close>
lemma t_fold_const_bound:  
  shows "t_fold (\<lambda>_ _. K) f l s = K*length l + 1"  
  by (induction l arbitrary: s) auto

lemma t_fold_bounded_bound:  
  assumes "\<forall>x s. x\<in>set l \<longrightarrow> t_f x s \<le> K"
  shows "t_fold t_f f l s \<le> K*length l + 1"  
  using assms 
  apply (induction l arbitrary: s)
  apply (simp; fail)
  using add_mono
  by (fastforce simp: algebra_simps) 
  
thm rev_conv_fold -- \<open>Theorem used by code generator\<close>
definition "t_rev xs = t_fold (\<lambda>_ _. 1) op # xs []"
lemma t_rev_bound: "t_rev xs = length xs + 1"
  unfolding t_rev_def t_fold_const_bound by auto
    
definition t_del_min :: "'a::linorder heap \<Rightarrow> nat" 
  where
  "t_del_min ts = t_get_min ts + (case get_min ts of (Node _ x ts\<^sub>1, ts\<^sub>2)
                    \<Rightarrow> t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2
  )"
  
lemma t_rev_ts1_bound_aux: 
  fixes ts
  defines "n \<equiv> size (mset_heap ts)"
  assumes BINVAR: "invar_bheap (rev ts)"
  shows "t_rev ts \<le> 1 + log 2 (n+1)"
proof -
  have "t_rev ts = length ts + 1"
    by (auto simp: t_rev_bound)
  hence "2^t_rev ts = 2*2^length ts" by auto
  also have "\<dots> \<le> 2*n+2" using size_bheap[OF BINVAR] by (auto simp: n_def)
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
  obtain r x ts\<^sub>1 ts\<^sub>2 where GM: "get_min ts = (Node r x ts\<^sub>1, ts\<^sub>2)"
    by (metis surj_pair tree.exhaust_sel)

  note BINVAR' = get_min_invar_bheap[OF GM \<open>ts\<noteq>[]\<close> BINVAR]
  hence BINVAR1: "invar_bheap (rev ts\<^sub>1)" by (blast intro: children_invar_bheap)

  define n\<^sub>1 where "n\<^sub>1 = size (mset_heap ts\<^sub>1)"
  define n\<^sub>2 where "n\<^sub>2 = size (mset_heap ts\<^sub>2)"
      
  have t_rev_ts1_bound: "t_rev ts\<^sub>1 \<le> 1 + log 2 (n+1)"
  proof -
    note t_rev_ts1_bound_aux[OF BINVAR1, simplified, folded n\<^sub>1_def]
    also have "n\<^sub>1 \<le> n" 
      unfolding n\<^sub>1_def n_def
      using get_min_mset[OF GM \<open>ts\<noteq>[]\<close>]
      by (auto simp: mset_heap_def)
    finally show ?thesis by (auto simp: algebra_simps)
  qed    
    
  have "t_del_min ts = t_get_min ts + t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2"
    unfolding t_del_min_def by (simp add: GM)
  also have "\<dots> \<le> log 2 (n+1) + t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2"
    using t_get_min_bound_aux[OF assms(2-)] by (auto simp: n_def)
  also have "\<dots> \<le> 2*log 2 (n+1) + t_merge (rev ts\<^sub>1) ts\<^sub>2 + 1"
    using t_rev_ts1_bound by auto
  also have "\<dots> \<le> 2*log 2 (n+1) + 4 * log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 3"
    using t_merge_bound_aux[OF \<open>invar_bheap (rev ts\<^sub>1)\<close> \<open>invar_bheap ts\<^sub>2\<close>]
    by (auto simp: n\<^sub>1_def n\<^sub>2_def algebra_simps)
  also have "n\<^sub>1 + n\<^sub>2 \<le> n"
    unfolding n\<^sub>1_def n\<^sub>2_def n_def
    using get_min_mset[OF GM \<open>ts\<noteq>[]\<close>]
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

subsection \<open>Instantiating the Priority Queue Locale\<close>

interpretation binheap: 
  Priority_Queue "[]" "op = []" ins find_min del_min invar mset_heap
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
  then show ?case using del_min_mset[of q] find_min[OF _ \<open>invar q\<close>] 
    by (auto simp: union_single_eq_diff)
next
  case (5 q)
  then show ?case using find_min[of q] by auto
next 
  case 6 
  then show ?case by (auto simp add: invar_def invar_bheap_def oheap_invar_def)
next
  case (7 q x)
  then show ?case by simp
next
  case (8 q)
  then show ?case by simp
qed
    
    
(* Exercise? *)    
subsection \<open>Combined Find and Delete Operation\<close>
  
text \<open>We define an operation that returns the minimum element and 
  a heap with this element removed. \<close>
definition pop_min :: "'a::linorder heap \<Rightarrow> 'a \<times> 'a::linorder heap" 
  where
  "pop_min ts = (case get_min ts of (Node _ x ts\<^sub>1, ts\<^sub>2) 
                    \<Rightarrow> (x,merge (rev ts\<^sub>1) ts\<^sub>2)
  )"
    
lemma pop_min_refine:  
  assumes "ts \<noteq> []"
  shows "pop_min ts = (find_min ts, del_min ts)"
  unfolding pop_min_def del_min_def
  by (auto 
      split: prod.split tree.split 
      dest: get_min_find_min_same_root[OF assms])
  
lemma pop_min_invar:
  assumes "ts \<noteq> []"
  assumes "invar ts"
  assumes "pop_min ts = (x,ts')"  
  shows "invar ts'"  
  using del_min_invar[of ts] pop_min_refine[of ts] assms by simp

lemma pop_min_mset:    
  assumes "ts \<noteq> []"
  assumes "invar ts"
  assumes "pop_min ts = (x,ts')"  
  shows "mset_heap ts = add_mset x (mset_heap ts')"
  using del_min_mset[of ts] pop_min_refine[of ts] assms by simp 
  
lemma pop_min_min:
  assumes "ts \<noteq> []"
  assumes "invar ts"
  assumes "pop_min ts = (x,ts')"  
  shows "\<forall>y\<in>#mset_heap ts'. x\<le>y"
  using pop_min_refine[of ts] del_min_mset[of ts] find_min_mset[of ts] assms
  by (auto simp del: binheap.mset_simps)
    

definition t_pop_min :: "'a::linorder heap \<Rightarrow> nat" 
  where
  "t_pop_min ts = t_get_min ts + (case get_min ts of (Node _ x ts\<^sub>1, ts\<^sub>2) 
                    \<Rightarrow> t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2
  )"
    
lemma t_pop_min_bound_aux:
  fixes ts
  defines "n \<equiv> size (mset_heap ts)"
  assumes BINVAR: "invar_bheap ts"
  assumes "ts\<noteq>[]"
  shows "t_pop_min ts \<le> 6 * log 2 (n+1) + 3"  
proof -
  obtain r x ts\<^sub>1 ts\<^sub>2 where GM: "get_min ts = (Node r x ts\<^sub>1, ts\<^sub>2)"
    by (metis surj_pair tree.exhaust_sel)

  note BINVAR' = get_min_invar_bheap[OF GM \<open>ts\<noteq>[]\<close> BINVAR]
  hence BINVAR1: "invar_bheap (rev ts\<^sub>1)" by (blast intro: children_invar_bheap)

  define n\<^sub>1 where "n\<^sub>1 = size (mset_heap ts\<^sub>1)"
  define n\<^sub>2 where "n\<^sub>2 = size (mset_heap ts\<^sub>2)"
      
  have t_rev_ts1_bound: "t_rev ts\<^sub>1 \<le> 1 + log 2 (n+1)"
  proof -
    note t_rev_ts1_bound_aux[OF BINVAR1, simplified, folded n\<^sub>1_def]
    also have "n\<^sub>1 \<le> n" 
      unfolding n\<^sub>1_def n_def
      using get_min_mset[OF GM \<open>ts\<noteq>[]\<close>]
      by (auto simp: mset_heap_def)
    finally show ?thesis by (auto simp: algebra_simps)
  qed

  have "t_pop_min ts = t_get_min ts + t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2"
    unfolding t_pop_min_def by (simp add: GM)
  also have "\<dots> \<le> log 2 (n+1) + t_rev ts\<^sub>1 + t_merge (rev ts\<^sub>1) ts\<^sub>2"
    using t_get_min_bound_aux[OF assms(2-)] by (auto simp: n_def)
  also have "\<dots> \<le> 2*log 2 (n+1) + t_merge (rev ts\<^sub>1) ts\<^sub>2 + 1"
    using t_rev_ts1_bound by auto
  also have "\<dots> \<le> 2*log 2 (n+1) + 4 * log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 3"
    using t_merge_bound_aux[OF \<open>invar_bheap (rev ts\<^sub>1)\<close> \<open>invar_bheap ts\<^sub>2\<close>]
    by (auto simp: n\<^sub>1_def n\<^sub>2_def algebra_simps)
  also have "n\<^sub>1 + n\<^sub>2 \<le> n"
    unfolding n\<^sub>1_def n\<^sub>2_def n_def
    using get_min_mset[OF GM \<open>ts\<noteq>[]\<close>]
    by (auto simp: mset_heap_def)
  finally have "t_pop_min ts \<le> 6 * log 2 (n+1) + 3" 
    by auto
  thus ?thesis by (simp add: algebra_simps)
qed      

end
