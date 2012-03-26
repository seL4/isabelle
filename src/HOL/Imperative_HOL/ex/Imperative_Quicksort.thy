(*  Title:      HOL/Imperative_HOL/ex/Imperative_Quicksort.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

header {* An imperative implementation of Quicksort on arrays *}

theory Imperative_Quicksort
imports
  "~~/src/HOL/Imperative_HOL/Imperative_HOL"
  Subarray
  "~~/src/HOL/Library/Multiset"
  "~~/src/HOL/Library/Efficient_Nat"
begin

text {* We prove QuickSort correct in the Relational Calculus. *}

definition swap :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
where
  "swap arr i j =
     do {
       x \<leftarrow> Array.nth arr i;
       y \<leftarrow> Array.nth arr j;
       Array.upd i y arr;
       Array.upd j x arr;
       return ()
     }"

lemma effect_swapI [effect_intros]:
  assumes "i < Array.length h a" "j < Array.length h a"
    "x = Array.get h a ! i" "y = Array.get h a ! j"
    "h' = Array.update a j x (Array.update a i y h)"
  shows "effect (swap a i j) h h' r"
  unfolding swap_def using assms by (auto intro!: effect_intros)

lemma swap_permutes:
  assumes "effect (swap a i j) h h' rs"
  shows "multiset_of (Array.get h' a) 
  = multiset_of (Array.get h a)"
  using assms
  unfolding swap_def
  by (auto simp add: Array.length_def multiset_of_swap dest: sym [of _ "h'"] elim!: effect_bindE effect_nthE effect_returnE effect_updE)

function part1 :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
where
  "part1 a left right p = (
     if (right \<le> left) then return right
     else do {
       v \<leftarrow> Array.nth a left;
       (if (v \<le> p) then (part1 a (left + 1) right p)
                    else (do { swap a left right;
  part1 a left (right - 1) p }))
     })"
by pat_completeness auto

termination
by (relation "measure (\<lambda>(_,l,r,_). r - l )") auto

declare part1.simps[simp del]

lemma part_permutes:
  assumes "effect (part1 a l r p) h h' rs"
  shows "multiset_of (Array.get h' a) 
  = multiset_of (Array.get h a)"
  using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  thus ?case
    unfolding part1.simps [of a l r p]
    by (elim effect_bindE effect_ifE effect_returnE effect_nthE) (auto simp add: swap_permutes)
qed

lemma part_returns_index_in_bounds:
  assumes "effect (part1 a l r p) h h' rs"
  assumes "l \<le> r"
  shows "l \<le> rs \<and> rs \<le> r"
using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  note cr = `effect (part1 a l r p) h h' rs`
  show ?case
  proof (cases "r \<le> l")
    case True (* Terminating case *)
    with cr `l \<le> r` show ?thesis
      unfolding part1.simps[of a l r p]
      by (elim effect_bindE effect_ifE effect_returnE effect_nthE) auto
  next
    case False (* recursive case *)
    note rec_condition = this
    let ?v = "Array.get h a ! l"
    show ?thesis
    proof (cases "?v \<le> p")
      case True
      with cr False
      have rec1: "effect (part1 a (l + 1) r p) h h' rs"
        unfolding part1.simps[of a l r p]
        by (elim effect_bindE effect_nthE effect_ifE effect_returnE) auto
      from rec_condition have "l + 1 \<le> r" by arith
      from 1(1)[OF rec_condition True rec1 `l + 1 \<le> r`]
      show ?thesis by simp
    next
      case False
      with rec_condition cr
      obtain h1 where swp: "effect (swap a l r) h h1 ()"
        and rec2: "effect (part1 a l (r - 1) p) h1 h' rs"
        unfolding part1.simps[of a l r p]
        by (elim effect_bindE effect_nthE effect_ifE effect_returnE) auto
      from rec_condition have "l \<le> r - 1" by arith
      from 1(2) [OF rec_condition False rec2 `l \<le> r - 1`] show ?thesis by fastforce
    qed
  qed
qed

lemma part_length_remains:
  assumes "effect (part1 a l r p) h h' rs"
  shows "Array.length h a = Array.length h' a"
using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  note cr = `effect (part1 a l r p) h h' rs`
  
  show ?case
  proof (cases "r \<le> l")
    case True (* Terminating case *)
    with cr show ?thesis
      unfolding part1.simps[of a l r p]
      by (elim effect_bindE effect_ifE effect_returnE effect_nthE) auto
  next
    case False (* recursive case *)
    with cr 1 show ?thesis
      unfolding part1.simps [of a l r p] swap_def
      by (auto elim!: effect_bindE effect_ifE effect_nthE effect_returnE effect_updE) fastforce
  qed
qed

lemma part_outer_remains:
  assumes "effect (part1 a l r p) h h' rs"
  shows "\<forall>i. i < l \<or> r < i \<longrightarrow> Array.get h (a::nat array) ! i = Array.get h' a ! i"
  using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  note cr = `effect (part1 a l r p) h h' rs`
  
  show ?case
  proof (cases "r \<le> l")
    case True (* Terminating case *)
    with cr show ?thesis
      unfolding part1.simps[of a l r p]
      by (elim effect_bindE effect_ifE effect_returnE effect_nthE) auto
  next
    case False (* recursive case *)
    note rec_condition = this
    let ?v = "Array.get h a ! l"
    show ?thesis
    proof (cases "?v \<le> p")
      case True
      with cr False
      have rec1: "effect (part1 a (l + 1) r p) h h' rs"
        unfolding part1.simps[of a l r p]
        by (elim effect_bindE effect_nthE effect_ifE effect_returnE) auto
      from 1(1)[OF rec_condition True rec1]
      show ?thesis by fastforce
    next
      case False
      with rec_condition cr
      obtain h1 where swp: "effect (swap a l r) h h1 ()"
        and rec2: "effect (part1 a l (r - 1) p) h1 h' rs"
        unfolding part1.simps[of a l r p]
        by (elim effect_bindE effect_nthE effect_ifE effect_returnE) auto
      from swp rec_condition have
        "\<forall>i. i < l \<or> r < i \<longrightarrow> Array.get h a ! i = Array.get h1 a ! i"
        unfolding swap_def
        by (elim effect_bindE effect_nthE effect_updE effect_returnE) auto
      with 1(2) [OF rec_condition False rec2] show ?thesis by fastforce
    qed
  qed
qed


lemma part_partitions:
  assumes "effect (part1 a l r p) h h' rs"
  shows "(\<forall>i. l \<le> i \<and> i < rs \<longrightarrow> Array.get h' (a::nat array) ! i \<le> p)
  \<and> (\<forall>i. rs < i \<and> i \<le> r \<longrightarrow> Array.get h' a ! i \<ge> p)"
  using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  note cr = `effect (part1 a l r p) h h' rs`
  
  show ?case
  proof (cases "r \<le> l")
    case True (* Terminating case *)
    with cr have "rs = r"
      unfolding part1.simps[of a l r p]
      by (elim effect_bindE effect_ifE effect_returnE effect_nthE) auto
    with True
    show ?thesis by auto
  next
    case False (* recursive case *)
    note lr = this
    let ?v = "Array.get h a ! l"
    show ?thesis
    proof (cases "?v \<le> p")
      case True
      with lr cr
      have rec1: "effect (part1 a (l + 1) r p) h h' rs"
        unfolding part1.simps[of a l r p]
        by (elim effect_bindE effect_nthE effect_ifE effect_returnE) auto
      from True part_outer_remains[OF rec1] have a_l: "Array.get h' a ! l \<le> p"
        by fastforce
      have "\<forall>i. (l \<le> i = (l = i \<or> Suc l \<le> i))" by arith
      with 1(1)[OF False True rec1] a_l show ?thesis
        by auto
    next
      case False
      with lr cr
      obtain h1 where swp: "effect (swap a l r) h h1 ()"
        and rec2: "effect (part1 a l (r - 1) p) h1 h' rs"
        unfolding part1.simps[of a l r p]
        by (elim effect_bindE effect_nthE effect_ifE effect_returnE) auto
      from swp False have "Array.get h1 a ! r \<ge> p"
        unfolding swap_def
        by (auto simp add: Array.length_def elim!: effect_bindE effect_nthE effect_updE effect_returnE)
      with part_outer_remains [OF rec2] lr have a_r: "Array.get h' a ! r \<ge> p"
        by fastforce
      have "\<forall>i. (i \<le> r = (i = r \<or> i \<le> r - 1))" by arith
      with 1(2)[OF lr False rec2] a_r show ?thesis
        by auto
    qed
  qed
qed


fun partition :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
where
  "partition a left right = do {
     pivot \<leftarrow> Array.nth a right;
     middle \<leftarrow> part1 a left (right - 1) pivot;
     v \<leftarrow> Array.nth a middle;
     m \<leftarrow> return (if (v \<le> pivot) then (middle + 1) else middle);
     swap a m right;
     return m
   }"

declare partition.simps[simp del]

lemma partition_permutes:
  assumes "effect (partition a l r) h h' rs"
  shows "multiset_of (Array.get h' a) 
  = multiset_of (Array.get h a)"
proof -
    from assms part_permutes swap_permutes show ?thesis
      unfolding partition.simps
      by (elim effect_bindE effect_returnE effect_nthE effect_ifE effect_updE) auto
qed

lemma partition_length_remains:
  assumes "effect (partition a l r) h h' rs"
  shows "Array.length h a = Array.length h' a"
proof -
  from assms part_length_remains show ?thesis
    unfolding partition.simps swap_def
    by (elim effect_bindE effect_returnE effect_nthE effect_ifE effect_updE) auto
qed

lemma partition_outer_remains:
  assumes "effect (partition a l r) h h' rs"
  assumes "l < r"
  shows "\<forall>i. i < l \<or> r < i \<longrightarrow> Array.get h (a::nat array) ! i = Array.get h' a ! i"
proof -
  from assms part_outer_remains part_returns_index_in_bounds show ?thesis
    unfolding partition.simps swap_def
    by (elim effect_bindE effect_returnE effect_nthE effect_ifE effect_updE) fastforce
qed

lemma partition_returns_index_in_bounds:
  assumes effect: "effect (partition a l r) h h' rs"
  assumes "l < r"
  shows "l \<le> rs \<and> rs \<le> r"
proof -
  from effect obtain middle h'' p where part: "effect (part1 a l (r - 1) p) h h'' middle"
    and rs_equals: "rs = (if Array.get h'' a ! middle \<le> Array.get h a ! r then middle + 1
         else middle)"
    unfolding partition.simps
    by (elim effect_bindE effect_returnE effect_nthE effect_ifE effect_updE) simp 
  from `l < r` have "l \<le> r - 1" by arith
  from part_returns_index_in_bounds[OF part this] rs_equals `l < r` show ?thesis by auto
qed

lemma partition_partitions:
  assumes effect: "effect (partition a l r) h h' rs"
  assumes "l < r"
  shows "(\<forall>i. l \<le> i \<and> i < rs \<longrightarrow> Array.get h' (a::nat array) ! i \<le> Array.get h' a ! rs) \<and>
  (\<forall>i. rs < i \<and> i \<le> r \<longrightarrow> Array.get h' a ! rs \<le> Array.get h' a ! i)"
proof -
  let ?pivot = "Array.get h a ! r" 
  from effect obtain middle h1 where part: "effect (part1 a l (r - 1) ?pivot) h h1 middle"
    and swap: "effect (swap a rs r) h1 h' ()"
    and rs_equals: "rs = (if Array.get h1 a ! middle \<le> ?pivot then middle + 1
         else middle)"
    unfolding partition.simps
    by (elim effect_bindE effect_returnE effect_nthE effect_ifE effect_updE) simp
  from swap have h'_def: "h' = Array.update a r (Array.get h1 a ! rs)
    (Array.update a rs (Array.get h1 a ! r) h1)"
    unfolding swap_def
    by (elim effect_bindE effect_returnE effect_nthE effect_updE) simp
  from swap have in_bounds: "r < Array.length h1 a \<and> rs < Array.length h1 a"
    unfolding swap_def
    by (elim effect_bindE effect_returnE effect_nthE effect_updE) simp
  from swap have swap_length_remains: "Array.length h1 a = Array.length h' a"
    unfolding swap_def by (elim effect_bindE effect_returnE effect_nthE effect_updE) auto
  from `l < r` have "l \<le> r - 1" by simp
  note middle_in_bounds = part_returns_index_in_bounds[OF part this]
  from part_outer_remains[OF part] `l < r`
  have "Array.get h a ! r = Array.get h1 a ! r"
    by fastforce
  with swap
  have right_remains: "Array.get h a ! r = Array.get h' a ! rs"
    unfolding swap_def
    by (auto simp add: Array.length_def elim!: effect_bindE effect_returnE effect_nthE effect_updE) (cases "r = rs", auto)
  from part_partitions [OF part]
  show ?thesis
  proof (cases "Array.get h1 a ! middle \<le> ?pivot")
    case True
    with rs_equals have rs_equals: "rs = middle + 1" by simp
    { 
      fix i
      assume i_is_left: "l \<le> i \<and> i < rs"
      with swap_length_remains in_bounds middle_in_bounds rs_equals `l < r`
      have i_props: "i < Array.length h' a" "i \<noteq> r" "i \<noteq> rs" by auto
      from i_is_left rs_equals have "l \<le> i \<and> i < middle \<or> i = middle" by arith
      with part_partitions[OF part] right_remains True
      have "Array.get h1 a ! i \<le> Array.get h' a ! rs" by fastforce
      with i_props h'_def in_bounds have "Array.get h' a ! i \<le> Array.get h' a ! rs"
        unfolding Array.update_def Array.length_def by simp
    }
    moreover
    {
      fix i
      assume "rs < i \<and> i \<le> r"

      hence "(rs < i \<and> i \<le> r - 1) \<or> (rs < i \<and> i = r)" by arith
      hence "Array.get h' a ! rs \<le> Array.get h' a ! i"
      proof
        assume i_is: "rs < i \<and> i \<le> r - 1"
        with swap_length_remains in_bounds middle_in_bounds rs_equals
        have i_props: "i < Array.length h' a" "i \<noteq> r" "i \<noteq> rs" by auto
        from part_partitions[OF part] rs_equals right_remains i_is
        have "Array.get h' a ! rs \<le> Array.get h1 a ! i"
          by fastforce
        with i_props h'_def show ?thesis by fastforce
      next
        assume i_is: "rs < i \<and> i = r"
        with rs_equals have "Suc middle \<noteq> r" by arith
        with middle_in_bounds `l < r` have "Suc middle \<le> r - 1" by arith
        with part_partitions[OF part] right_remains 
        have "Array.get h' a ! rs \<le> Array.get h1 a ! (Suc middle)"
          by fastforce
        with i_is True rs_equals right_remains h'_def
        show ?thesis using in_bounds
          unfolding Array.update_def Array.length_def
          by auto
      qed
    }
    ultimately show ?thesis by auto
  next
    case False
    with rs_equals have rs_equals: "middle = rs" by simp
    { 
      fix i
      assume i_is_left: "l \<le> i \<and> i < rs"
      with swap_length_remains in_bounds middle_in_bounds rs_equals
      have i_props: "i < Array.length h' a" "i \<noteq> r" "i \<noteq> rs" by auto
      from part_partitions[OF part] rs_equals right_remains i_is_left
      have "Array.get h1 a ! i \<le> Array.get h' a ! rs" by fastforce
      with i_props h'_def have "Array.get h' a ! i \<le> Array.get h' a ! rs"
        unfolding Array.update_def by simp
    }
    moreover
    {
      fix i
      assume "rs < i \<and> i \<le> r"
      hence "(rs < i \<and> i \<le> r - 1) \<or> i = r" by arith
      hence "Array.get h' a ! rs \<le> Array.get h' a ! i"
      proof
        assume i_is: "rs < i \<and> i \<le> r - 1"
        with swap_length_remains in_bounds middle_in_bounds rs_equals
        have i_props: "i < Array.length h' a" "i \<noteq> r" "i \<noteq> rs" by auto
        from part_partitions[OF part] rs_equals right_remains i_is
        have "Array.get h' a ! rs \<le> Array.get h1 a ! i"
          by fastforce
        with i_props h'_def show ?thesis by fastforce
      next
        assume i_is: "i = r"
        from i_is False rs_equals right_remains h'_def
        show ?thesis using in_bounds
          unfolding Array.update_def Array.length_def
          by auto
      qed
    }
    ultimately
    show ?thesis by auto
  qed
qed


function quicksort :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
where
  "quicksort arr left right =
     (if (right > left)  then
        do {
          pivotNewIndex \<leftarrow> partition arr left right;
          pivotNewIndex \<leftarrow> assert (\<lambda>x. left \<le> x \<and> x \<le> right) pivotNewIndex;
          quicksort arr left (pivotNewIndex - 1);
          quicksort arr (pivotNewIndex + 1) right
        }
     else return ())"
by pat_completeness auto

(* For termination, we must show that the pivotNewIndex is between left and right *) 
termination
by (relation "measure (\<lambda>(a, l, r). (r - l))") auto

declare quicksort.simps[simp del]


lemma quicksort_permutes:
  assumes "effect (quicksort a l r) h h' rs"
  shows "multiset_of (Array.get h' a) 
  = multiset_of (Array.get h a)"
  using assms
proof (induct a l r arbitrary: h h' rs rule: quicksort.induct)
  case (1 a l r h h' rs)
  with partition_permutes show ?case
    unfolding quicksort.simps [of a l r]
    by (elim effect_ifE effect_bindE effect_assertE effect_returnE) auto
qed

lemma length_remains:
  assumes "effect (quicksort a l r) h h' rs"
  shows "Array.length h a = Array.length h' a"
using assms
proof (induct a l r arbitrary: h h' rs rule: quicksort.induct)
  case (1 a l r h h' rs)
  with partition_length_remains show ?case
    unfolding quicksort.simps [of a l r]
    by (elim effect_ifE effect_bindE effect_assertE effect_returnE) auto
qed

lemma quicksort_outer_remains:
  assumes "effect (quicksort a l r) h h' rs"
   shows "\<forall>i. i < l \<or> r < i \<longrightarrow> Array.get h (a::nat array) ! i = Array.get h' a ! i"
  using assms
proof (induct a l r arbitrary: h h' rs rule: quicksort.induct)
  case (1 a l r h h' rs)
  note cr = `effect (quicksort a l r) h h' rs`
  thus ?case
  proof (cases "r > l")
    case False
    with cr have "h' = h"
      unfolding quicksort.simps [of a l r]
      by (elim effect_ifE effect_returnE) auto
    thus ?thesis by simp
  next
  case True
   { 
      fix h1 h2 p ret1 ret2 i
      assume part: "effect (partition a l r) h h1 p"
      assume qs1: "effect (quicksort a l (p - 1)) h1 h2 ret1"
      assume qs2: "effect (quicksort a (p + 1) r) h2 h' ret2"
      assume pivot: "l \<le> p \<and> p \<le> r"
      assume i_outer: "i < l \<or> r < i"
      from  partition_outer_remains [OF part True] i_outer
      have "Array.get h a !i = Array.get h1 a ! i" by fastforce
      moreover
      with 1(1) [OF True pivot qs1] pivot i_outer
      have "Array.get h1 a ! i = Array.get h2 a ! i" by auto
      moreover
      with qs2 1(2) [of p h2 h' ret2] True pivot i_outer
      have "Array.get h2 a ! i = Array.get h' a ! i" by auto
      ultimately have "Array.get h a ! i= Array.get h' a ! i" by simp
    }
    with cr show ?thesis
      unfolding quicksort.simps [of a l r]
      by (elim effect_ifE effect_bindE effect_assertE effect_returnE) auto
  qed
qed

lemma quicksort_is_skip:
  assumes "effect (quicksort a l r) h h' rs"
  shows "r \<le> l \<longrightarrow> h = h'"
  using assms
  unfolding quicksort.simps [of a l r]
  by (elim effect_ifE effect_returnE) auto
 
lemma quicksort_sorts:
  assumes "effect (quicksort a l r) h h' rs"
  assumes l_r_length: "l < Array.length h a" "r < Array.length h a" 
  shows "sorted (subarray l (r + 1) a h')"
  using assms
proof (induct a l r arbitrary: h h' rs rule: quicksort.induct)
  case (1 a l r h h' rs)
  note cr = `effect (quicksort a l r) h h' rs`
  thus ?case
  proof (cases "r > l")
    case False
    hence "l \<ge> r + 1 \<or> l = r" by arith 
    with length_remains[OF cr] 1(5) show ?thesis
      by (auto simp add: subarray_Nil subarray_single)
  next
    case True
    { 
      fix h1 h2 p
      assume part: "effect (partition a l r) h h1 p"
      assume qs1: "effect (quicksort a l (p - 1)) h1 h2 ()"
      assume qs2: "effect (quicksort a (p + 1) r) h2 h' ()"
      from partition_returns_index_in_bounds [OF part True]
      have pivot: "l\<le> p \<and> p \<le> r" .
     note length_remains = length_remains[OF qs2] length_remains[OF qs1] partition_length_remains[OF part]
      from quicksort_outer_remains [OF qs2] quicksort_outer_remains [OF qs1] pivot quicksort_is_skip[OF qs1]
      have pivot_unchanged: "Array.get h1 a ! p = Array.get h' a ! p" by (cases p, auto)
        (*-- First of all, by induction hypothesis both sublists are sorted. *)
      from 1(1)[OF True pivot qs1] length_remains pivot 1(5) 
      have IH1: "sorted (subarray l p a h2)"  by (cases p, auto simp add: subarray_Nil)
      from quicksort_outer_remains [OF qs2] length_remains
      have left_subarray_remains: "subarray l p a h2 = subarray l p a h'"
        by (simp add: subarray_eq_samelength_iff)
      with IH1 have IH1': "sorted (subarray l p a h')" by simp
      from 1(2)[OF True pivot qs2] pivot 1(5) length_remains
      have IH2: "sorted (subarray (p + 1) (r + 1) a h')"
        by (cases "Suc p \<le> r", auto simp add: subarray_Nil)
           (* -- Secondly, both sublists remain partitioned. *)
      from partition_partitions[OF part True]
      have part_conds1: "\<forall>j. j \<in> set (subarray l p a h1) \<longrightarrow> j \<le> Array.get h1 a ! p "
        and part_conds2: "\<forall>j. j \<in> set (subarray (p + 1) (r + 1) a h1) \<longrightarrow> Array.get h1 a ! p \<le> j"
        by (auto simp add: all_in_set_subarray_conv)
      from quicksort_outer_remains [OF qs1] quicksort_permutes [OF qs1] True
        length_remains 1(5) pivot multiset_of_sublist [of l p "Array.get h1 a" "Array.get h2 a"]
      have multiset_partconds1: "multiset_of (subarray l p a h2) = multiset_of (subarray l p a h1)"
        unfolding Array.length_def subarray_def by (cases p, auto)
      with left_subarray_remains part_conds1 pivot_unchanged
      have part_conds2': "\<forall>j. j \<in> set (subarray l p a h') \<longrightarrow> j \<le> Array.get h' a ! p"
        by (simp, subst set_of_multiset_of[symmetric], simp)
          (* -- These steps are the analogous for the right sublist \<dots> *)
      from quicksort_outer_remains [OF qs1] length_remains
      have right_subarray_remains: "subarray (p + 1) (r + 1) a h1 = subarray (p + 1) (r + 1) a h2"
        by (auto simp add: subarray_eq_samelength_iff)
      from quicksort_outer_remains [OF qs2] quicksort_permutes [OF qs2] True
        length_remains 1(5) pivot multiset_of_sublist [of "p + 1" "r + 1" "Array.get h2 a" "Array.get h' a"]
      have multiset_partconds2: "multiset_of (subarray (p + 1) (r + 1) a h') = multiset_of (subarray (p + 1) (r + 1) a h2)"
        unfolding Array.length_def subarray_def by auto
      with right_subarray_remains part_conds2 pivot_unchanged
      have part_conds1': "\<forall>j. j \<in> set (subarray (p + 1) (r + 1) a h') \<longrightarrow> Array.get h' a ! p \<le> j"
        by (simp, subst set_of_multiset_of[symmetric], simp)
          (* -- Thirdly and finally, we show that the array is sorted
          following from the facts above. *)
      from True pivot 1(5) length_remains have "subarray l (r + 1) a h' = subarray l p a h' @ [Array.get h' a ! p] @ subarray (p + 1) (r + 1) a h'"
        by (simp add: subarray_nth_array_Cons, cases "l < p") (auto simp add: subarray_append subarray_Nil)
      with IH1' IH2 part_conds1' part_conds2' pivot have ?thesis
        unfolding subarray_def
        apply (auto simp add: sorted_append sorted_Cons all_in_set_sublist'_conv)
        by (auto simp add: set_sublist' dest: le_trans [of _ "Array.get h' a ! p"])
    }
    with True cr show ?thesis
      unfolding quicksort.simps [of a l r]
      by (elim effect_ifE effect_returnE effect_bindE effect_assertE) auto
  qed
qed


lemma quicksort_is_sort:
  assumes effect: "effect (quicksort a 0 (Array.length h a - 1)) h h' rs"
  shows "Array.get h' a = sort (Array.get h a)"
proof (cases "Array.get h a = []")
  case True
  with quicksort_is_skip[OF effect] show ?thesis
  unfolding Array.length_def by simp
next
  case False
  from quicksort_sorts [OF effect] False have "sorted (sublist' 0 (List.length (Array.get h a)) (Array.get h' a))"
    unfolding Array.length_def subarray_def by auto
  with length_remains[OF effect] have "sorted (Array.get h' a)"
    unfolding Array.length_def by simp
  with quicksort_permutes [OF effect] properties_for_sort show ?thesis by fastforce
qed

subsection {* No Errors in quicksort *}
text {* We have proved that quicksort sorts (if no exceptions occur).
We will now show that exceptions do not occur. *}

lemma success_part1I: 
  assumes "l < Array.length h a" "r < Array.length h a"
  shows "success (part1 a l r p) h"
  using assms
proof (induct a l r p arbitrary: h rule: part1.induct)
  case (1 a l r p)
  thus ?case unfolding part1.simps [of a l r]
  apply (auto intro!: success_intros simp add: not_le)
  apply (auto intro!: effect_intros)
  done
qed

lemma success_bindI' [success_intros]: (*FIXME move*)
  assumes "success f h"
  assumes "\<And>h' r. effect f h h' r \<Longrightarrow> success (g r) h'"
  shows "success (f \<guillemotright>= g) h"
using assms(1) proof (rule success_effectE)
  fix h' r
  assume "effect f h h' r"
  moreover with assms(2) have "success (g r) h'" .
  ultimately show "success (f \<guillemotright>= g) h" by (rule success_bind_effectI)
qed

lemma success_partitionI:
  assumes "l < r" "l < Array.length h a" "r < Array.length h a"
  shows "success (partition a l r) h"
using assms unfolding partition.simps swap_def
apply (auto intro!: success_bindI' success_ifI success_returnI success_nthI success_updI success_part1I elim!: effect_bindE effect_updE effect_nthE effect_returnE simp add:)
apply (frule part_length_remains)
apply (frule part_returns_index_in_bounds)
apply auto
apply (frule part_length_remains)
apply (frule part_returns_index_in_bounds)
apply auto
apply (frule part_length_remains)
apply auto
done

lemma success_quicksortI:
  assumes "l < Array.length h a" "r < Array.length h a"
  shows "success (quicksort a l r) h"
using assms
proof (induct a l r arbitrary: h rule: quicksort.induct)
  case (1 a l ri h)
  thus ?case
    unfolding quicksort.simps [of a l ri]
    apply (auto intro!: success_ifI success_bindI' success_returnI success_nthI success_updI success_assertI success_partitionI)
    apply (frule partition_returns_index_in_bounds)
    apply auto
    apply (frule partition_returns_index_in_bounds)
    apply auto
    apply (auto elim!: effect_assertE dest!: partition_length_remains length_remains)
    apply (subgoal_tac "Suc r \<le> ri \<or> r = ri") 
    apply (erule disjE)
    apply auto
    unfolding quicksort.simps [of a "Suc ri" ri]
    apply (auto intro!: success_ifI success_returnI)
    done
qed


subsection {* Example *}

definition "qsort a = do {
    k \<leftarrow> Array.len a;
    quicksort a 0 (k - 1);
    return a
  }"

code_reserved SML upto

ML {* @{code qsort} (Array.fromList [42, 2, 3, 5, 0, 1705, 8, 3, 15]) () *}

export_code qsort checking SML SML_imp OCaml? OCaml_imp? Haskell? Scala? Scala_imp?

end
