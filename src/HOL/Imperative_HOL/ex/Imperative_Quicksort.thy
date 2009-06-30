(* Author: Lukas Bulwahn, TU Muenchen *)

theory Imperative_Quicksort
imports "~~/src/HOL/Imperative_HOL/Imperative_HOL" Subarray Multiset Efficient_Nat
begin

text {* We prove QuickSort correct in the Relational Calculus. *}

definition swap :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
where
  "swap arr i j = (
     do
       x \<leftarrow> nth arr i;
       y \<leftarrow> nth arr j;
       upd i y arr;
       upd j x arr;
       return ()
     done)"

lemma swap_permutes:
  assumes "crel (swap a i j) h h' rs"
  shows "multiset_of (get_array a h') 
  = multiset_of (get_array a h)"
  using assms
  unfolding swap_def
  by (auto simp add: Heap.length_def multiset_of_swap dest: sym [of _ "h'"] elim!: crelE crel_nth crel_return crel_upd)

function part1 :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
where
  "part1 a left right p = (
     if (right \<le> left) then return right
     else (do
       v \<leftarrow> nth a left;
       (if (v \<le> p) then (part1 a (left + 1) right p)
                    else (do swap a left right;
  part1 a left (right - 1) p done))
     done))"
by pat_completeness auto

termination
by (relation "measure (\<lambda>(_,l,r,_). r - l )") auto

declare part1.simps[simp del]

lemma part_permutes:
  assumes "crel (part1 a l r p) h h' rs"
  shows "multiset_of (get_array a h') 
  = multiset_of (get_array a h)"
  using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  thus ?case
    unfolding part1.simps [of a l r p]
    by (elim crelE crel_if crel_return crel_nth) (auto simp add: swap_permutes)
qed

lemma part_returns_index_in_bounds:
  assumes "crel (part1 a l r p) h h' rs"
  assumes "l \<le> r"
  shows "l \<le> rs \<and> rs \<le> r"
using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  note cr = `crel (part1 a l r p) h h' rs`
  show ?case
  proof (cases "r \<le> l")
    case True (* Terminating case *)
    with cr `l \<le> r` show ?thesis
      unfolding part1.simps[of a l r p]
      by (elim crelE crel_if crel_return crel_nth) auto
  next
    case False (* recursive case *)
    note rec_condition = this
    let ?v = "get_array a h ! l"
    show ?thesis
    proof (cases "?v \<le> p")
      case True
      with cr False
      have rec1: "crel (part1 a (l + 1) r p) h h' rs"
        unfolding part1.simps[of a l r p]
        by (elim crelE crel_nth crel_if crel_return) auto
      from rec_condition have "l + 1 \<le> r" by arith
      from 1(1)[OF rec_condition True rec1 `l + 1 \<le> r`]
      show ?thesis by simp
    next
      case False
      with rec_condition cr
      obtain h1 where swp: "crel (swap a l r) h h1 ()"
        and rec2: "crel (part1 a l (r - 1) p) h1 h' rs"
        unfolding part1.simps[of a l r p]
        by (elim crelE crel_nth crel_if crel_return) auto
      from rec_condition have "l \<le> r - 1" by arith
      from 1(2) [OF rec_condition False rec2 `l \<le> r - 1`] show ?thesis by fastsimp
    qed
  qed
qed

lemma part_length_remains:
  assumes "crel (part1 a l r p) h h' rs"
  shows "Heap.length a h = Heap.length a h'"
using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  note cr = `crel (part1 a l r p) h h' rs`
  
  show ?case
  proof (cases "r \<le> l")
    case True (* Terminating case *)
    with cr show ?thesis
      unfolding part1.simps[of a l r p]
      by (elim crelE crel_if crel_return crel_nth) auto
  next
    case False (* recursive case *)
    with cr 1 show ?thesis
      unfolding part1.simps [of a l r p] swap_def
      by (auto elim!: crelE crel_if crel_nth crel_return crel_upd) fastsimp
  qed
qed

lemma part_outer_remains:
  assumes "crel (part1 a l r p) h h' rs"
  shows "\<forall>i. i < l \<or> r < i \<longrightarrow> get_array (a::nat array) h ! i = get_array a h' ! i"
  using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  note cr = `crel (part1 a l r p) h h' rs`
  
  show ?case
  proof (cases "r \<le> l")
    case True (* Terminating case *)
    with cr show ?thesis
      unfolding part1.simps[of a l r p]
      by (elim crelE crel_if crel_return crel_nth) auto
  next
    case False (* recursive case *)
    note rec_condition = this
    let ?v = "get_array a h ! l"
    show ?thesis
    proof (cases "?v \<le> p")
      case True
      with cr False
      have rec1: "crel (part1 a (l + 1) r p) h h' rs"
        unfolding part1.simps[of a l r p]
        by (elim crelE crel_nth crel_if crel_return) auto
      from 1(1)[OF rec_condition True rec1]
      show ?thesis by fastsimp
    next
      case False
      with rec_condition cr
      obtain h1 where swp: "crel (swap a l r) h h1 ()"
        and rec2: "crel (part1 a l (r - 1) p) h1 h' rs"
        unfolding part1.simps[of a l r p]
        by (elim crelE crel_nth crel_if crel_return) auto
      from swp rec_condition have
        "\<forall>i. i < l \<or> r < i \<longrightarrow> get_array a h ! i = get_array a h1 ! i"
	unfolding swap_def
	by (elim crelE crel_nth crel_upd crel_return) auto
      with 1(2) [OF rec_condition False rec2] show ?thesis by fastsimp
    qed
  qed
qed


lemma part_partitions:
  assumes "crel (part1 a l r p) h h' rs"
  shows "(\<forall>i. l \<le> i \<and> i < rs \<longrightarrow> get_array (a::nat array) h' ! i \<le> p)
  \<and> (\<forall>i. rs < i \<and> i \<le> r \<longrightarrow> get_array a h' ! i \<ge> p)"
  using assms
proof (induct a l r p arbitrary: h h' rs rule:part1.induct)
  case (1 a l r p h h' rs)
  note cr = `crel (part1 a l r p) h h' rs`
  
  show ?case
  proof (cases "r \<le> l")
    case True (* Terminating case *)
    with cr have "rs = r"
      unfolding part1.simps[of a l r p]
      by (elim crelE crel_if crel_return crel_nth) auto
    with True
    show ?thesis by auto
  next
    case False (* recursive case *)
    note lr = this
    let ?v = "get_array a h ! l"
    show ?thesis
    proof (cases "?v \<le> p")
      case True
      with lr cr
      have rec1: "crel (part1 a (l + 1) r p) h h' rs"
        unfolding part1.simps[of a l r p]
        by (elim crelE crel_nth crel_if crel_return) auto
      from True part_outer_remains[OF rec1] have a_l: "get_array a h' ! l \<le> p"
	by fastsimp
      have "\<forall>i. (l \<le> i = (l = i \<or> Suc l \<le> i))" by arith
      with 1(1)[OF False True rec1] a_l show ?thesis
	by auto
    next
      case False
      with lr cr
      obtain h1 where swp: "crel (swap a l r) h h1 ()"
        and rec2: "crel (part1 a l (r - 1) p) h1 h' rs"
        unfolding part1.simps[of a l r p]
        by (elim crelE crel_nth crel_if crel_return) auto
      from swp False have "get_array a h1 ! r \<ge> p"
	unfolding swap_def
	by (auto simp add: Heap.length_def elim!: crelE crel_nth crel_upd crel_return)
      with part_outer_remains [OF rec2] lr have a_r: "get_array a h' ! r \<ge> p"
	by fastsimp
      have "\<forall>i. (i \<le> r = (i = r \<or> i \<le> r - 1))" by arith
      with 1(2)[OF lr False rec2] a_r show ?thesis
	by auto
    qed
  qed
qed


fun partition :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
where
  "partition a left right = (do
     pivot \<leftarrow> nth a right;
     middle \<leftarrow> part1 a left (right - 1) pivot;
     v \<leftarrow> nth a middle;
     m \<leftarrow> return (if (v \<le> pivot) then (middle + 1) else middle);
     swap a m right;
     return m
   done)"

declare partition.simps[simp del]

lemma partition_permutes:
  assumes "crel (partition a l r) h h' rs"
  shows "multiset_of (get_array a h') 
  = multiset_of (get_array a h)"
proof -
    from assms part_permutes swap_permutes show ?thesis
      unfolding partition.simps
      by (elim crelE crel_return crel_nth crel_if crel_upd) auto
qed

lemma partition_length_remains:
  assumes "crel (partition a l r) h h' rs"
  shows "Heap.length a h = Heap.length a h'"
proof -
  from assms part_length_remains show ?thesis
    unfolding partition.simps swap_def
    by (elim crelE crel_return crel_nth crel_if crel_upd) auto
qed

lemma partition_outer_remains:
  assumes "crel (partition a l r) h h' rs"
  assumes "l < r"
  shows "\<forall>i. i < l \<or> r < i \<longrightarrow> get_array (a::nat array) h ! i = get_array a h' ! i"
proof -
  from assms part_outer_remains part_returns_index_in_bounds show ?thesis
    unfolding partition.simps swap_def
    by (elim crelE crel_return crel_nth crel_if crel_upd) fastsimp
qed

lemma partition_returns_index_in_bounds:
  assumes crel: "crel (partition a l r) h h' rs"
  assumes "l < r"
  shows "l \<le> rs \<and> rs \<le> r"
proof -
  from crel obtain middle h'' p where part: "crel (part1 a l (r - 1) p) h h'' middle"
    and rs_equals: "rs = (if get_array a h'' ! middle \<le> get_array a h ! r then middle + 1
         else middle)"
    unfolding partition.simps
    by (elim crelE crel_return crel_nth crel_if crel_upd) simp
  from `l < r` have "l \<le> r - 1" by arith
  from part_returns_index_in_bounds[OF part this] rs_equals `l < r` show ?thesis by auto
qed

lemma partition_partitions:
  assumes crel: "crel (partition a l r) h h' rs"
  assumes "l < r"
  shows "(\<forall>i. l \<le> i \<and> i < rs \<longrightarrow> get_array (a::nat array) h' ! i \<le> get_array a h' ! rs) \<and>
  (\<forall>i. rs < i \<and> i \<le> r \<longrightarrow> get_array a h' ! rs \<le> get_array a h' ! i)"
proof -
  let ?pivot = "get_array a h ! r" 
  from crel obtain middle h1 where part: "crel (part1 a l (r - 1) ?pivot) h h1 middle"
    and swap: "crel (swap a rs r) h1 h' ()"
    and rs_equals: "rs = (if get_array a h1 ! middle \<le> ?pivot then middle + 1
         else middle)"
    unfolding partition.simps
    by (elim crelE crel_return crel_nth crel_if crel_upd) simp
  from swap have h'_def: "h' = Heap.upd a r (get_array a h1 ! rs)
    (Heap.upd a rs (get_array a h1 ! r) h1)"
    unfolding swap_def
    by (elim crelE crel_return crel_nth crel_upd) simp
  from swap have in_bounds: "r < Heap.length a h1 \<and> rs < Heap.length a h1"
    unfolding swap_def
    by (elim crelE crel_return crel_nth crel_upd) simp
  from swap have swap_length_remains: "Heap.length a h1 = Heap.length a h'"
    unfolding swap_def by (elim crelE crel_return crel_nth crel_upd) auto
  from `l < r` have "l \<le> r - 1" by simp 
  note middle_in_bounds = part_returns_index_in_bounds[OF part this]
  from part_outer_remains[OF part] `l < r`
  have "get_array a h ! r = get_array a h1 ! r"
    by fastsimp
  with swap
  have right_remains: "get_array a h ! r = get_array a h' ! rs"
    unfolding swap_def
    by (auto simp add: Heap.length_def elim!: crelE crel_return crel_nth crel_upd) (cases "r = rs", auto)
  from part_partitions [OF part]
  show ?thesis
  proof (cases "get_array a h1 ! middle \<le> ?pivot")
    case True
    with rs_equals have rs_equals: "rs = middle + 1" by simp
    { 
      fix i
      assume i_is_left: "l \<le> i \<and> i < rs"
      with swap_length_remains in_bounds middle_in_bounds rs_equals `l < r`
      have i_props: "i < Heap.length a h'" "i \<noteq> r" "i \<noteq> rs" by auto
      from i_is_left rs_equals have "l \<le> i \<and> i < middle \<or> i = middle" by arith
      with part_partitions[OF part] right_remains True
      have "get_array a h1 ! i \<le> get_array a h' ! rs" by fastsimp
      with i_props h'_def in_bounds have "get_array a h' ! i \<le> get_array a h' ! rs"
	unfolding Heap.upd_def Heap.length_def by simp
    }
    moreover
    {
      fix i
      assume "rs < i \<and> i \<le> r"

      hence "(rs < i \<and> i \<le> r - 1) \<or> (rs < i \<and> i = r)" by arith
      hence "get_array a h' ! rs \<le> get_array a h' ! i"
      proof
	assume i_is: "rs < i \<and> i \<le> r - 1"
	with swap_length_remains in_bounds middle_in_bounds rs_equals
	have i_props: "i < Heap.length a h'" "i \<noteq> r" "i \<noteq> rs" by auto
	from part_partitions[OF part] rs_equals right_remains i_is
	have "get_array a h' ! rs \<le> get_array a h1 ! i"
	  by fastsimp
	with i_props h'_def show ?thesis by fastsimp
      next
	assume i_is: "rs < i \<and> i = r"
	with rs_equals have "Suc middle \<noteq> r" by arith
	with middle_in_bounds `l < r` have "Suc middle \<le> r - 1" by arith
	with part_partitions[OF part] right_remains 
	have "get_array a h' ! rs \<le> get_array a h1 ! (Suc middle)"
	  by fastsimp
	with i_is True rs_equals right_remains h'_def
	show ?thesis using in_bounds
	  unfolding Heap.upd_def Heap.length_def
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
      have i_props: "i < Heap.length a h'" "i \<noteq> r" "i \<noteq> rs" by auto
      from part_partitions[OF part] rs_equals right_remains i_is_left
      have "get_array a h1 ! i \<le> get_array a h' ! rs" by fastsimp
      with i_props h'_def have "get_array a h' ! i \<le> get_array a h' ! rs"
	unfolding Heap.upd_def by simp
    }
    moreover
    {
      fix i
      assume "rs < i \<and> i \<le> r"
      hence "(rs < i \<and> i \<le> r - 1) \<or> i = r" by arith
      hence "get_array a h' ! rs \<le> get_array a h' ! i"
      proof
	assume i_is: "rs < i \<and> i \<le> r - 1"
	with swap_length_remains in_bounds middle_in_bounds rs_equals
	have i_props: "i < Heap.length a h'" "i \<noteq> r" "i \<noteq> rs" by auto
	from part_partitions[OF part] rs_equals right_remains i_is
	have "get_array a h' ! rs \<le> get_array a h1 ! i"
	  by fastsimp
	with i_props h'_def show ?thesis by fastsimp
      next
	assume i_is: "i = r"
	from i_is False rs_equals right_remains h'_def
	show ?thesis using in_bounds
	  unfolding Heap.upd_def Heap.length_def
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
        do
          pivotNewIndex \<leftarrow> partition arr left right;
          pivotNewIndex \<leftarrow> assert (\<lambda>x. left \<le> x \<and> x \<le> right) pivotNewIndex;
          quicksort arr left (pivotNewIndex - 1);
          quicksort arr (pivotNewIndex + 1) right
        done
     else return ())"
by pat_completeness auto

(* For termination, we must show that the pivotNewIndex is between left and right *) 
termination
by (relation "measure (\<lambda>(a, l, r). (r - l))") auto

declare quicksort.simps[simp del]


lemma quicksort_permutes:
  assumes "crel (quicksort a l r) h h' rs"
  shows "multiset_of (get_array a h') 
  = multiset_of (get_array a h)"
  using assms
proof (induct a l r arbitrary: h h' rs rule: quicksort.induct)
  case (1 a l r h h' rs)
  with partition_permutes show ?case
    unfolding quicksort.simps [of a l r]
    by (elim crel_if crelE crel_assert crel_return) auto
qed

lemma length_remains:
  assumes "crel (quicksort a l r) h h' rs"
  shows "Heap.length a h = Heap.length a h'"
using assms
proof (induct a l r arbitrary: h h' rs rule: quicksort.induct)
  case (1 a l r h h' rs)
  with partition_length_remains show ?case
    unfolding quicksort.simps [of a l r]
    by (elim crel_if crelE crel_assert crel_return) auto
qed

lemma quicksort_outer_remains:
  assumes "crel (quicksort a l r) h h' rs"
   shows "\<forall>i. i < l \<or> r < i \<longrightarrow> get_array (a::nat array) h ! i = get_array a h' ! i"
  using assms
proof (induct a l r arbitrary: h h' rs rule: quicksort.induct)
  case (1 a l r h h' rs)
  note cr = `crel (quicksort a l r) h h' rs`
  thus ?case
  proof (cases "r > l")
    case False
    with cr have "h' = h"
      unfolding quicksort.simps [of a l r]
      by (elim crel_if crel_return) auto
    thus ?thesis by simp
  next
  case True
   { 
      fix h1 h2 p ret1 ret2 i
      assume part: "crel (partition a l r) h h1 p"
      assume qs1: "crel (quicksort a l (p - 1)) h1 h2 ret1"
      assume qs2: "crel (quicksort a (p + 1) r) h2 h' ret2"
      assume pivot: "l \<le> p \<and> p \<le> r"
      assume i_outer: "i < l \<or> r < i"
      from  partition_outer_remains [OF part True] i_outer
      have "get_array a h !i = get_array a h1 ! i" by fastsimp
      moreover
      with 1(1) [OF True pivot qs1] pivot i_outer
      have "get_array a h1 ! i = get_array a h2 ! i" by auto
      moreover
      with qs2 1(2) [of p h2 h' ret2] True pivot i_outer
      have "get_array a h2 ! i = get_array a h' ! i" by auto
      ultimately have "get_array a h ! i= get_array a h' ! i" by simp
    }
    with cr show ?thesis
      unfolding quicksort.simps [of a l r]
      by (elim crel_if crelE crel_assert crel_return) auto
  qed
qed

lemma quicksort_is_skip:
  assumes "crel (quicksort a l r) h h' rs"
  shows "r \<le> l \<longrightarrow> h = h'"
  using assms
  unfolding quicksort.simps [of a l r]
  by (elim crel_if crel_return) auto
 
lemma quicksort_sorts:
  assumes "crel (quicksort a l r) h h' rs"
  assumes l_r_length: "l < Heap.length a h" "r < Heap.length a h" 
  shows "sorted (subarray l (r + 1) a h')"
  using assms
proof (induct a l r arbitrary: h h' rs rule: quicksort.induct)
  case (1 a l r h h' rs)
  note cr = `crel (quicksort a l r) h h' rs`
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
      assume part: "crel (partition a l r) h h1 p"
      assume qs1: "crel (quicksort a l (p - 1)) h1 h2 ()"
      assume qs2: "crel (quicksort a (p + 1) r) h2 h' ()"
      from partition_returns_index_in_bounds [OF part True]
      have pivot: "l\<le> p \<and> p \<le> r" .
     note length_remains = length_remains[OF qs2] length_remains[OF qs1] partition_length_remains[OF part]
      from quicksort_outer_remains [OF qs2] quicksort_outer_remains [OF qs1] pivot quicksort_is_skip[OF qs1]
      have pivot_unchanged: "get_array a h1 ! p = get_array a h' ! p" by (cases p, auto)
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
      have part_conds1: "\<forall>j. j \<in> set (subarray l p a h1) \<longrightarrow> j \<le> get_array a h1 ! p "
        and part_conds2: "\<forall>j. j \<in> set (subarray (p + 1) (r + 1) a h1) \<longrightarrow> get_array a h1 ! p \<le> j"
        by (auto simp add: all_in_set_subarray_conv)
      from quicksort_outer_remains [OF qs1] quicksort_permutes [OF qs1] True
        length_remains 1(5) pivot multiset_of_sublist [of l p "get_array a h1" "get_array a h2"]
      have multiset_partconds1: "multiset_of (subarray l p a h2) = multiset_of (subarray l p a h1)"
	unfolding Heap.length_def subarray_def by (cases p, auto)
      with left_subarray_remains part_conds1 pivot_unchanged
      have part_conds2': "\<forall>j. j \<in> set (subarray l p a h') \<longrightarrow> j \<le> get_array a h' ! p"
        by (simp, subst set_of_multiset_of[symmetric], simp)
          (* -- These steps are the analogous for the right sublist \<dots> *)
      from quicksort_outer_remains [OF qs1] length_remains
      have right_subarray_remains: "subarray (p + 1) (r + 1) a h1 = subarray (p + 1) (r + 1) a h2"
	by (auto simp add: subarray_eq_samelength_iff)
      from quicksort_outer_remains [OF qs2] quicksort_permutes [OF qs2] True
        length_remains 1(5) pivot multiset_of_sublist [of "p + 1" "r + 1" "get_array a h2" "get_array a h'"]
      have multiset_partconds2: "multiset_of (subarray (p + 1) (r + 1) a h') = multiset_of (subarray (p + 1) (r + 1) a h2)"
        unfolding Heap.length_def subarray_def by auto
      with right_subarray_remains part_conds2 pivot_unchanged
      have part_conds1': "\<forall>j. j \<in> set (subarray (p + 1) (r + 1) a h') \<longrightarrow> get_array a h' ! p \<le> j"
        by (simp, subst set_of_multiset_of[symmetric], simp)
          (* -- Thirdly and finally, we show that the array is sorted
          following from the facts above. *)
      from True pivot 1(5) length_remains have "subarray l (r + 1) a h' = subarray l p a h' @ [get_array a h' ! p] @ subarray (p + 1) (r + 1) a h'"
	by (simp add: subarray_nth_array_Cons, cases "l < p") (auto simp add: subarray_append subarray_Nil)
      with IH1' IH2 part_conds1' part_conds2' pivot have ?thesis
	unfolding subarray_def
	apply (auto simp add: sorted_append sorted_Cons all_in_set_sublist'_conv)
	by (auto simp add: set_sublist' dest: le_trans [of _ "get_array a h' ! p"])
    }
    with True cr show ?thesis
      unfolding quicksort.simps [of a l r]
      by (elim crel_if crel_return crelE crel_assert) auto
  qed
qed


lemma quicksort_is_sort:
  assumes crel: "crel (quicksort a 0 (Heap.length a h - 1)) h h' rs"
  shows "get_array a h' = sort (get_array a h)"
proof (cases "get_array a h = []")
  case True
  with quicksort_is_skip[OF crel] show ?thesis
  unfolding Heap.length_def by simp
next
  case False
  from quicksort_sorts [OF crel] False have "sorted (sublist' 0 (List.length (get_array a h)) (get_array a h'))"
    unfolding Heap.length_def subarray_def by auto
  with length_remains[OF crel] have "sorted (get_array a h')"
    unfolding Heap.length_def by simp
  with quicksort_permutes [OF crel] properties_for_sort show ?thesis by fastsimp
qed

subsection {* No Errors in quicksort *}
text {* We have proved that quicksort sorts (if no exceptions occur).
We will now show that exceptions do not occur. *}

lemma noError_part1: 
  assumes "l < Heap.length a h" "r < Heap.length a h"
  shows "noError (part1 a l r p) h"
  using assms
proof (induct a l r p arbitrary: h rule: part1.induct)
  case (1 a l r p)
  thus ?case
    unfolding part1.simps [of a l r] swap_def
    by (auto intro!: noError_if noErrorI noError_return noError_nth noError_upd elim!: crelE crel_upd crel_nth crel_return)
qed

lemma noError_partition:
  assumes "l < r" "l < Heap.length a h" "r < Heap.length a h"
  shows "noError (partition a l r) h"
using assms
unfolding partition.simps swap_def
apply (auto intro!: noError_if noErrorI noError_return noError_nth noError_upd noError_part1 elim!: crelE crel_upd crel_nth crel_return)
apply (frule part_length_remains)
apply (frule part_returns_index_in_bounds)
apply auto
apply (frule part_length_remains)
apply (frule part_returns_index_in_bounds)
apply auto
apply (frule part_length_remains)
apply auto
done

lemma noError_quicksort:
  assumes "l < Heap.length a h" "r < Heap.length a h"
  shows "noError (quicksort a l r) h"
using assms
proof (induct a l r arbitrary: h rule: quicksort.induct)
  case (1 a l ri h)
  thus ?case
    unfolding quicksort.simps [of a l ri]
    apply (auto intro!: noError_if noErrorI noError_return noError_nth noError_upd noError_assert noError_partition)
    apply (frule partition_returns_index_in_bounds)
    apply auto
    apply (frule partition_returns_index_in_bounds)
    apply auto
    apply (auto elim!: crel_assert dest!: partition_length_remains length_remains)
    apply (subgoal_tac "Suc r \<le> ri \<or> r = ri") 
    apply (erule disjE)
    apply auto
    unfolding quicksort.simps [of a "Suc ri" ri]
    apply (auto intro!: noError_if noError_return)
    done
qed


subsection {* Example *}

definition "qsort a = do
    k \<leftarrow> length a;
    quicksort a 0 (k - 1);
    return a
  done"

ML {* @{code qsort} (Array.fromList [42, 2, 3, 5, 0, 1705, 8, 3, 15]) () *}

(*export_code qsort in SML_imp module_name QSort*)
export_code qsort in OCaml module_name QSort file -
(*export_code qsort in OCaml_imp module_name QSort file -*)
export_code qsort in Haskell module_name QSort file -

end