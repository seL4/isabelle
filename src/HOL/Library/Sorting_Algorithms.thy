(*  Title:      HOL/Library/Sorting_Algorithms.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Sorting_Algorithms
  imports Main Multiset Comparator
begin

section \<open>Stably sorted lists\<close>

abbreviation (input) stable_segment :: \<open>'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  where \<open>stable_segment cmp x \<equiv> filter (\<lambda>y. compare cmp x y = Equiv)\<close>

fun sorted :: \<open>'a comparator \<Rightarrow> 'a list \<Rightarrow> bool\<close>
  where sorted_Nil: \<open>sorted cmp [] \<longleftrightarrow> True\<close>
  | sorted_single: \<open>sorted cmp [x] \<longleftrightarrow> True\<close>
  | sorted_rec: \<open>sorted cmp (y # x # xs) \<longleftrightarrow> compare cmp y x \<noteq> Greater \<and> sorted cmp (x # xs)\<close>

lemma sorted_ConsI:
  \<open>sorted cmp (x # xs)\<close> if \<open>sorted cmp xs\<close>
    and \<open>\<And>y ys. xs = y # ys \<Longrightarrow> compare cmp x y \<noteq> Greater\<close>
  using that by (cases xs) simp_all

lemma sorted_Cons_imp_sorted:
  \<open>sorted cmp xs\<close> if \<open>sorted cmp (x # xs)\<close>
  using that by (cases xs) simp_all

lemma sorted_Cons_imp_not_less:
  \<open>compare cmp y x \<noteq> Greater\<close> if \<open>sorted cmp (y # xs)\<close>
    and \<open>x \<in> set xs\<close>
  using that by (induction xs arbitrary: y) (auto dest: compare.trans_not_greater)

lemma sorted_induct [consumes 1, case_names Nil Cons, induct pred: sorted]:
  \<open>P xs\<close> if \<open>sorted cmp xs\<close> and \<open>P []\<close>
    and *: \<open>\<And>x xs. sorted cmp xs \<Longrightarrow> P xs
      \<Longrightarrow> (\<And>y. y \<in> set xs \<Longrightarrow> compare cmp x y \<noteq> Greater) \<Longrightarrow> P (x # xs)\<close>
using \<open>sorted cmp xs\<close> proof (induction xs)
  case Nil
  show ?case
    by (rule \<open>P []\<close>)
next
  case (Cons x xs)
  from \<open>sorted cmp (x # xs)\<close> have \<open>sorted cmp xs\<close>
    by (cases xs) simp_all
  moreover have \<open>P xs\<close> using \<open>sorted cmp xs\<close>
    by (rule Cons.IH)
  moreover have \<open>compare cmp x y \<noteq> Greater\<close> if \<open>y \<in> set xs\<close> for y
  using that \<open>sorted cmp (x # xs)\<close> proof (induction xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons z zs)
    then show ?case
    proof (cases zs)
      case Nil
      with Cons.prems show ?thesis
        by simp
    next
      case (Cons w ws)
      with Cons.prems have \<open>compare cmp z w \<noteq> Greater\<close> \<open>compare cmp x z \<noteq> Greater\<close>
        by auto
      then have \<open>compare cmp x w \<noteq> Greater\<close>
        by (auto dest: compare.trans_not_greater)
      with Cons show ?thesis
        using Cons.prems Cons.IH by auto
    qed
  qed
  ultimately show ?case
    by (rule *)
qed

lemma sorted_induct_remove1 [consumes 1, case_names Nil minimum]:
  \<open>P xs\<close> if \<open>sorted cmp xs\<close> and \<open>P []\<close>
    and *: \<open>\<And>x xs. sorted cmp xs \<Longrightarrow> P (remove1 x xs)
      \<Longrightarrow> x \<in> set xs \<Longrightarrow> hd (stable_segment cmp x xs) = x \<Longrightarrow> (\<And>y. y \<in> set xs \<Longrightarrow> compare cmp x y \<noteq> Greater)
    \<Longrightarrow> P xs\<close>
using \<open>sorted cmp xs\<close> proof (induction xs)
  case Nil
  show ?case
    by (rule \<open>P []\<close>)
next
  case (Cons x xs)
  then have \<open>sorted cmp (x # xs)\<close>
    by (simp add: sorted_ConsI)
  moreover note Cons.IH
  moreover have \<open>\<And>y. compare cmp x y = Greater \<Longrightarrow> y \<in> set xs \<Longrightarrow> False\<close>
    using Cons.hyps by simp
  ultimately show ?case
    by (auto intro!: * [of \<open>x # xs\<close> x]) blast
qed

lemma sorted_remove1:
  \<open>sorted cmp (remove1 x xs)\<close> if \<open>sorted cmp xs\<close>
proof (cases \<open>x \<in> set xs\<close>)
  case False
  with that show ?thesis
    by (simp add: remove1_idem)
next
  case True
  with that show ?thesis proof (induction xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons y ys)
    show ?case proof (cases \<open>x = y\<close>)
      case True
      with Cons.hyps show ?thesis
        by simp
    next
      case False
      then have \<open>sorted cmp (remove1 x ys)\<close>
        using Cons.IH Cons.prems by auto
      then have \<open>sorted cmp (y # remove1 x ys)\<close>
      proof (rule sorted_ConsI)
        fix z zs
        assume \<open>remove1 x ys = z # zs\<close>
        with \<open>x \<noteq> y\<close> have \<open>z \<in> set ys\<close>
          using notin_set_remove1 [of z ys x] by auto
        then show \<open>compare cmp y z \<noteq> Greater\<close>
          by (rule Cons.hyps(2))
      qed
      with False show ?thesis
        by simp
    qed
  qed
qed

lemma sorted_stable_segment:
  \<open>sorted cmp (stable_segment cmp x xs)\<close>
proof (induction xs)
  case Nil
  show ?case
    by simp
next
  case (Cons y ys)
  then show ?case
    by (auto intro!: sorted_ConsI simp add: filter_eq_Cons_iff compare.sym)
      (auto dest: compare.trans_equiv simp add: compare.sym compare.greater_iff_sym_less)

qed

primrec insort :: \<open>'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  where \<open>insort cmp y [] = [y]\<close>
  | \<open>insort cmp y (x # xs) = (if compare cmp y x \<noteq> Greater
       then y # x # xs
       else x # insort cmp y xs)\<close>

lemma mset_insort [simp]:
  \<open>mset (insort cmp x xs) = add_mset x (mset xs)\<close>
  by (induction xs) simp_all

lemma length_insort [simp]:
  \<open>length (insort cmp x xs) = Suc (length xs)\<close>
  by (induction xs) simp_all

lemma sorted_insort:
  \<open>sorted cmp (insort cmp x xs)\<close> if \<open>sorted cmp xs\<close>
using that proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  then show ?case by (cases ys)
    (auto, simp_all add: compare.greater_iff_sym_less)
qed

lemma stable_insort_equiv:
  \<open>stable_segment cmp y (insort cmp x xs) = x # stable_segment cmp y xs\<close>
    if \<open>compare cmp y x = Equiv\<close>
proof (induction xs)
  case Nil
  from that show ?case
    by simp
next
  case (Cons z xs)
  moreover from that have \<open>compare cmp y z = Equiv \<Longrightarrow> compare cmp z x = Equiv\<close>
    by (auto intro: compare.trans_equiv simp add: compare.sym)
  ultimately show ?case
    using that by (auto simp add: compare.greater_iff_sym_less)
qed

lemma stable_insort_not_equiv:
  \<open>stable_segment cmp y (insort cmp x xs) = stable_segment cmp y xs\<close>
    if \<open>compare cmp y x \<noteq> Equiv\<close>
  using that by (induction xs) simp_all

lemma remove1_insort_same_eq [simp]:
  \<open>remove1 x (insort cmp x xs) = xs\<close>
  by (induction xs) simp_all

lemma insort_eq_ConsI:
  \<open>insort cmp x xs = x # xs\<close>
    if \<open>sorted cmp xs\<close> \<open>\<And>y. y \<in> set xs \<Longrightarrow> compare cmp x y \<noteq> Greater\<close>
  using that by (induction xs) (simp_all add: compare.greater_iff_sym_less)

lemma remove1_insort_not_same_eq [simp]:
  \<open>remove1 y (insort cmp x xs) = insort cmp x (remove1 y xs)\<close>
    if \<open>sorted cmp xs\<close> \<open>x \<noteq> y\<close>
using that proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons z zs)
  show ?case
  proof (cases \<open>compare cmp x z = Greater\<close>)
    case True
    with Cons show ?thesis
      by simp
  next
    case False
    then have \<open>compare cmp x y \<noteq> Greater\<close> if \<open>y \<in> set zs\<close> for y
      using that Cons.hyps
      by (auto dest: compare.trans_not_greater)
    with Cons show ?thesis
      by (simp add: insort_eq_ConsI)
  qed
qed

lemma insort_remove1_same_eq:
  \<open>insort cmp x (remove1 x xs) = xs\<close>
    if \<open>sorted cmp xs\<close> and \<open>x \<in> set xs\<close> and \<open>hd (stable_segment cmp x xs) = x\<close>
using that proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  then have \<open>compare cmp x y \<noteq> Less\<close>
    by (auto simp add: compare.greater_iff_sym_less)
  then consider \<open>compare cmp x y = Greater\<close> | \<open>compare cmp x y = Equiv\<close>
    by (cases \<open>compare cmp x y\<close>) auto
  then show ?case proof cases
    case 1
    with Cons.prems Cons.IH show ?thesis
      by auto
  next
    case 2
    with Cons.prems have \<open>x = y\<close>
      by simp
    with Cons.hyps show ?thesis
      by (simp add: insort_eq_ConsI)
  qed
qed

lemma sorted_append_iff:
  \<open>sorted cmp (xs @ ys) \<longleftrightarrow> sorted cmp xs \<and> sorted cmp ys
     \<and> (\<forall>x \<in> set xs. \<forall>y \<in> set ys. compare cmp x y \<noteq> Greater)\<close> (is \<open>?P \<longleftrightarrow> ?R \<and> ?S \<and> ?Q\<close>)
proof
  assume ?P
  have ?R
    using \<open>?P\<close> by (induction xs)
      (auto simp add: sorted_Cons_imp_not_less,
        auto simp add: sorted_Cons_imp_sorted intro: sorted_ConsI)
  moreover have ?S
    using \<open>?P\<close> by (induction xs) (auto dest: sorted_Cons_imp_sorted)
  moreover have ?Q
    using \<open>?P\<close> by (induction xs) (auto simp add: sorted_Cons_imp_not_less,
      simp add: sorted_Cons_imp_sorted)
  ultimately show \<open>?R \<and> ?S \<and> ?Q\<close>
    by simp
next
  assume \<open>?R \<and> ?S \<and> ?Q\<close>
  then have ?R ?S ?Q
    by simp_all
  then show ?P
    by (induction xs)
      (auto simp add: append_eq_Cons_conv intro!: sorted_ConsI)
qed

definition sort :: \<open>'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  where \<open>sort cmp xs = foldr (insort cmp) xs []\<close>

lemma sort_simps [simp]:
  \<open>sort cmp [] = []\<close>
  \<open>sort cmp (x # xs) = insort cmp x (sort cmp xs)\<close>
  by (simp_all add: sort_def)

lemma mset_sort [simp]:
  \<open>mset (sort cmp xs) = mset xs\<close>
  by (induction xs) simp_all

lemma length_sort [simp]:
  \<open>length (sort cmp xs) = length xs\<close>
  by (induction xs) simp_all

lemma sorted_sort [simp]:
  \<open>sorted cmp (sort cmp xs)\<close>
  by (induction xs) (simp_all add: sorted_insort)

lemma stable_sort:
  \<open>stable_segment cmp x (sort cmp xs) = stable_segment cmp x xs\<close>
  by (induction xs) (simp_all add: stable_insort_equiv stable_insort_not_equiv)

lemma sort_remove1_eq [simp]:
  \<open>sort cmp (remove1 x xs) = remove1 x (sort cmp xs)\<close>
  by (induction xs) simp_all

lemma set_insort [simp]:
  \<open>set (insort cmp x xs) = insert x (set xs)\<close>
  by (induction xs) auto

lemma set_sort [simp]:
  \<open>set (sort cmp xs) = set xs\<close>
  by (induction xs) auto

lemma sort_eqI:
  \<open>sort cmp ys = xs\<close>
    if permutation: \<open>mset ys = mset xs\<close>
    and sorted: \<open>sorted cmp xs\<close>
    and stable: \<open>\<And>y. y \<in> set ys \<Longrightarrow>
      stable_segment cmp y ys = stable_segment cmp y xs\<close>
proof -
  have stable': \<open>stable_segment cmp y ys =
    stable_segment cmp y xs\<close> for y
  proof (cases \<open>\<exists>x\<in>set ys. compare cmp y x = Equiv\<close>)
    case True
    then obtain z where \<open>z \<in> set ys\<close> and \<open>compare cmp y z = Equiv\<close>
      by auto
    then have \<open>compare cmp y x = Equiv \<longleftrightarrow> compare cmp z x = Equiv\<close> for x
      by (meson compare.sym compare.trans_equiv)
    moreover have \<open>stable_segment cmp z ys =
      stable_segment cmp z xs\<close>
      using \<open>z \<in> set ys\<close> by (rule stable)
    ultimately show ?thesis
      by simp
  next
    case False
    moreover from permutation have \<open>set ys = set xs\<close>
      by (rule mset_eq_setD)
    ultimately show ?thesis
      by simp
  qed
  show ?thesis
  using sorted permutation stable' proof (induction xs arbitrary: ys rule: sorted_induct_remove1)
    case Nil
    then show ?case
      by simp
  next
    case (minimum x xs)
    from \<open>mset ys = mset xs\<close> have ys: \<open>set ys = set xs\<close>
      by (rule mset_eq_setD)
    then have \<open>compare cmp x y \<noteq> Greater\<close> if \<open>y \<in> set ys\<close> for y
      using that minimum.hyps by simp
    from minimum.prems have stable: \<open>stable_segment cmp x ys = stable_segment cmp x xs\<close>
      by simp
    have \<open>sort cmp (remove1 x ys) = remove1 x xs\<close>
      by (rule minimum.IH) (simp_all add: minimum.prems filter_remove1)
    then have \<open>remove1 x (sort cmp ys) = remove1 x xs\<close>
      by simp
    then have \<open>insort cmp x (remove1 x (sort cmp ys)) =
      insort cmp x (remove1 x xs)\<close>
      by simp
    also from minimum.hyps ys stable have \<open>insort cmp x (remove1 x (sort cmp ys)) = sort cmp ys\<close>
      by (simp add: stable_sort insort_remove1_same_eq)
    also from minimum.hyps have \<open>insort cmp x (remove1 x xs) = xs\<close>
      by (simp add: insort_remove1_same_eq)
    finally show ?case .
  qed
qed

lemma filter_insort:
  \<open>filter P (insort cmp x xs) = insort cmp x (filter P xs)\<close>
    if \<open>sorted cmp xs\<close> and \<open>P x\<close>
  using that by (induction xs)
    (auto simp add: compare.trans_not_greater insort_eq_ConsI)

lemma filter_insort_triv:
  \<open>filter P (insort cmp x xs) = filter P xs\<close>
    if \<open>\<not> P x\<close>
  using that by (induction xs) simp_all

lemma filter_sort:
  \<open>filter P (sort cmp xs) = sort cmp (filter P xs)\<close>
  by (induction xs) (auto simp add: filter_insort filter_insort_triv)


section \<open>Alternative sorting algorithms\<close>

subsection \<open>Quicksort\<close>

definition quicksort :: \<open>'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  where quicksort_is_sort [simp]: \<open>quicksort = sort\<close>

lemma sort_by_quicksort:
  \<open>sort = quicksort\<close>
  by simp

lemma sort_by_quicksort_rec:
  \<open>sort cmp xs = sort cmp [x\<leftarrow>xs. compare cmp x (xs ! (length xs div 2)) = Less]
    @ stable_segment cmp (xs ! (length xs div 2)) xs
    @ sort cmp [x\<leftarrow>xs. compare cmp x (xs ! (length xs div 2)) = Greater]\<close> (is \<open>_ = ?rhs\<close>)
proof (rule sort_eqI)
  show \<open>mset xs = mset ?rhs\<close>
    by (rule multiset_eqI) (auto simp add: compare.sym intro: comp.exhaust)
next
  show \<open>sorted cmp ?rhs\<close>
    by (auto simp add: sorted_append_iff sorted_stable_segment compare.equiv_subst_right dest: compare.trans_greater)
next
  let ?pivot = \<open>xs ! (length xs div 2)\<close>
  fix l
  have \<open>compare cmp x ?pivot = comp \<and> compare cmp l x = Equiv
    \<longleftrightarrow> compare cmp l ?pivot = comp \<and> compare cmp l x = Equiv\<close> for x comp
  proof -
    have \<open>compare cmp x ?pivot = comp \<longleftrightarrow> compare cmp l ?pivot = comp\<close>
      if \<open>compare cmp l x = Equiv\<close>
      using that by (simp add: compare.equiv_subst_left compare.sym)
    then show ?thesis by blast
  qed
  then show \<open>stable_segment cmp l xs = stable_segment cmp l ?rhs\<close>
    by (simp add: stable_sort compare.sym [of _ ?pivot])
      (cases \<open>compare cmp l ?pivot\<close>, simp_all)
qed

context
begin

qualified definition partition :: \<open>'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list\<close>
  where \<open>partition cmp pivot xs =
    ([x \<leftarrow> xs. compare cmp x pivot = Less], stable_segment cmp pivot xs, [x \<leftarrow> xs. compare cmp x pivot = Greater])\<close>

qualified lemma partition_code [code]:
  \<open>partition cmp pivot [] = ([], [], [])\<close>
  \<open>partition cmp pivot (x # xs) =
    (let (lts, eqs, gts) = partition cmp pivot xs
     in case compare cmp x pivot of
       Less \<Rightarrow> (x # lts, eqs, gts)
     | Equiv \<Rightarrow> (lts, x # eqs, gts)
     | Greater \<Rightarrow> (lts, eqs, x # gts))\<close>
  using comp.exhaust by (auto simp add: partition_def Let_def compare.sym [of _ pivot])

lemma quicksort_code [code]:
  \<open>quicksort cmp xs =
    (case xs of
      [] \<Rightarrow> []
    | [x] \<Rightarrow> xs
    | [x, y] \<Rightarrow> (if compare cmp x y \<noteq> Greater then xs else [y, x])
    | _ \<Rightarrow>
        let (lts, eqs, gts) = partition cmp (xs ! (length xs div 2)) xs
        in quicksort cmp lts @ eqs @ quicksort cmp gts)\<close>
proof (cases \<open>length xs \<ge> 3\<close>)
  case False
  then have \<open>length xs \<in> {0, 1, 2}\<close>
    by (auto simp add: not_le le_less less_antisym)
  then consider \<open>xs = []\<close> | x where \<open>xs = [x]\<close> | x y where \<open>xs = [x, y]\<close>
    by (auto simp add: length_Suc_conv numeral_2_eq_2)
  then show ?thesis
    by cases simp_all
next
  case True
  then obtain x y z zs where \<open>xs = x # y # z # zs\<close>
    by (metis le_0_eq length_0_conv length_Cons list.exhaust not_less_eq_eq numeral_3_eq_3)
  moreover have \<open>quicksort cmp xs =
    (let (lts, eqs, gts) = partition cmp (xs ! (length xs div 2)) xs
    in quicksort cmp lts @ eqs @ quicksort cmp gts)\<close>
    using sort_by_quicksort_rec [of cmp xs] by (simp add: partition_def)
  ultimately show ?thesis
    by simp
qed

end


subsection \<open>Mergesort\<close>

definition mergesort :: \<open>'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  where mergesort_is_sort [simp]: \<open>mergesort = sort\<close>

lemma sort_by_mergesort:
  \<open>sort = mergesort\<close>
  by simp

context
  fixes cmp :: \<open>'a comparator\<close>
begin

qualified function merge :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>
  where \<open>merge [] ys = ys\<close>
  | \<open>merge xs [] = xs\<close>
  | \<open>merge (x # xs) (y # ys) = (if compare cmp x y = Greater
      then y # merge (x # xs) ys else x # merge xs (y # ys))\<close>
  by pat_completeness auto

qualified termination by lexicographic_order

lemma mset_merge:
  \<open>mset (merge xs ys) = mset xs + mset ys\<close>
  by (induction xs ys rule: merge.induct) simp_all

lemma merge_eq_Cons_imp:
  \<open>xs \<noteq> [] \<and> z = hd xs \<or> ys \<noteq> [] \<and> z = hd ys\<close>
    if \<open>merge xs ys = z # zs\<close>
  using that by (induction xs ys rule: merge.induct) (auto split: if_splits)

lemma filter_merge:
  \<open>filter P (merge xs ys) = merge (filter P xs) (filter P ys)\<close>
    if \<open>sorted cmp xs\<close> and \<open>sorted cmp ys\<close>
using that proof (induction xs ys rule: merge.induct)
  case (1 ys)
  then show ?case
    by simp
next
  case (2 xs)
  then show ?case
    by simp
next
  case (3 x xs y ys)
  show ?case
  proof (cases \<open>compare cmp x y = Greater\<close>)
    case True
    with 3 have hyp: \<open>filter P (merge (x # xs) ys) =
      merge (filter P (x # xs)) (filter P ys)\<close>
      by (simp add: sorted_Cons_imp_sorted)
    show ?thesis
    proof (cases \<open>\<not> P x \<and> P y\<close>)
      case False
      with \<open>compare cmp x y = Greater\<close> show ?thesis
        by (auto simp add: hyp)
    next
      case True
      from \<open>compare cmp x y = Greater\<close> "3.prems"
      have *: \<open>compare cmp z y = Greater\<close> if \<open>z \<in> set (filter P xs)\<close> for z
        using that by (auto dest: compare.trans_not_greater sorted_Cons_imp_not_less)
      from \<open>compare cmp x y = Greater\<close> show ?thesis
        by (cases \<open>filter P xs\<close>) (simp_all add: hyp *)
    qed
  next
    case False
    with 3 have hyp: \<open>filter P (merge xs (y # ys)) =
      merge (filter P xs) (filter P (y # ys))\<close>
      by (simp add: sorted_Cons_imp_sorted)
    show ?thesis
    proof (cases \<open>P x \<and> \<not> P y\<close>)
      case False
      with \<open>compare cmp x y \<noteq> Greater\<close> show ?thesis
        by (auto simp add: hyp)
    next
      case True
      from \<open>compare cmp x y \<noteq> Greater\<close> "3.prems"
      have *: \<open>compare cmp x z \<noteq> Greater\<close> if \<open>z \<in> set (filter P ys)\<close> for z
        using that by (auto dest: compare.trans_not_greater sorted_Cons_imp_not_less)
      from \<open>compare cmp x y \<noteq> Greater\<close> show ?thesis
        by (cases \<open>filter P ys\<close>) (simp_all add: hyp *)
    qed
  qed
qed

lemma sorted_merge:
  \<open>sorted cmp (merge xs ys)\<close> if \<open>sorted cmp xs\<close> and \<open>sorted cmp ys\<close>
using that proof (induction xs ys rule: merge.induct)
  case (1 ys)
  then show ?case
    by simp
next
  case (2 xs)
  then show ?case
    by simp
next
  case (3 x xs y ys)
  show ?case
  proof (cases \<open>compare cmp x y = Greater\<close>)
    case True
    with 3 have \<open>sorted cmp (merge (x # xs) ys)\<close>
      by (simp add: sorted_Cons_imp_sorted)
    then have \<open>sorted cmp (y # merge (x # xs) ys)\<close>
    proof (rule sorted_ConsI)
      fix z zs
      assume \<open>merge (x # xs) ys = z # zs\<close>
      with 3(4) True show \<open>compare cmp y z \<noteq> Greater\<close>
        by (clarsimp simp add: sorted_Cons_imp_sorted dest!: merge_eq_Cons_imp)
          (auto simp add: compare.asym_greater sorted_Cons_imp_not_less)
    qed
    with True show ?thesis
      by simp
  next
    case False
    with 3 have \<open>sorted cmp (merge xs (y # ys))\<close>
      by (simp add: sorted_Cons_imp_sorted)
    then have \<open>sorted cmp (x # merge xs (y # ys))\<close>
    proof (rule sorted_ConsI)
      fix z zs
      assume \<open>merge xs (y # ys) = z # zs\<close>
      with 3(3) False show \<open>compare cmp x z \<noteq> Greater\<close>
        by (clarsimp simp add: sorted_Cons_imp_sorted dest!: merge_eq_Cons_imp)
          (auto simp add: compare.asym_greater sorted_Cons_imp_not_less)
    qed
    with False show ?thesis
      by simp
  qed
qed

lemma merge_eq_appendI:
  \<open>merge xs ys = xs @ ys\<close>
    if \<open>\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> compare cmp x y \<noteq> Greater\<close>
  using that by (induction xs ys rule: merge.induct) simp_all

lemma merge_stable_segments:
  \<open>merge (stable_segment cmp l xs) (stable_segment cmp l ys) =
     stable_segment cmp l xs @ stable_segment cmp l ys\<close>
  by (rule merge_eq_appendI) (auto dest: compare.trans_equiv_greater)

lemma sort_by_mergesort_rec:
  \<open>sort cmp xs =
    merge (sort cmp (take (length xs div 2) xs))
      (sort cmp (drop (length xs div 2) xs))\<close> (is \<open>_ = ?rhs\<close>)
proof (rule sort_eqI)
  have \<open>mset (take (length xs div 2) xs) + mset (drop (length xs div 2) xs) =
    mset (take (length xs div 2) xs @ drop (length xs div 2) xs)\<close>
    by (simp only: mset_append)
  then show \<open>mset xs = mset ?rhs\<close>
    by (simp add: mset_merge)
next
  show \<open>sorted cmp ?rhs\<close>
    by (simp add: sorted_merge)
next
  fix l
  have \<open>stable_segment cmp l (take (length xs div 2) xs) @ stable_segment cmp l (drop (length xs div 2) xs)
    = stable_segment cmp l xs\<close>
    by (simp only: filter_append [symmetric] append_take_drop_id)
  have \<open>merge (stable_segment cmp l (take (length xs div 2) xs))
    (stable_segment cmp l (drop (length xs div 2) xs)) =
    stable_segment cmp l (take (length xs div 2) xs) @ stable_segment cmp l (drop (length xs div 2) xs)\<close>
    by (rule merge_eq_appendI) (auto simp add: compare.trans_equiv_greater)
  also have \<open>\<dots> = stable_segment cmp l xs\<close>
    by (simp only: filter_append [symmetric] append_take_drop_id)
  finally show \<open>stable_segment cmp l xs = stable_segment cmp l ?rhs\<close>
    by (simp add: stable_sort filter_merge)
qed

lemma mergesort_code [code]:
  \<open>mergesort cmp xs =
    (case xs of
      [] \<Rightarrow> []
    | [x] \<Rightarrow> xs
    | [x, y] \<Rightarrow> (if compare cmp x y \<noteq> Greater then xs else [y, x])
    | _ \<Rightarrow>
        let
          half = length xs div 2;
          ys = take half xs;
          zs = drop half xs
        in merge (mergesort cmp ys) (mergesort cmp zs))\<close>
proof (cases \<open>length xs \<ge> 3\<close>)
  case False
  then have \<open>length xs \<in> {0, 1, 2}\<close>
    by (auto simp add: not_le le_less less_antisym)
  then consider \<open>xs = []\<close> | x where \<open>xs = [x]\<close> | x y where \<open>xs = [x, y]\<close>
    by (auto simp add: length_Suc_conv numeral_2_eq_2)
  then show ?thesis
    by cases simp_all
next
  case True
  then obtain x y z zs where \<open>xs = x # y # z # zs\<close>
    by (metis le_0_eq length_0_conv length_Cons list.exhaust not_less_eq_eq numeral_3_eq_3)
  moreover have \<open>mergesort cmp xs =
    (let
       half = length xs div 2;
       ys = take half xs;
       zs = drop half xs
     in merge (mergesort cmp ys) (mergesort cmp zs))\<close>
    using sort_by_mergesort_rec [of xs] by (simp add: Let_def)
  ultimately show ?thesis
    by simp
qed

end

end
