(*  Title:      HOL/Library/Sorting_Algorithms.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Sorting_Algorithms
  imports Main Multiset Comparator
begin

section \<open>Stably sorted lists\<close>

abbreviation (input) stable_segment :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "stable_segment cmp x \<equiv> filter (\<lambda>y. compare cmp x y = Equiv)"

fun sorted :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> bool"
  where sorted_Nil: "sorted cmp [] \<longleftrightarrow> True"
  | sorted_single: "sorted cmp [x] \<longleftrightarrow> True"
  | sorted_rec: "sorted cmp (y # x # xs) \<longleftrightarrow> compare cmp y x \<noteq> Greater \<and> sorted cmp (x # xs)"

lemma sorted_ConsI:
  "sorted cmp (x # xs)" if "sorted cmp xs"
    and "\<And>y ys. xs = y # ys \<Longrightarrow> compare cmp x y \<noteq> Greater"
  using that by (cases xs) simp_all

lemma sorted_Cons_imp_sorted:
  "sorted cmp xs" if "sorted cmp (x # xs)"
  using that by (cases xs) simp_all

lemma sorted_Cons_imp_not_less:
  "compare cmp y x \<noteq> Greater" if "sorted cmp (y # xs)"
    and "x \<in> set xs"
  using that by (induction xs arbitrary: y) (auto dest: compare.trans_not_greater)

lemma sorted_induct [consumes 1, case_names Nil Cons, induct pred: sorted]:
  "P xs" if "sorted cmp xs" and "P []"
    and *: "\<And>x xs. sorted cmp xs \<Longrightarrow> P xs
      \<Longrightarrow> (\<And>y. y \<in> set xs \<Longrightarrow> compare cmp x y \<noteq> Greater) \<Longrightarrow> P (x # xs)"
using \<open>sorted cmp xs\<close> proof (induction xs)
  case Nil
  show ?case
    by (rule \<open>P []\<close>)
next
  case (Cons x xs)
  from \<open>sorted cmp (x # xs)\<close> have "sorted cmp xs"
    by (cases xs) simp_all
  moreover have "P xs" using \<open>sorted cmp xs\<close>
    by (rule Cons.IH)
  moreover have "compare cmp x y \<noteq> Greater" if "y \<in> set xs" for y
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
      with Cons.prems have "compare cmp z w \<noteq> Greater" "compare cmp x z \<noteq> Greater"
        by auto
      then have "compare cmp x w \<noteq> Greater"
        by (auto dest: compare.trans_not_greater)
      with Cons show ?thesis
        using Cons.prems Cons.IH by auto
    qed
  qed
  ultimately show ?case
    by (rule *)
qed

lemma sorted_induct_remove1 [consumes 1, case_names Nil minimum]:
  "P xs" if "sorted cmp xs" and "P []"
    and *: "\<And>x xs. sorted cmp xs \<Longrightarrow> P (remove1 x xs)
      \<Longrightarrow> x \<in> set xs \<Longrightarrow> hd (stable_segment cmp x xs) = x \<Longrightarrow> (\<And>y. y \<in> set xs \<Longrightarrow> compare cmp x y \<noteq> Greater)
    \<Longrightarrow> P xs"
using \<open>sorted cmp xs\<close> proof (induction xs)
  case Nil
  show ?case
    by (rule \<open>P []\<close>)
next
  case (Cons x xs)
  then have "sorted cmp (x # xs)"
    by (simp add: sorted_ConsI)
  moreover note Cons.IH
  moreover have "\<And>y. compare cmp x y = Greater \<Longrightarrow> y \<in> set xs \<Longrightarrow> False"
    using Cons.hyps by simp
  ultimately show ?case
    by (auto intro!: * [of "x # xs" x]) blast
qed

lemma sorted_remove1:
  "sorted cmp (remove1 x xs)" if "sorted cmp xs"
proof (cases "x \<in> set xs")
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
    show ?case proof (cases "x = y")
      case True
      with Cons.hyps show ?thesis
        by simp
    next
      case False
      then have "sorted cmp (remove1 x ys)"
        using Cons.IH Cons.prems by auto
      then have "sorted cmp (y # remove1 x ys)"
      proof (rule sorted_ConsI)
        fix z zs
        assume "remove1 x ys = z # zs"
        with \<open>x \<noteq> y\<close> have "z \<in> set ys"
          using notin_set_remove1 [of z ys x] by auto
        then show "compare cmp y z \<noteq> Greater"
          by (rule Cons.hyps(2))
      qed
      with False show ?thesis
        by simp
    qed
  qed
qed

lemma sorted_stable_segment:
  "sorted cmp (stable_segment cmp x xs)"
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

primrec insort :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "insort cmp y [] = [y]"
  | "insort cmp y (x # xs) = (if compare cmp y x \<noteq> Greater
       then y # x # xs
       else x # insort cmp y xs)"

lemma mset_insort [simp]:
  "mset (insort cmp x xs) = add_mset x (mset xs)"
  by (induction xs) simp_all

lemma length_insort [simp]:
  "length (insort cmp x xs) = Suc (length xs)"
  by (induction xs) simp_all

lemma sorted_insort:
  "sorted cmp (insort cmp x xs)" if "sorted cmp xs"
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
  "stable_segment cmp y (insort cmp x xs) = x # stable_segment cmp y xs"
    if "compare cmp y x = Equiv"
proof (induction xs)
  case Nil
  from that show ?case
    by simp
next
  case (Cons z xs)
  moreover from that have "compare cmp y z = Equiv \<Longrightarrow> compare cmp z x = Equiv"
    by (auto intro: compare.trans_equiv simp add: compare.sym)
  ultimately show ?case
    using that by (auto simp add: compare.greater_iff_sym_less)
qed

lemma stable_insort_not_equiv:
  "stable_segment cmp y (insort cmp x xs) = stable_segment cmp y xs"
    if "compare cmp y x \<noteq> Equiv"
  using that by (induction xs) simp_all

lemma remove1_insort_same_eq [simp]:
  "remove1 x (insort cmp x xs) = xs"
  by (induction xs) simp_all

lemma insort_eq_ConsI:
  "insort cmp x xs = x # xs"
    if "sorted cmp xs" "\<And>y. y \<in> set xs \<Longrightarrow> compare cmp x y \<noteq> Greater"
  using that by (induction xs) (simp_all add: compare.greater_iff_sym_less)

lemma remove1_insort_not_same_eq [simp]:
  "remove1 y (insort cmp x xs) = insort cmp x (remove1 y xs)"
    if "sorted cmp xs" "x \<noteq> y"
using that proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons z zs)
  show ?case
  proof (cases "compare cmp x z = Greater")
    case True
    with Cons show ?thesis
      by simp
  next
    case False
    then have "compare cmp x y \<noteq> Greater" if "y \<in> set zs" for y
      using that Cons.hyps
      by (auto dest: compare.trans_not_greater)
    with Cons show ?thesis
      by (simp add: insort_eq_ConsI)
  qed
qed

lemma insort_remove1_same_eq:
  "insort cmp x (remove1 x xs) = xs"
    if "sorted cmp xs" and "x \<in> set xs" and "hd (stable_segment cmp x xs) = x"
using that proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  then have "compare cmp x y \<noteq> Less"
    by (auto simp add: compare.greater_iff_sym_less)
  then consider "compare cmp x y = Greater" | "compare cmp x y = Equiv"
    by (cases "compare cmp x y") auto
  then show ?case proof cases
    case 1
    with Cons.prems Cons.IH show ?thesis
      by auto
  next
    case 2
    with Cons.prems have "x = y"
      by simp
    with Cons.hyps show ?thesis
      by (simp add: insort_eq_ConsI)
  qed
qed

lemma sorted_append_iff:
  "sorted cmp (xs @ ys) \<longleftrightarrow> sorted cmp xs \<and> sorted cmp ys
     \<and> (\<forall>x \<in> set xs. \<forall>y \<in> set ys. compare cmp x y \<noteq> Greater)" (is "?P \<longleftrightarrow> ?R \<and> ?S \<and> ?Q")
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
  ultimately show "?R \<and> ?S \<and> ?Q"
    by simp
next
  assume "?R \<and> ?S \<and> ?Q"
  then have ?R ?S ?Q
    by simp_all
  then show ?P
    by (induction xs)
      (auto simp add: append_eq_Cons_conv intro!: sorted_ConsI)
qed

definition sort :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "sort cmp xs = foldr (insort cmp) xs []"

lemma sort_simps [simp]:
  "sort cmp [] = []"
  "sort cmp (x # xs) = insort cmp x (sort cmp xs)"
  by (simp_all add: sort_def)

lemma mset_sort [simp]:
  "mset (sort cmp xs) = mset xs"
  by (induction xs) simp_all

lemma length_sort [simp]:
  "length (sort cmp xs) = length xs"
  by (induction xs) simp_all

lemma sorted_sort [simp]:
  "sorted cmp (sort cmp xs)"
  by (induction xs) (simp_all add: sorted_insort)

lemma stable_sort:
  "stable_segment cmp x (sort cmp xs) = stable_segment cmp x xs"
  by (induction xs) (simp_all add: stable_insort_equiv stable_insort_not_equiv)

lemma sort_remove1_eq [simp]:
  "sort cmp (remove1 x xs) = remove1 x (sort cmp xs)"
  by (induction xs) simp_all

lemma set_insort [simp]:
  "set (insort cmp x xs) = insert x (set xs)"
  by (induction xs) auto

lemma set_sort [simp]:
  "set (sort cmp xs) = set xs"
  by (induction xs) auto

lemma sort_eqI:
  "sort cmp ys = xs"
    if permutation: "mset ys = mset xs"
    and sorted: "sorted cmp xs"
    and stable: "\<And>y. y \<in> set ys \<Longrightarrow>
      stable_segment cmp y ys = stable_segment cmp y xs"
proof -
  have stable': "stable_segment cmp y ys =
    stable_segment cmp y xs" for y
  proof (cases "\<exists>x\<in>set ys. compare cmp y x = Equiv")
    case True
    then obtain z where "z \<in> set ys" and "compare cmp y z = Equiv"
      by auto
    then have "compare cmp y x = Equiv \<longleftrightarrow> compare cmp z x = Equiv" for x
      by (meson compare.sym compare.trans_equiv)
    moreover have "stable_segment cmp z ys =
      stable_segment cmp z xs"
      using \<open>z \<in> set ys\<close> by (rule stable)
    ultimately show ?thesis
      by simp
  next
    case False
    moreover from permutation have "set ys = set xs"
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
    from \<open>mset ys = mset xs\<close> have ys: "set ys = set xs"
      by (rule mset_eq_setD)
    then have "compare cmp x y \<noteq> Greater" if "y \<in> set ys" for y
      using that minimum.hyps by simp
    from minimum.prems have stable: "stable_segment cmp x ys = stable_segment cmp x xs"
      by simp
    have "sort cmp (remove1 x ys) = remove1 x xs"
      by (rule minimum.IH) (simp_all add: minimum.prems filter_remove1)
    then have "remove1 x (sort cmp ys) = remove1 x xs"
      by simp
    then have "insort cmp x (remove1 x (sort cmp ys)) =
      insort cmp x (remove1 x xs)"
      by simp
    also from minimum.hyps ys stable have "insort cmp x (remove1 x (sort cmp ys)) = sort cmp ys"
      by (simp add: stable_sort insort_remove1_same_eq)
    also from minimum.hyps have "insort cmp x (remove1 x xs) = xs"
      by (simp add: insort_remove1_same_eq)
    finally show ?case .
  qed
qed

lemma filter_insort:
  "filter P (insort cmp x xs) = insort cmp x (filter P xs)"
    if "sorted cmp xs" and "P x"
  using that by (induction xs)
    (auto simp add: compare.trans_not_greater insort_eq_ConsI)

lemma filter_insort_triv:
  "filter P (insort cmp x xs) = filter P xs"
    if "\<not> P x"
  using that by (induction xs) simp_all

lemma filter_sort:
  "filter P (sort cmp xs) = sort cmp (filter P xs)"
  by (induction xs) (auto simp add: filter_insort filter_insort_triv)


section \<open>Alternative sorting algorithms\<close>

subsection \<open>Quicksort\<close>

definition quicksort :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where quicksort_is_sort [simp]: "quicksort = sort"

lemma sort_by_quicksort:
  "sort = quicksort"
  by simp

lemma sort_by_quicksort_rec:
  "sort cmp xs = sort cmp [x\<leftarrow>xs. compare cmp x (xs ! (length xs div 2)) = Less]
    @ stable_segment cmp (xs ! (length xs div 2)) xs
    @ sort cmp [x\<leftarrow>xs. compare cmp x (xs ! (length xs div 2)) = Greater]" (is "sort cmp ?lhs = ?rhs")
proof (rule sort_eqI)
  show "mset ?lhs = mset ?rhs"
    by (rule multiset_eqI) (auto simp add: compare.sym intro: comp.exhaust)
next
  show "sorted cmp ?rhs"
    by (auto simp add: sorted_append_iff sorted_stable_segment compare.equiv_subst_right dest: compare.trans_greater)
next
  let ?pivot = "xs ! (length xs div 2)"
  fix l
  assume "l \<in> set xs"
  have "compare cmp x ?pivot = comp \<and> compare cmp l x = Equiv
    \<longleftrightarrow> compare cmp l ?pivot = comp \<and> compare cmp l x = Equiv" for x comp
  proof -
    have "compare cmp x ?pivot = comp \<longleftrightarrow> compare cmp l ?pivot = comp"
      if "compare cmp l x = Equiv"
      using that by (simp add: compare.equiv_subst_left compare.sym)
    then show ?thesis by blast
  qed
  then show "stable_segment cmp l ?lhs = stable_segment cmp l ?rhs"
    by (simp add: stable_sort compare.sym [of _ ?pivot])
      (cases "compare cmp l ?pivot", simp_all)
qed

context
begin

qualified definition partition :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list"
  where "partition cmp pivot xs =
    ([x \<leftarrow> xs. compare cmp x pivot = Less], stable_segment cmp pivot xs, [x \<leftarrow> xs. compare cmp x pivot = Greater])"

qualified lemma partition_code [code]:
  "partition cmp pivot [] = ([], [], [])"
  "partition cmp pivot (x # xs) =
    (let (lts, eqs, gts) = partition cmp pivot xs
     in case compare cmp x pivot of
       Less \<Rightarrow> (x # lts, eqs, gts)
     | Equiv \<Rightarrow> (lts, x # eqs, gts)
     | Greater \<Rightarrow> (lts, eqs, x # gts))"
  using comp.exhaust by (auto simp add: partition_def Let_def compare.sym [of _ pivot])

lemma quicksort_code [code]:
  "quicksort cmp xs =
    (case xs of
      [] \<Rightarrow> []
    | [x] \<Rightarrow> xs
    | [x, y] \<Rightarrow> (if compare cmp x y \<noteq> Greater then xs else [y, x])
    | _ \<Rightarrow>
        let (lts, eqs, gts) = partition cmp (xs ! (length xs div 2)) xs
        in quicksort cmp lts @ eqs @ quicksort cmp gts)"
proof (cases "length xs \<ge> 3")
  case False
  then have "length xs \<le> 2"
    by simp
  then have "length xs = 0 \<or> length xs = 1 \<or> length xs = 2"
    using le_neq_trans less_2_cases by auto
  then consider "xs = []" | x where "xs = [x]" | x y where "xs = [x, y]"
    by (auto simp add: length_Suc_conv numeral_2_eq_2)
  then show ?thesis
    by cases simp_all
next
  case True
  then obtain x y z zs where "xs = x # y # z # zs"
    by (metis le_0_eq length_0_conv length_Cons list.exhaust not_less_eq_eq numeral_3_eq_3)
  moreover have "quicksort cmp xs =
    (let (lts, eqs, gts) = partition cmp (xs ! (length xs div 2)) xs
    in quicksort cmp lts @ eqs @ quicksort cmp gts)"
    using sort_by_quicksort_rec [of cmp xs] by (simp add: partition_def)
  ultimately show ?thesis
    by simp
qed

end

text \<open>Evaluation example\<close>

value "let cmp = key abs (reversed default)
  in quicksort cmp [65, 1705, -2322, 734, 4, (-17::int)]"

end
