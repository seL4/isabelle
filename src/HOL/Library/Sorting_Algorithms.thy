(*  Title:      HOL/Library/Sorting_Algorithms.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Sorting_Algorithms
  imports Main Multiset Comparator
begin

text \<open>Prelude\<close>

hide_const (open) sorted insort sort


section \<open>Stably sorted lists\<close>

abbreviation (input) stable_segment :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "stable_segment cmp x \<equiv> filter (\<lambda>y. compare cmp x y = Equiv)"

fun sorted :: "'a comparator \<Rightarrow> 'a list \<Rightarrow> bool"
  where sorted_Nil: "sorted cmp [] \<longleftrightarrow> True"
  | sorted_single: "sorted cmp [x] \<longleftrightarrow> True"
  | sorted_rec: "sorted cmp (y # x # xs) \<longleftrightarrow> compare cmp x y \<noteq> Less \<and> sorted cmp (x # xs)"

lemma sorted_ConsI:
  "sorted cmp (x # xs)" if "sorted cmp xs"
    and "\<And>y ys. xs = y # ys \<Longrightarrow> compare cmp y x \<noteq> Less"
  using that by (cases xs) simp_all

lemma sorted_induct [consumes 1, case_names Nil Cons, induct pred: sorted]:
  "P xs" if "sorted cmp xs" and "P []"
    and *: "\<And>x xs. sorted cmp xs \<Longrightarrow> P xs
      \<Longrightarrow> (\<And>y. y \<in> set xs \<Longrightarrow> compare cmp y x \<noteq> Less) \<Longrightarrow> P (x # xs)"
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
  moreover have "compare cmp y x \<noteq> Less" if "y \<in> set xs" for y
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
      with Cons.prems have "compare cmp w z \<noteq> Less" "compare cmp z x \<noteq> Less"
        by auto
      then have "compare cmp w x \<noteq> Less"
        by (auto dest: compare.trans_not_less)
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
      \<Longrightarrow> x \<in> set xs \<Longrightarrow> hd (stable_segment cmp x xs) = x \<Longrightarrow> (\<And>y. y \<in> set xs \<Longrightarrow> compare cmp y x \<noteq> Less)
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
  moreover have "\<And>y. compare cmp y x = Less \<Longrightarrow> y \<in> set xs \<Longrightarrow> False"
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
        then show "compare cmp z y \<noteq> Less"
          by (rule Cons.hyps(2))
      qed
      with False show ?thesis
        by simp
    qed
  qed
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
    if "sorted cmp xs" "\<And>y. y \<in> set xs \<Longrightarrow> compare cmp y x \<noteq> Less"
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
  proof (cases "compare cmp z x = Less")
    case True
    with Cons show ?thesis
      by (simp add: compare.greater_iff_sym_less)
  next
    case False
    have "compare cmp y x \<noteq> Less" if "y \<in> set zs" for y
      using that False Cons.hyps by (auto dest: compare.trans_not_less)
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
    by auto
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
    then have "compare cmp y x \<noteq> Less" if "y \<in> set ys" for y
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

end
