(*  Title:      HOL/Library/DAList_Multiset.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

header {* Multisets partially implemented by association lists *}

theory DAList_Multiset
imports Multiset DAList
begin

text {* Delete prexisting code equations *}

lemma [code, code del]:
  "{#} = {#}"
  ..

lemma [code, code del]:
  "single = single"
  ..

lemma [code, code del]:
  "plus = (plus :: 'a multiset \<Rightarrow> _)"
  ..

lemma [code, code del]:
  "minus = (minus :: 'a multiset \<Rightarrow> _)"
  ..

lemma [code, code del]:
  "inf = (inf :: 'a multiset \<Rightarrow> _)"
  ..

lemma [code, code del]:
  "sup = (sup :: 'a multiset \<Rightarrow> _)"
  ..

lemma [code, code del]:
  "image_mset = image_mset"
  ..

lemma [code, code del]:
  "Multiset.filter = Multiset.filter"
  ..

lemma [code, code del]:
  "count = count"
  ..

lemma [code, code del]:
  "mcard = mcard"
  ..

lemma [code, code del]:
  "msetsum = msetsum"
  ..

lemma [code, code del]:
  "msetprod = msetprod"
  ..

lemma [code, code del]:
  "set_of = set_of"
  ..

lemma [code, code del]:
  "sorted_list_of_multiset = sorted_list_of_multiset"
  ..

lemma [code, code del]:
  "ord_multiset_inst.less_eq_multiset = ord_multiset_inst.less_eq_multiset"
  ..

lemma [code, code del]:
  "ord_multiset_inst.less_multiset = ord_multiset_inst.less_multiset"
  ..

lemma [code, code del]:
  "equal_multiset_inst.equal_multiset = equal_multiset_inst.equal_multiset"
  ..


text {* Raw operations on lists *}

definition join_raw :: "('key \<Rightarrow> 'val \<times> 'val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
where
  "join_raw f xs ys = foldr (\<lambda>(k, v). map_default k v (%v'. f k (v', v))) ys xs"

lemma join_raw_Nil [simp]:
  "join_raw f xs [] = xs"
by (simp add: join_raw_def)

lemma join_raw_Cons [simp]:
  "join_raw f xs ((k, v) # ys) = map_default k v (%v'. f k (v', v)) (join_raw f xs ys)"
by (simp add: join_raw_def)

lemma map_of_join_raw:
  assumes "distinct (map fst ys)"
  shows "map_of (join_raw f xs ys) x = (case map_of xs x of None => map_of ys x | Some v =>
    (case map_of ys x of None => Some v | Some v' => Some (f x (v, v'))))"
using assms
apply (induct ys)
apply (auto simp add: map_of_map_default split: option.split)
apply (metis map_of_eq_None_iff option.simps(2) weak_map_of_SomeI)
by (metis Some_eq_map_of_iff map_of_eq_None_iff option.simps(2))

lemma distinct_join_raw:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (join_raw f xs ys))"
using assms
proof (induct ys)
  case (Cons y ys)
  thus ?case by (cases y) (simp add: distinct_map_default)
qed auto

definition
  "subtract_entries_raw xs ys = foldr (%(k, v). AList.map_entry k (%v'. v' - v)) ys xs"

lemma map_of_subtract_entries_raw:
  assumes "distinct (map fst ys)"
  shows "map_of (subtract_entries_raw xs ys) x = (case map_of xs x of None => None | Some v =>
    (case map_of ys x of None => Some v | Some v' => Some (v - v')))"
using assms unfolding subtract_entries_raw_def
apply (induct ys)
apply auto
apply (simp split: option.split)
apply (simp add: map_of_map_entry)
apply (auto split: option.split)
apply (metis map_of_eq_None_iff option.simps(3) option.simps(4))
by (metis map_of_eq_None_iff option.simps(4) option.simps(5))

lemma distinct_subtract_entries_raw:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (subtract_entries_raw xs ys))"
using assms
unfolding subtract_entries_raw_def by (induct ys) (auto simp add: distinct_map_entry)


text {* Operations on alists with distinct keys *}

lift_definition join :: "('a \<Rightarrow> 'b \<times> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist" 
is join_raw
by (simp add: distinct_join_raw)

lift_definition subtract_entries :: "('a, ('b :: minus)) alist \<Rightarrow> ('a, 'b) alist \<Rightarrow> ('a, 'b) alist"
is subtract_entries_raw 
by (simp add: distinct_subtract_entries_raw)


text {* Implementing multisets by means of association lists *}

definition count_of :: "('a \<times> nat) list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count_of xs x = (case map_of xs x of None \<Rightarrow> 0 | Some n \<Rightarrow> n)"

lemma count_of_multiset:
  "count_of xs \<in> multiset"
proof -
  let ?A = "{x::'a. 0 < (case map_of xs x of None \<Rightarrow> 0\<Colon>nat | Some (n\<Colon>nat) \<Rightarrow> n)}"
  have "?A \<subseteq> dom (map_of xs)"
  proof
    fix x
    assume "x \<in> ?A"
    then have "0 < (case map_of xs x of None \<Rightarrow> 0\<Colon>nat | Some (n\<Colon>nat) \<Rightarrow> n)" by simp
    then have "map_of xs x \<noteq> None" by (cases "map_of xs x") auto
    then show "x \<in> dom (map_of xs)" by auto
  qed
  with finite_dom_map_of [of xs] have "finite ?A"
    by (auto intro: finite_subset)
  then show ?thesis
    by (simp add: count_of_def fun_eq_iff multiset_def)
qed

lemma count_simps [simp]:
  "count_of [] = (\<lambda>_. 0)"
  "count_of ((x, n) # xs) = (\<lambda>y. if x = y then n else count_of xs y)"
  by (simp_all add: count_of_def fun_eq_iff)

lemma count_of_empty:
  "x \<notin> fst ` set xs \<Longrightarrow> count_of xs x = 0"
  by (induct xs) (simp_all add: count_of_def)

lemma count_of_filter:
  "count_of (List.filter (P \<circ> fst) xs) x = (if P x then count_of xs x else 0)"
  by (induct xs) auto

lemma count_of_map_default [simp]:
  "count_of (map_default x b (%x. x + b) xs) y = (if x = y then count_of xs x + b else count_of xs y)"
unfolding count_of_def by (simp add: map_of_map_default split: option.split)

lemma count_of_join_raw:
  "distinct (map fst ys) ==> count_of xs x + count_of ys x = count_of (join_raw (%x (x, y). x + y) xs ys) x"
unfolding count_of_def by (simp add: map_of_join_raw split: option.split)

lemma count_of_subtract_entries_raw:
  "distinct (map fst ys) ==> count_of xs x - count_of ys x = count_of (subtract_entries_raw xs ys) x"
unfolding count_of_def by (simp add: map_of_subtract_entries_raw split: option.split)


text {* Code equations for multiset operations *}

definition Bag :: "('a, nat) alist \<Rightarrow> 'a multiset" where
  "Bag xs = Abs_multiset (count_of (DAList.impl_of xs))"

code_datatype Bag

lemma count_Bag [simp, code]:
  "count (Bag xs) = count_of (DAList.impl_of xs)"
  by (simp add: Bag_def count_of_multiset Abs_multiset_inverse)

lemma Mempty_Bag [code]:
  "{#} = Bag (DAList.empty)"
  by (simp add: multiset_eq_iff alist.Alist_inverse DAList.empty_def)

lemma single_Bag [code]:
  "{#x#} = Bag (DAList.update x 1 DAList.empty)"
  by (simp add: multiset_eq_iff alist.Alist_inverse update.rep_eq empty.rep_eq)

lemma union_Bag [code]:
  "Bag xs + Bag ys = Bag (join (\<lambda>x (n1, n2). n1 + n2) xs ys)"
by (rule multiset_eqI) (simp add: count_of_join_raw alist.Alist_inverse distinct_join_raw join_def)

lemma minus_Bag [code]:
  "Bag xs - Bag ys = Bag (subtract_entries xs ys)"
by (rule multiset_eqI)
  (simp add: count_of_subtract_entries_raw alist.Alist_inverse distinct_subtract_entries_raw subtract_entries_def)

lemma filter_Bag [code]:
  "Multiset.filter P (Bag xs) = Bag (DAList.filter (P \<circ> fst) xs)"
by (rule multiset_eqI) (simp add: count_of_filter DAList.filter.rep_eq)


lemma mset_eq [code]: "HOL.equal (m1::'a::equal multiset) m2 \<longleftrightarrow> m1 \<le> m2 \<and> m2 \<le> m1"
by (metis equal_multiset_def eq_iff)

lemma mset_less_eq_Bag [code]:
  "Bag xs \<le> A \<longleftrightarrow> (\<forall>(x, n) \<in> set (DAList.impl_of xs). count_of (DAList.impl_of xs) x \<le> count A x)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (auto simp add: mset_le_def)
next
  assume ?rhs
  show ?lhs
  proof (rule mset_less_eqI)
    fix x
    from `?rhs` have "count_of (DAList.impl_of xs) x \<le> count A x"
      by (cases "x \<in> fst ` set (DAList.impl_of xs)") (auto simp add: count_of_empty)
    then show "count (Bag xs) x \<le> count A x"
      by (simp add: mset_le_def)
  qed
qed

declare multiset_inter_def [code]
declare sup_multiset_def [code]
declare multiset_of.simps [code]

instantiation multiset :: (exhaustive) exhaustive
begin

definition exhaustive_multiset :: "('a multiset \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool * term list) option"
where
  "exhaustive_multiset f i = Quickcheck_Exhaustive.exhaustive (\<lambda>xs. f (Bag xs)) i"

instance ..

end

end

