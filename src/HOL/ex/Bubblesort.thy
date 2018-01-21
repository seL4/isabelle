(* Author: Tobias Nipkow *)

section \<open>Bubblesort\<close>

theory Bubblesort
imports "HOL-Library.Multiset"
begin

text\<open>This is \emph{a} version of bubblesort.\<close>

context linorder
begin

fun bubble_min where
"bubble_min [] = []" |
"bubble_min [x] = [x]" |
"bubble_min (x#xs) =
  (case bubble_min xs of y#ys \<Rightarrow> if x>y then y#x#ys else x#y#ys)"

lemma size_bubble_min: "size(bubble_min xs) = size xs"
by(induction xs rule: bubble_min.induct) (auto split: list.split)

lemma bubble_min_eq_Nil_iff[simp]: "bubble_min xs = [] \<longleftrightarrow> xs = []"
by (metis length_0_conv size_bubble_min)

lemma bubble_minD_size: "bubble_min (xs) = ys \<Longrightarrow> size xs = size ys"
by(auto simp: size_bubble_min)

function (sequential) bubblesort where
"bubblesort []  = []" |
"bubblesort [x] = [x]" |
"bubblesort xs  = (case bubble_min xs of y#ys \<Rightarrow> y # bubblesort ys)"
by pat_completeness auto

termination
proof
  show "wf(measure size)" by simp
next
  fix x1 x2 y :: 'a fix xs ys :: "'a list"
  show "bubble_min(x1#x2#xs) = y#ys \<Longrightarrow> (ys, x1#x2#xs) \<in> measure size"
    by(auto simp: size_bubble_min dest!: bubble_minD_size split: list.splits if_splits)
qed

lemma mset_bubble_min: "mset (bubble_min xs) = mset xs"
apply(induction xs rule: bubble_min.induct)
  apply simp
 apply simp
apply (auto split: list.split)
done

lemma bubble_minD_mset:
  "bubble_min (xs) = ys \<Longrightarrow> mset xs = mset ys"
by(auto simp: mset_bubble_min)

lemma mset_bubblesort:
  "mset (bubblesort xs) = mset xs"
apply(induction xs rule: bubblesort.induct)
  apply simp
 apply simp
by(auto split: list.splits if_splits dest: bubble_minD_mset)

lemma set_bubblesort: "set (bubblesort xs) = set xs"
by(rule mset_bubblesort[THEN mset_eq_setD])

lemma bubble_min_min: "bubble_min xs = y#ys \<Longrightarrow> z \<in> set ys \<Longrightarrow> y \<le> z"
apply(induction xs arbitrary: y ys z rule: bubble_min.induct)
  apply simp
 apply simp
apply (fastforce split: list.splits if_splits dest!: sym[of "a#b" for a b])
done

lemma sorted_bubblesort: "sorted(bubblesort xs)"
apply(induction xs rule: bubblesort.induct)
  apply simp
 apply simp
apply (fastforce simp: set_bubblesort sorted_Cons split: list.split if_splits dest: bubble_min_min)
done

end

end
