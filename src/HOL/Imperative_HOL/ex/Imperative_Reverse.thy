theory Imperative_Reverse
imports "~~/src/HOL/Imperative_HOL/Imperative_HOL" Subarray
begin

hide (open) const swap rev

fun swap :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "swap a i j = (do
     x \<leftarrow> nth a i;
     y \<leftarrow> nth a j;
     upd i y a;
     upd j x a;
     return ()
   done)"

fun rev :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "rev a i j = (if (i < j) then (do
     swap a i j;
     rev a (i + 1) (j - 1)
   done)
   else return ())"

notation (output) swap ("swap")
notation (output) rev ("rev")

declare swap.simps [simp del] rev.simps [simp del]

lemma swap_pointwise: assumes "crel (swap a i j) h h' r"
  shows "get_array a h' ! k = (if k = i then get_array a h ! j
      else if k = j then get_array a h ! i
      else get_array a h ! k)"
using assms unfolding swap.simps
by (elim crel_elim_all)
 (auto simp: Heap.length_def)

lemma rev_pointwise: assumes "crel (rev a i j) h h' r"
  shows "get_array a h' ! k = (if k < i then get_array a h ! k
      else if j < k then get_array a h ! k
      else get_array a h ! (j - (k - i)))" (is "?P a i j h h'")
using assms proof (induct a i j arbitrary: h h' rule: rev.induct)
  case (1 a i j h h'')
  thus ?case
  proof (cases "i < j")
    case True
    with 1[unfolded rev.simps[of a i j]]
    obtain h' where
      swp: "crel (swap a i j) h h' ()"
      and rev: "crel (rev a (i + 1) (j - 1)) h' h'' ()"
      by (auto elim: crel_elim_all)
    from rev 1 True
    have eq: "?P a (i + 1) (j - 1) h' h''" by auto

    have "k < i \<or> i = k \<or> (i < k \<and> k < j) \<or> j = k \<or> j < k" by arith
    with True show ?thesis
      by (elim disjE) (auto simp: eq swap_pointwise[OF swp])
  next
    case False
    with 1[unfolded rev.simps[of a i j]]
    show ?thesis
      by (cases "k = j") (auto elim: crel_elim_all)
  qed
qed

lemma rev_length:
  assumes "crel (rev a i j) h h' r"
  shows "Heap.length a h = Heap.length a h'"
using assms
proof (induct a i j arbitrary: h h' rule: rev.induct)
  case (1 a i j h h'')
  thus ?case
  proof (cases "i < j")
    case True
    with 1[unfolded rev.simps[of a i j]]
    obtain h' where
      swp: "crel (swap a i j) h h' ()"
      and rev: "crel (rev a (i + 1) (j - 1)) h' h'' ()"
      by (auto elim: crel_elim_all)
    from swp rev 1 True show ?thesis
      unfolding swap.simps
      by (elim crel_elim_all) fastsimp
  next
    case False
    with 1[unfolded rev.simps[of a i j]]
    show ?thesis
      by (auto elim: crel_elim_all)
  qed
qed

lemma rev2_rev': assumes "crel (rev a i j) h h' u"
  assumes "j < Heap.length a h"
  shows "subarray i (j + 1) a h' = List.rev (subarray i (j + 1) a h)"
proof - 
  {
    fix k
    assume "k < Suc j - i"
    with rev_pointwise[OF assms(1)] have "get_array a h' ! (i + k) = get_array a h ! (j - k)"
      by auto
  } 
  with assms(2) rev_length[OF assms(1)] show ?thesis
  unfolding subarray_def Heap.length_def
  by (auto simp add: length_sublist' rev_nth min_def nth_sublist' intro!: nth_equalityI)
qed

lemma rev2_rev: 
  assumes "crel (rev a 0 (Heap.length a h - 1)) h h' u"
  shows "get_array a h' = List.rev (get_array a h)"
  using rev2_rev'[OF assms] rev_length[OF assms] assms
    by (cases "Heap.length a h = 0", auto simp add: Heap.length_def
      subarray_def sublist'_all rev.simps[where j=0] elim!: crel_elim_all)
  (drule sym[of "List.length (get_array a h)"], simp)

end
