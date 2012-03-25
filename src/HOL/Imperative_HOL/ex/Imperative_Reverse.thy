(*  Title:      HOL/Imperative_HOL/ex/Imperative_Reverse.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

header {* An imperative in-place reversal on arrays *}

theory Imperative_Reverse
imports Subarray "~~/src/HOL/Imperative_HOL/Imperative_HOL"
begin

fun swap :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "swap a i j = do {
     x \<leftarrow> Array.nth a i;
     y \<leftarrow> Array.nth a j;
     Array.upd i y a;
     Array.upd j x a;
     return ()
   }"

fun rev :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "rev a i j = (if (i < j) then do {
     swap a i j;
     rev a (i + 1) (j - 1)
   }
   else return ())"

declare swap.simps [simp del] rev.simps [simp del]

lemma swap_pointwise: assumes "effect (swap a i j) h h' r"
  shows "Array.get h' a ! k = (if k = i then Array.get h a ! j
      else if k = j then Array.get h a ! i
      else Array.get h a ! k)"
using assms unfolding swap.simps
by (elim effect_elims)
 (auto simp: length_def)

lemma rev_pointwise: assumes "effect (rev a i j) h h' r"
  shows "Array.get h' a ! k = (if k < i then Array.get h a ! k
      else if j < k then Array.get h a ! k
      else Array.get h a ! (j - (k - i)))" (is "?P a i j h h'")
using assms proof (induct a i j arbitrary: h h' rule: rev.induct)
  case (1 a i j h h'')
  thus ?case
  proof (cases "i < j")
    case True
    with 1[unfolded rev.simps[of a i j]]
    obtain h' where
      swp: "effect (swap a i j) h h' ()"
      and rev: "effect (rev a (i + 1) (j - 1)) h' h'' ()"
      by (auto elim: effect_elims)
    from rev 1 True
    have eq: "?P a (i + 1) (j - 1) h' h''" by auto

    have "k < i \<or> i = k \<or> (i < k \<and> k < j) \<or> j = k \<or> j < k" by arith
    with True show ?thesis
      by (elim disjE) (auto simp: eq swap_pointwise[OF swp])
  next
    case False
    with 1[unfolded rev.simps[of a i j]]
    show ?thesis
      by (cases "k = j") (auto elim: effect_elims)
  qed
qed

lemma rev_length:
  assumes "effect (rev a i j) h h' r"
  shows "Array.length h a = Array.length h' a"
using assms
proof (induct a i j arbitrary: h h' rule: rev.induct)
  case (1 a i j h h'')
  thus ?case
  proof (cases "i < j")
    case True
    with 1[unfolded rev.simps[of a i j]]
    obtain h' where
      swp: "effect (swap a i j) h h' ()"
      and rev: "effect (rev a (i + 1) (j - 1)) h' h'' ()"
      by (auto elim: effect_elims)
    from swp rev 1 True show ?thesis
      unfolding swap.simps
      by (elim effect_elims) fastforce
  next
    case False
    with 1[unfolded rev.simps[of a i j]]
    show ?thesis
      by (auto elim: effect_elims)
  qed
qed

lemma rev2_rev': assumes "effect (rev a i j) h h' u"
  assumes "j < Array.length h a"
  shows "subarray i (j + 1) a h' = List.rev (subarray i (j + 1) a h)"
proof - 
  {
    fix k
    assume "k < Suc j - i"
    with rev_pointwise[OF assms(1)] have "Array.get h' a ! (i + k) = Array.get h a ! (j - k)"
      by auto
  } 
  with assms(2) rev_length[OF assms(1)] show ?thesis
  unfolding subarray_def Array.length_def
  by (auto simp add: length_sublist' rev_nth min_def nth_sublist' intro!: nth_equalityI)
qed

lemma rev2_rev: 
  assumes "effect (rev a 0 (Array.length h a - 1)) h h' u"
  shows "Array.get h' a = List.rev (Array.get h a)"
  using rev2_rev'[OF assms] rev_length[OF assms] assms
    by (cases "Array.length h a = 0", auto simp add: Array.length_def
      subarray_def rev.simps[where j=0] elim!: effect_elims)
  (drule sym[of "List.length (Array.get h a)"], simp)

definition "example = (Array.make 10 id \<guillemotright>= (\<lambda>a. rev a 0 9))"

export_code example checking SML SML_imp OCaml? OCaml_imp? Haskell? Scala? Scala_imp?

end

