(*  Title:      HOL/Library/List_Prefix.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

header {*
  \title{List prefixes}
  \author{Tobias Nipkow and Markus Wenzel}
*}

theory List_Prefix = Main:

subsection {* Prefix order on lists *}

instance list :: ("term") ord ..

defs (overloaded)
  prefix_def: "xs \<le> zs == \<exists>ys. zs = xs @ ys"
  strict_prefix_def: "xs < zs == xs \<le> zs \<and> xs \<noteq> (zs::'a list)"

instance list :: ("term") order
proof
  fix xs ys zs :: "'a list"
  show "xs \<le> xs" by (simp add: prefix_def)
  { assume "xs \<le> ys" and "ys \<le> zs" thus "xs \<le> zs" by (auto simp add: prefix_def) }
  { assume "xs \<le> ys" and "ys \<le> xs" thus "xs = ys" by (auto simp add: prefix_def) }
  show "(xs < zs) = (xs \<le> zs \<and> xs \<noteq> zs)" by (simp only: strict_prefix_def)
qed

constdefs
  parallel :: "'a list => 'a list => bool"    (infixl "\<parallel>" 50)
  "xs \<parallel> ys == \<not> (xs \<le> ys) \<and> \<not> (ys \<le> xs)"

lemma parallelI [intro]: "\<not> (xs \<le> ys) ==> \<not> (ys \<le> xs) ==> xs \<parallel> ys"
  by (unfold parallel_def) blast

lemma parellelE [elim]:
    "xs \<parallel> ys ==> (\<not> (xs \<le> ys) ==> \<not> (ys \<le> xs) ==> C) ==> C"
  by (unfold parallel_def) blast

theorem prefix_cases:
  "(xs \<le> ys ==> C) ==>
    (ys \<le> xs ==> C) ==>
    (xs \<parallel> ys ==> C) ==> C"
  by (unfold parallel_def) blast


subsection {* Recursion equations *}

theorem Nil_prefix [iff]: "[] \<le> xs"
  apply (simp add: prefix_def)
  done

theorem prefix_Nil [simp]: "(xs \<le> []) = (xs = [])"
  apply (induct_tac xs)
   apply simp
  apply (simp add: prefix_def)
  done

lemma prefix_snoc [simp]: "(xs \<le> ys @ [y]) = (xs = ys @ [y] \<or> xs \<le> ys)"
  apply (unfold prefix_def)
  apply (rule iffI)
   apply (erule exE)
   apply (rename_tac zs)
   apply (rule_tac xs = zs in rev_exhaust)
    apply simp
   apply hypsubst
   apply (simp del: append_assoc add: append_assoc [symmetric])
  apply force
  done

lemma Cons_prefix_Cons [simp]: "(x # xs \<le> y # ys) = (x = y \<and> xs \<le> ys)"
  apply (auto simp add: prefix_def)
  done

lemma same_prefix_prefix [simp]: "(xs @ ys \<le> xs @ zs) = (ys \<le> zs)"
  apply (induct_tac xs)
   apply simp_all
  done

lemma [iff]: "(xs @ ys \<le> xs) = (ys = [])"
  apply (insert same_prefix_prefix [where ?zs = "[]"])
  apply simp
  apply blast
  done

lemma prefix_prefix [simp]: "xs \<le> ys ==> xs \<le> ys @ zs"
  apply (unfold prefix_def)
  apply clarify
  apply simp
  done

theorem prefix_Cons: "(xs \<le> y # ys) = (xs = [] \<or> (\<exists>zs. xs = y # zs \<and> zs \<le> ys))"
  apply (unfold prefix_def)
  apply (case_tac xs)
   apply auto
  done

theorem prefix_append:
    "(xs \<le> ys @ zs) = (xs \<le> ys \<or> (\<exists>us. xs = ys @ us \<and> us \<le> zs))"
  apply (induct zs rule: rev_induct)
   apply force
  apply (simp del: append_assoc add: append_assoc [symmetric])
  apply simp
  apply blast
  done

lemma append_one_prefix:
    "xs \<le> ys ==> length xs < length ys ==> xs @ [ys ! length xs] \<le> ys"
  apply (unfold prefix_def)
  apply (auto simp add: nth_append)
  apply (case_tac ys)
   apply auto
  done

theorem prefix_length_le: "xs \<le> ys ==> length xs \<le> length ys"
  apply (auto simp add: prefix_def)
  done


subsection {* Prefix cases *}

lemma prefix_Nil_cases [case_names Nil]:
  "xs \<le> [] ==>
    (xs = [] ==> C) ==> C"
  by simp

lemma prefix_Cons_cases [case_names Nil Cons]:
  "xs \<le> y # ys ==>
    (xs = [] ==> C) ==>
    (!!zs. xs = y # zs ==> zs \<le> ys ==> C) ==> C"
  by (simp only: prefix_Cons) blast

lemma prefix_snoc_cases [case_names prefix snoc]:
  "xs \<le> ys @ [y] ==>
    (xs \<le> ys ==> C) ==>
    (xs = ys @ [y] ==> C) ==> C"
  by (simp only: prefix_snoc) blast

lemma prefix_append_cases [case_names prefix append]:
  "xs \<le> ys @ zs ==>
    (xs \<le> ys ==> C) ==>
    (!!us. xs = ys @ us ==> us \<le> zs ==> C) ==> C"
  by (simp only: prefix_append) blast

lemmas prefix_any_cases [cases set: prefix] =    (*dummy set name*)
  prefix_Nil_cases prefix_Cons_cases
  prefix_snoc_cases prefix_append_cases

end
