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
  prefix_def: "xs \<le> ys == \<exists>zs. ys = xs @ zs"
  strict_prefix_def: "xs < ys == xs \<le> ys \<and> xs \<noteq> (ys::'a list)"

instance list :: ("term") order
  by intro_classes (auto simp add: prefix_def strict_prefix_def)

lemma prefixI [intro?]: "ys = xs @ zs ==> xs \<le> ys"
  by (unfold prefix_def) blast

lemma prefixE [elim?]: "xs \<le> ys ==> (!!zs. ys = xs @ zs ==> C) ==> C"
  by (unfold prefix_def) blast

lemma strict_prefixI [intro?]: "xs \<le> ys ==> xs \<noteq> ys ==> xs < (ys::'a list)"
  by (unfold strict_prefix_def) blast

lemma strict_prefixE [elim?]:
    "xs < ys ==> (xs \<le> ys ==> xs \<noteq> (ys::'a list) ==> C) ==> C"
  by (unfold strict_prefix_def) blast


subsection {* Basic properties of prefixes *}

theorem Nil_prefix [iff]: "[] \<le> xs"
  by (simp add: prefix_def)

theorem prefix_Nil [simp]: "(xs \<le> []) = (xs = [])"
  by (induct xs) (simp_all add: prefix_def)

lemma prefix_snoc [simp]: "(xs \<le> ys @ [y]) = (xs = ys @ [y] \<or> xs \<le> ys)"
proof
  assume "xs \<le> ys @ [y]"
  then obtain zs where zs: "ys @ [y] = xs @ zs" ..
  show "xs = ys @ [y] \<or> xs \<le> ys"
  proof (cases zs rule: rev_cases)
    assume "zs = []"
    with zs have "xs = ys @ [y]" by simp
    thus ?thesis ..
  next
    fix z zs' assume "zs = zs' @ [z]"
    with zs have "ys = xs @ zs'" by simp
    hence "xs \<le> ys" ..
    thus ?thesis ..
  qed
next
  assume "xs = ys @ [y] \<or> xs \<le> ys"
  thus "xs \<le> ys @ [y]"
  proof
    assume "xs = ys @ [y]"
    thus ?thesis by simp
  next
    assume "xs \<le> ys"
    then obtain zs where "ys = xs @ zs" ..
    hence "ys @ [y] = xs @ (zs @ [y])" by simp
    thus ?thesis ..
  qed
qed

lemma Cons_prefix_Cons [simp]: "(x # xs \<le> y # ys) = (x = y \<and> xs \<le> ys)"
  by (auto simp add: prefix_def)

lemma same_prefix_prefix [simp]: "(xs @ ys \<le> xs @ zs) = (ys \<le> zs)"
  by (induct xs) simp_all

lemma same_prefix_nil [iff]: "(xs @ ys \<le> xs) = (ys = [])"
proof -
  have "(xs @ ys \<le> xs @ []) = (ys \<le> [])" by (rule same_prefix_prefix)
  thus ?thesis by simp
qed

lemma prefix_prefix [simp]: "xs \<le> ys ==> xs \<le> ys @ zs"
proof -
  assume "xs \<le> ys"
  then obtain us where "ys = xs @ us" ..
  hence "ys @ zs = xs @ (us @ zs)" by simp
  thus ?thesis ..
qed

theorem prefix_Cons: "(xs \<le> y # ys) = (xs = [] \<or> (\<exists>zs. xs = y # zs \<and> zs \<le> ys))"
  by (cases xs) (auto simp add: prefix_def)

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
  apply (case_tac zs)
   apply auto
  done

theorem prefix_length_le: "xs \<le> ys ==> length xs \<le> length ys"
  by (auto simp add: prefix_def)


subsection {* Parallel lists *}

constdefs
  parallel :: "'a list => 'a list => bool"    (infixl "\<parallel>" 50)
  "xs \<parallel> ys == \<not> xs \<le> ys \<and> \<not> ys \<le> xs"

lemma parallelI [intro]: "\<not> xs \<le> ys ==> \<not> ys \<le> xs ==> xs \<parallel> ys"
  by (unfold parallel_def) blast

lemma parallelE [elim]:
    "xs \<parallel> ys ==> (\<not> xs \<le> ys ==> \<not> ys \<le> xs ==> C) ==> C"
  by (unfold parallel_def) blast

theorem prefix_cases:
  "(xs \<le> ys ==> C) ==>
    (ys < xs ==> C) ==>
    (xs \<parallel> ys ==> C) ==> C"
  by (unfold parallel_def strict_prefix_def) blast

theorem parallel_decomp:
  "xs \<parallel> ys ==> \<exists>as b bs c cs. b \<noteq> c \<and> xs = as @ b # bs \<and> ys = as @ c # cs"
  (is "PROP ?P xs" concl is "?E xs")
proof (induct xs rule: rev_induct)
  assume "[] \<parallel> ys" hence False by auto
  thus "?E []" ..
next
  fix x xs
  assume hyp: "PROP ?P xs"
  assume asm: "xs @ [x] \<parallel> ys"
  show "?E (xs @ [x])"
  proof (rule prefix_cases)
    assume le: "xs \<le> ys"
    then obtain ys' where ys: "ys = xs @ ys'" ..
    show ?thesis
    proof (cases ys')
      assume "ys' = []" with ys have "xs = ys" by simp
      with asm have "[x] \<parallel> []" by auto
      hence False by blast
      thus ?thesis ..
    next
      fix c cs assume ys': "ys' = c # cs"
      with asm ys have "xs @ [x] \<parallel> xs @ c # cs" by (simp only:)
      hence "x \<noteq> c" by auto
      moreover have "xs @ [x] = xs @ x # []" by simp
      moreover from ys ys' have "ys = xs @ c # cs" by (simp only:)
      ultimately show ?thesis by blast
    qed
  next
    assume "ys < xs" hence "ys \<le> xs @ [x]" by (simp add: strict_prefix_def)
    with asm have False by blast
    thus ?thesis ..
  next
    assume "xs \<parallel> ys"
    with hyp obtain as b bs c cs where neq: "(b::'a) \<noteq> c"
      and xs: "xs = as @ b # bs" and ys: "ys = as @ c # cs"
      by blast
    from xs have "xs @ [x] = as @ b # (bs @ [x])" by simp
    with neq ys show ?thesis by blast
  qed
qed

end
