(*  Title:      HOL/Library/Sublist.thy
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
    Author:     Christian Sternagel, JAIST
*)

header {* Parallel lists, list suffixes, and homeomorphic embedding *}

theory Sublist
imports Main
begin

subsection {* Parallel lists *}

definition parallel :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infixl "\<parallel>" 50)
  where "(xs \<parallel> ys) = (\<not> prefixeq xs ys \<and> \<not> prefixeq ys xs)"

lemma parallelI [intro]: "\<not> prefixeq xs ys \<Longrightarrow> \<not> prefixeq ys xs \<Longrightarrow> xs \<parallel> ys"
  unfolding parallel_def by blast

lemma parallelE [elim]:
  assumes "xs \<parallel> ys"
  obtains "\<not> prefixeq xs ys \<and> \<not> prefixeq ys xs"
  using assms unfolding parallel_def by blast

theorem prefixeq_cases:
  obtains "prefixeq xs ys" | "prefix ys xs" | "xs \<parallel> ys"
  unfolding parallel_def prefix_def by blast

theorem parallel_decomp:
  "xs \<parallel> ys \<Longrightarrow> \<exists>as b bs c cs. b \<noteq> c \<and> xs = as @ b # bs \<and> ys = as @ c # cs"
proof (induct xs rule: rev_induct)
  case Nil
  then have False by auto
  then show ?case ..
next
  case (snoc x xs)
  show ?case
  proof (rule prefixeq_cases)
    assume le: "prefixeq xs ys"
    then obtain ys' where ys: "ys = xs @ ys'" ..
    show ?thesis
    proof (cases ys')
      assume "ys' = []"
      then show ?thesis by (metis append_Nil2 parallelE prefixeqI snoc.prems ys)
    next
      fix c cs assume ys': "ys' = c # cs"
      have "x \<noteq> c" using snoc.prems ys ys' by fastforce
      thus "\<exists>as b bs c cs. b \<noteq> c \<and> xs @ [x] = as @ b # bs \<and> ys = as @ c # cs"
        using ys ys' by blast
    qed
  next
    assume "prefix ys xs"
    then have "prefixeq ys (xs @ [x])" by (simp add: prefix_def)
    with snoc have False by blast
    then show ?thesis ..
  next
    assume "xs \<parallel> ys"
    with snoc obtain as b bs c cs where neq: "(b::'a) \<noteq> c"
      and xs: "xs = as @ b # bs" and ys: "ys = as @ c # cs"
      by blast
    from xs have "xs @ [x] = as @ b # (bs @ [x])" by simp
    with neq ys show ?thesis by blast
  qed
qed

lemma parallel_append: "a \<parallel> b \<Longrightarrow> a @ c \<parallel> b @ d"
  apply (rule parallelI)
    apply (erule parallelE, erule conjE,
      induct rule: not_prefixeq_induct, simp+)+
  done

lemma parallel_appendI: "xs \<parallel> ys \<Longrightarrow> x = xs @ xs' \<Longrightarrow> y = ys @ ys' \<Longrightarrow> x \<parallel> y"
  by (simp add: parallel_append)

lemma parallel_commute: "a \<parallel> b \<longleftrightarrow> b \<parallel> a"
  unfolding parallel_def by auto


subsection {* Suffix order on lists *}

definition suffixeq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "suffixeq xs ys = (\<exists>zs. ys = zs @ xs)"

definition suffix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "suffix xs ys \<longleftrightarrow> (\<exists>us. ys = us @ xs \<and> us \<noteq> [])"

lemma suffix_imp_suffixeq:
  "suffix xs ys \<Longrightarrow> suffixeq xs ys"
  by (auto simp: suffixeq_def suffix_def)

lemma suffixeqI [intro?]: "ys = zs @ xs \<Longrightarrow> suffixeq xs ys"
  unfolding suffixeq_def by blast

lemma suffixeqE [elim?]:
  assumes "suffixeq xs ys"
  obtains zs where "ys = zs @ xs"
  using assms unfolding suffixeq_def by blast

lemma suffixeq_refl [iff]: "suffixeq xs xs"
  by (auto simp add: suffixeq_def)
lemma suffix_trans:
  "suffix xs ys \<Longrightarrow> suffix ys zs \<Longrightarrow> suffix xs zs"
  by (auto simp: suffix_def)
lemma suffixeq_trans: "\<lbrakk>suffixeq xs ys; suffixeq ys zs\<rbrakk> \<Longrightarrow> suffixeq xs zs"
  by (auto simp add: suffixeq_def)
lemma suffixeq_antisym: "\<lbrakk>suffixeq xs ys; suffixeq ys xs\<rbrakk> \<Longrightarrow> xs = ys"
  by (auto simp add: suffixeq_def)

lemma suffixeq_tl [simp]: "suffixeq (tl xs) xs"
  by (induct xs) (auto simp: suffixeq_def)

lemma suffix_tl [simp]: "xs \<noteq> [] \<Longrightarrow> suffix (tl xs) xs"
  by (induct xs) (auto simp: suffix_def)

lemma Nil_suffixeq [iff]: "suffixeq [] xs"
  by (simp add: suffixeq_def)
lemma suffixeq_Nil [simp]: "(suffixeq xs []) = (xs = [])"
  by (auto simp add: suffixeq_def)

lemma suffixeq_ConsI: "suffixeq xs ys \<Longrightarrow> suffixeq xs (y # ys)"
  by (auto simp add: suffixeq_def)
lemma suffixeq_ConsD: "suffixeq (x # xs) ys \<Longrightarrow> suffixeq xs ys"
  by (auto simp add: suffixeq_def)

lemma suffixeq_appendI: "suffixeq xs ys \<Longrightarrow> suffixeq xs (zs @ ys)"
  by (auto simp add: suffixeq_def)
lemma suffixeq_appendD: "suffixeq (zs @ xs) ys \<Longrightarrow> suffixeq xs ys"
  by (auto simp add: suffixeq_def)

lemma suffix_set_subset:
  "suffix xs ys \<Longrightarrow> set xs \<subseteq> set ys" by (auto simp: suffix_def)

lemma suffixeq_set_subset:
  "suffixeq xs ys \<Longrightarrow> set xs \<subseteq> set ys" by (auto simp: suffixeq_def)

lemma suffixeq_ConsD2: "suffixeq (x # xs) (y # ys) \<Longrightarrow> suffixeq xs ys"
proof -
  assume "suffixeq (x # xs) (y # ys)"
  then obtain zs where "y # ys = zs @ x # xs" ..
  then show ?thesis
    by (induct zs) (auto intro!: suffixeq_appendI suffixeq_ConsI)
qed

lemma suffixeq_to_prefixeq [code]: "suffixeq xs ys \<longleftrightarrow> prefixeq (rev xs) (rev ys)"
proof
  assume "suffixeq xs ys"
  then obtain zs where "ys = zs @ xs" ..
  then have "rev ys = rev xs @ rev zs" by simp
  then show "prefixeq (rev xs) (rev ys)" ..
next
  assume "prefixeq (rev xs) (rev ys)"
  then obtain zs where "rev ys = rev xs @ zs" ..
  then have "rev (rev ys) = rev zs @ rev (rev xs)" by simp
  then have "ys = rev zs @ xs" by simp
  then show "suffixeq xs ys" ..
qed

lemma distinct_suffixeq: "distinct ys \<Longrightarrow> suffixeq xs ys \<Longrightarrow> distinct xs"
  by (clarsimp elim!: suffixeqE)

lemma suffixeq_map: "suffixeq xs ys \<Longrightarrow> suffixeq (map f xs) (map f ys)"
  by (auto elim!: suffixeqE intro: suffixeqI)

lemma suffixeq_drop: "suffixeq (drop n as) as"
  unfolding suffixeq_def
  apply (rule exI [where x = "take n as"])
  apply simp
  done

lemma suffixeq_take: "suffixeq xs ys \<Longrightarrow> ys = take (length ys - length xs) ys @ xs"
  by (auto elim!: suffixeqE)

lemma suffixeq_suffix_reflclp_conv: "suffixeq = suffix\<^sup>=\<^sup>="
proof (intro ext iffI)
  fix xs ys :: "'a list"
  assume "suffixeq xs ys"
  show "suffix\<^sup>=\<^sup>= xs ys"
  proof
    assume "xs \<noteq> ys"
    with `suffixeq xs ys` show "suffix xs ys"
      by (auto simp: suffixeq_def suffix_def)
  qed
next
  fix xs ys :: "'a list"
  assume "suffix\<^sup>=\<^sup>= xs ys"
  then show "suffixeq xs ys"
  proof
    assume "suffix xs ys" then show "suffixeq xs ys"
      by (rule suffix_imp_suffixeq)
  next
    assume "xs = ys" then show "suffixeq xs ys"
      by (auto simp: suffixeq_def)
  qed
qed

lemma parallelD1: "x \<parallel> y \<Longrightarrow> \<not> prefixeq x y"
  by blast

lemma parallelD2: "x \<parallel> y \<Longrightarrow> \<not> prefixeq y x"
  by blast

lemma parallel_Nil1 [simp]: "\<not> x \<parallel> []"
  unfolding parallel_def by simp

lemma parallel_Nil2 [simp]: "\<not> [] \<parallel> x"
  unfolding parallel_def by simp

lemma Cons_parallelI1: "a \<noteq> b \<Longrightarrow> a # as \<parallel> b # bs"
  by auto

lemma Cons_parallelI2: "\<lbrakk> a = b; as \<parallel> bs \<rbrakk> \<Longrightarrow> a # as \<parallel> b # bs"
  by (metis Cons_prefixeq_Cons parallelE parallelI)

lemma not_equal_is_parallel:
  assumes neq: "xs \<noteq> ys"
    and len: "length xs = length ys"
  shows "xs \<parallel> ys"
  using len neq
proof (induct rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons a as b bs)
  have ih: "as \<noteq> bs \<Longrightarrow> as \<parallel> bs" by fact
  show ?case
  proof (cases "a = b")
    case True
    then have "as \<noteq> bs" using Cons by simp
    then show ?thesis by (rule Cons_parallelI2 [OF True ih])
  next
    case False
    then show ?thesis by (rule Cons_parallelI1)
  qed
qed

lemma suffix_reflclp_conv: "suffix\<^sup>=\<^sup>= = suffixeq"
  by (intro ext) (auto simp: suffixeq_def suffix_def)

lemma suffix_lists: "suffix xs ys \<Longrightarrow> ys \<in> lists A \<Longrightarrow> xs \<in> lists A"
  unfolding suffix_def by auto


subsection {* Homeomorphic embedding on lists *}

inductive list_hembeq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for P :: "('a \<Rightarrow> 'a \<Rightarrow> bool)"
where
  list_hembeq_Nil [intro, simp]: "list_hembeq P [] ys"
| list_hembeq_Cons [intro] : "list_hembeq P xs ys \<Longrightarrow> list_hembeq P xs (y#ys)"
| list_hembeq_Cons2 [intro]: "P\<^sup>=\<^sup>= x y \<Longrightarrow> list_hembeq P xs ys \<Longrightarrow> list_hembeq P (x#xs) (y#ys)"

lemma list_hembeq_Nil2 [simp]:
  assumes "list_hembeq P xs []" shows "xs = []"
  using assms by (cases rule: list_hembeq.cases) auto

lemma list_hembeq_refl [simp, intro!]:
  "list_hembeq P xs xs"
  by (induct xs) auto

lemma list_hembeq_Cons_Nil [simp]: "list_hembeq P (x#xs) [] = False"
proof -
  { assume "list_hembeq P (x#xs) []"
    from list_hembeq_Nil2 [OF this] have False by simp
  } moreover {
    assume False
    then have "list_hembeq P (x#xs) []" by simp
  } ultimately show ?thesis by blast
qed

lemma list_hembeq_append2 [intro]: "list_hembeq P xs ys \<Longrightarrow> list_hembeq P xs (zs @ ys)"
  by (induct zs) auto

lemma list_hembeq_prefix [intro]:
  assumes "list_hembeq P xs ys" shows "list_hembeq P xs (ys @ zs)"
  using assms
  by (induct arbitrary: zs) auto

lemma list_hembeq_ConsD:
  assumes "list_hembeq P (x#xs) ys"
  shows "\<exists>us v vs. ys = us @ v # vs \<and> P\<^sup>=\<^sup>= x v \<and> list_hembeq P xs vs"
using assms
proof (induct x \<equiv> "x # xs" ys arbitrary: x xs)
  case list_hembeq_Cons
  then show ?case by (metis append_Cons)
next
  case (list_hembeq_Cons2 x y xs ys)
  then show ?case by blast
qed

lemma list_hembeq_appendD:
  assumes "list_hembeq P (xs @ ys) zs"
  shows "\<exists>us vs. zs = us @ vs \<and> list_hembeq P xs us \<and> list_hembeq P ys vs"
using assms
proof (induction xs arbitrary: ys zs)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  then obtain us v vs where
    zs: "zs = us @ v # vs" and p: "P\<^sup>=\<^sup>= x v" and lh: "list_hembeq P (xs @ ys) vs"
    by (auto dest: list_hembeq_ConsD)
  obtain sk\<^sub>0 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" and sk\<^sub>1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    sk: "\<forall>x\<^sub>0 x\<^sub>1. \<not> list_hembeq P (xs @ x\<^sub>0) x\<^sub>1 \<or> sk\<^sub>0 x\<^sub>0 x\<^sub>1 @ sk\<^sub>1 x\<^sub>0 x\<^sub>1 = x\<^sub>1 \<and> list_hembeq P xs (sk\<^sub>0 x\<^sub>0 x\<^sub>1) \<and> list_hembeq P x\<^sub>0 (sk\<^sub>1 x\<^sub>0 x\<^sub>1)"
    using Cons(1) by (metis (no_types))
  hence "\<forall>x\<^sub>2. list_hembeq P (x # xs) (x\<^sub>2 @ v # sk\<^sub>0 ys vs)" using p lh by auto
  thus ?case using lh zs sk by (metis (no_types) append_Cons append_assoc)
qed

lemma list_hembeq_suffix:
  assumes "list_hembeq P xs ys" and "suffix ys zs"
  shows "list_hembeq P xs zs"
  using assms(2) and list_hembeq_append2 [OF assms(1)] by (auto simp: suffix_def)

lemma list_hembeq_suffixeq:
  assumes "list_hembeq P xs ys" and "suffixeq ys zs"
  shows "list_hembeq P xs zs"
  using assms and list_hembeq_suffix unfolding suffixeq_suffix_reflclp_conv by auto

lemma list_hembeq_length: "list_hembeq P xs ys \<Longrightarrow> length xs \<le> length ys"
  by (induct rule: list_hembeq.induct) auto

lemma list_hembeq_trans:
  assumes "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A; P x y; P y z\<rbrakk> \<Longrightarrow> P x z"
  shows "\<And>xs ys zs. \<lbrakk>xs \<in> lists A; ys \<in> lists A; zs \<in> lists A;
    list_hembeq P xs ys; list_hembeq P ys zs\<rbrakk> \<Longrightarrow> list_hembeq P xs zs"
proof -
  fix xs ys zs
  assume "list_hembeq P xs ys" and "list_hembeq P ys zs"
    and "xs \<in> lists A" and "ys \<in> lists A" and "zs \<in> lists A"
  then show "list_hembeq P xs zs"
  proof (induction arbitrary: zs)
    case list_hembeq_Nil show ?case by blast
  next
    case (list_hembeq_Cons xs ys y)
    from list_hembeq_ConsD [OF `list_hembeq P (y#ys) zs`] obtain us v vs
      where zs: "zs = us @ v # vs" and "P\<^sup>=\<^sup>= y v" and "list_hembeq P ys vs" by blast
    then have "list_hembeq P ys (v#vs)" by blast
    then have "list_hembeq P ys zs" unfolding zs by (rule list_hembeq_append2)
    from list_hembeq_Cons.IH [OF this] and list_hembeq_Cons.prems show ?case by simp
  next
    case (list_hembeq_Cons2 x y xs ys)
    from list_hembeq_ConsD [OF `list_hembeq P (y#ys) zs`] obtain us v vs
      where zs: "zs = us @ v # vs" and "P\<^sup>=\<^sup>= y v" and "list_hembeq P ys vs" by blast
    with list_hembeq_Cons2 have "list_hembeq P xs vs" by simp
    moreover have "P\<^sup>=\<^sup>= x v"
    proof -
      from zs and `zs \<in> lists A` have "v \<in> A" by auto
      moreover have "x \<in> A" and "y \<in> A" using list_hembeq_Cons2 by simp_all
      ultimately show ?thesis
        using `P\<^sup>=\<^sup>= x y` and `P\<^sup>=\<^sup>= y v` and assms
        by blast
    qed
    ultimately have "list_hembeq P (x#xs) (v#vs)" by blast
    then show ?case unfolding zs by (rule list_hembeq_append2)
  qed
qed


subsection {* Sublists (special case of homeomorphic embedding) *}

abbreviation sublisteq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "sublisteq xs ys \<equiv> list_hembeq (op =) xs ys"

lemma sublisteq_Cons2: "sublisteq xs ys \<Longrightarrow> sublisteq (x#xs) (x#ys)" by auto

lemma sublisteq_same_length:
  assumes "sublisteq xs ys" and "length xs = length ys" shows "xs = ys"
  using assms by (induct) (auto dest: list_hembeq_length)

lemma not_sublisteq_length [simp]: "length ys < length xs \<Longrightarrow> \<not> sublisteq xs ys"
  by (metis list_hembeq_length linorder_not_less)

lemma [code]:
  "list_hembeq P [] ys \<longleftrightarrow> True"
  "list_hembeq P (x#xs) [] \<longleftrightarrow> False"
  by (simp_all)

lemma sublisteq_Cons': "sublisteq (x#xs) ys \<Longrightarrow> sublisteq xs ys"
  by (induct xs, simp, blast dest: list_hembeq_ConsD)

lemma sublisteq_Cons2':
  assumes "sublisteq (x#xs) (x#ys)" shows "sublisteq xs ys"
  using assms by (cases) (rule sublisteq_Cons')

lemma sublisteq_Cons2_neq:
  assumes "sublisteq (x#xs) (y#ys)"
  shows "x \<noteq> y \<Longrightarrow> sublisteq (x#xs) ys"
  using assms by (cases) auto

lemma sublisteq_Cons2_iff [simp, code]:
  "sublisteq (x#xs) (y#ys) = (if x = y then sublisteq xs ys else sublisteq (x#xs) ys)"
  by (metis list_hembeq_Cons sublisteq_Cons2 sublisteq_Cons2' sublisteq_Cons2_neq)

lemma sublisteq_append': "sublisteq (zs @ xs) (zs @ ys) \<longleftrightarrow> sublisteq xs ys"
  by (induct zs) simp_all

lemma sublisteq_refl [simp, intro!]: "sublisteq xs xs" by (induct xs) simp_all

lemma sublisteq_antisym:
  assumes "sublisteq xs ys" and "sublisteq ys xs"
  shows "xs = ys"
using assms
proof (induct)
  case list_hembeq_Nil
  from list_hembeq_Nil2 [OF this] show ?case by simp
next
  case list_hembeq_Cons2
  thus ?case by simp
next
  case list_hembeq_Cons
  hence False using sublisteq_Cons' by fastforce
  thus ?case ..
qed

lemma sublisteq_trans: "sublisteq xs ys \<Longrightarrow> sublisteq ys zs \<Longrightarrow> sublisteq xs zs"
  by (rule list_hembeq_trans [of UNIV "op ="]) auto

lemma sublisteq_append_le_same_iff: "sublisteq (xs @ ys) ys \<longleftrightarrow> xs = []"
  by (auto dest: list_hembeq_length)

lemma list_hembeq_append_mono:
  "\<lbrakk> list_hembeq P xs xs'; list_hembeq P ys ys' \<rbrakk> \<Longrightarrow> list_hembeq P (xs@ys) (xs'@ys')"
  apply (induct rule: list_hembeq.induct)
    apply (metis eq_Nil_appendI list_hembeq_append2)
   apply (metis append_Cons list_hembeq_Cons)
  apply (metis append_Cons list_hembeq_Cons2)
  done


subsection {* Appending elements *}

lemma sublisteq_append [simp]:
  "sublisteq (xs @ zs) (ys @ zs) \<longleftrightarrow> sublisteq xs ys" (is "?l = ?r")
proof
  { fix xs' ys' xs ys zs :: "'a list" assume "sublisteq xs' ys'"
    then have "xs' = xs @ zs & ys' = ys @ zs \<longrightarrow> sublisteq xs ys"
    proof (induct arbitrary: xs ys zs)
      case list_hembeq_Nil show ?case by simp
    next
      case (list_hembeq_Cons xs' ys' x)
      { assume "ys=[]" then have ?case using list_hembeq_Cons(1) by auto }
      moreover
      { fix us assume "ys = x#us"
        then have ?case using list_hembeq_Cons(2) by(simp add: list_hembeq.list_hembeq_Cons) }
      ultimately show ?case by (auto simp:Cons_eq_append_conv)
    next
      case (list_hembeq_Cons2 x y xs' ys')
      { assume "xs=[]" then have ?case using list_hembeq_Cons2(1) by auto }
      moreover
      { fix us vs assume "xs=x#us" "ys=x#vs" then have ?case using list_hembeq_Cons2 by auto}
      moreover
      { fix us assume "xs=x#us" "ys=[]" then have ?case using list_hembeq_Cons2(2) by bestsimp }
      ultimately show ?case using `op =\<^sup>=\<^sup>= x y` by (auto simp: Cons_eq_append_conv)
    qed }
  moreover assume ?l
  ultimately show ?r by blast
next
  assume ?r then show ?l by (metis list_hembeq_append_mono sublisteq_refl)
qed

lemma sublisteq_drop_many: "sublisteq xs ys \<Longrightarrow> sublisteq xs (zs @ ys)"
  by (induct zs) auto

lemma sublisteq_rev_drop_many: "sublisteq xs ys \<Longrightarrow> sublisteq xs (ys @ zs)"
  by (metis append_Nil2 list_hembeq_Nil list_hembeq_append_mono)


subsection {* Relation to standard list operations *}

lemma sublisteq_map:
  assumes "sublisteq xs ys" shows "sublisteq (map f xs) (map f ys)"
  using assms by (induct) auto

lemma sublisteq_filter_left [simp]: "sublisteq (filter P xs) xs"
  by (induct xs) auto

lemma sublisteq_filter [simp]:
  assumes "sublisteq xs ys" shows "sublisteq (filter P xs) (filter P ys)"
  using assms by induct auto

lemma "sublisteq xs ys \<longleftrightarrow> (\<exists>N. xs = sublist ys N)" (is "?L = ?R")
proof
  assume ?L
  then show ?R
  proof (induct)
    case list_hembeq_Nil show ?case by (metis sublist_empty)
  next
    case (list_hembeq_Cons xs ys x)
    then obtain N where "xs = sublist ys N" by blast
    then have "xs = sublist (x#ys) (Suc ` N)"
      by (clarsimp simp add:sublist_Cons inj_image_mem_iff)
    then show ?case by blast
  next
    case (list_hembeq_Cons2 x y xs ys)
    then obtain N where "xs = sublist ys N" by blast
    then have "x#xs = sublist (x#ys) (insert 0 (Suc ` N))"
      by (clarsimp simp add:sublist_Cons inj_image_mem_iff)
    moreover from list_hembeq_Cons2 have "x = y" by simp
    ultimately show ?case by blast
  qed
next
  assume ?R
  then obtain N where "xs = sublist ys N" ..
  moreover have "sublisteq (sublist ys N) ys"
  proof (induct ys arbitrary: N)
    case Nil show ?case by simp
  next
    case Cons then show ?case by (auto simp: sublist_Cons)
  qed
  ultimately show ?L by simp
qed

end
