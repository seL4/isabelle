(*  Title:      HOL/Library/Sublist.thy
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
    Author:     Christian Sternagel, JAIST
*)

header {* List prefixes, suffixes, and homeomorphic embedding *}

theory Sublist
imports Main
begin

subsection {* Prefix order on lists *}

definition prefixeq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "prefixeq xs ys \<longleftrightarrow> (\<exists>zs. ys = xs @ zs)"

definition prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "prefix xs ys \<longleftrightarrow> prefixeq xs ys \<and> xs \<noteq> ys"

interpretation prefix_order: order prefixeq prefix
  by default (auto simp: prefixeq_def prefix_def)

interpretation prefix_bot: order_bot Nil prefixeq prefix
  by default (simp add: prefixeq_def)

lemma prefixeqI [intro?]: "ys = xs @ zs \<Longrightarrow> prefixeq xs ys"
  unfolding prefixeq_def by blast

lemma prefixeqE [elim?]:
  assumes "prefixeq xs ys"
  obtains zs where "ys = xs @ zs"
  using assms unfolding prefixeq_def by blast

lemma prefixI' [intro?]: "ys = xs @ z # zs \<Longrightarrow> prefix xs ys"
  unfolding prefix_def prefixeq_def by blast

lemma prefixE' [elim?]:
  assumes "prefix xs ys"
  obtains z zs where "ys = xs @ z # zs"
proof -
  from `prefix xs ys` obtain us where "ys = xs @ us" and "xs \<noteq> ys"
    unfolding prefix_def prefixeq_def by blast
  with that show ?thesis by (auto simp add: neq_Nil_conv)
qed

lemma prefixI [intro?]: "prefixeq xs ys \<Longrightarrow> xs \<noteq> ys \<Longrightarrow> prefix xs ys"
  unfolding prefix_def by blast

lemma prefixE [elim?]:
  fixes xs ys :: "'a list"
  assumes "prefix xs ys"
  obtains "prefixeq xs ys" and "xs \<noteq> ys"
  using assms unfolding prefix_def by blast


subsection {* Basic properties of prefixes *}

theorem Nil_prefixeq [iff]: "prefixeq [] xs"
  by (simp add: prefixeq_def)

theorem prefixeq_Nil [simp]: "(prefixeq xs []) = (xs = [])"
  by (induct xs) (simp_all add: prefixeq_def)

lemma prefixeq_snoc [simp]: "prefixeq xs (ys @ [y]) \<longleftrightarrow> xs = ys @ [y] \<or> prefixeq xs ys"
proof
  assume "prefixeq xs (ys @ [y])"
  then obtain zs where zs: "ys @ [y] = xs @ zs" ..
  show "xs = ys @ [y] \<or> prefixeq xs ys"
    by (metis append_Nil2 butlast_append butlast_snoc prefixeqI zs)
next
  assume "xs = ys @ [y] \<or> prefixeq xs ys"
  then show "prefixeq xs (ys @ [y])"
    by (metis prefix_order.eq_iff prefix_order.order_trans prefixeqI)
qed

lemma Cons_prefixeq_Cons [simp]: "prefixeq (x # xs) (y # ys) = (x = y \<and> prefixeq xs ys)"
  by (auto simp add: prefixeq_def)

lemma prefixeq_code [code]:
  "prefixeq [] xs \<longleftrightarrow> True"
  "prefixeq (x # xs) [] \<longleftrightarrow> False"
  "prefixeq (x # xs) (y # ys) \<longleftrightarrow> x = y \<and> prefixeq xs ys"
  by simp_all

lemma same_prefixeq_prefixeq [simp]: "prefixeq (xs @ ys) (xs @ zs) = prefixeq ys zs"
  by (induct xs) simp_all

lemma same_prefixeq_nil [iff]: "prefixeq (xs @ ys) xs = (ys = [])"
  by (metis append_Nil2 append_self_conv prefix_order.eq_iff prefixeqI)

lemma prefixeq_prefixeq [simp]: "prefixeq xs ys \<Longrightarrow> prefixeq xs (ys @ zs)"
  by (metis prefix_order.le_less_trans prefixeqI prefixE prefixI)

lemma append_prefixeqD: "prefixeq (xs @ ys) zs \<Longrightarrow> prefixeq xs zs"
  by (auto simp add: prefixeq_def)

theorem prefixeq_Cons: "prefixeq xs (y # ys) = (xs = [] \<or> (\<exists>zs. xs = y # zs \<and> prefixeq zs ys))"
  by (cases xs) (auto simp add: prefixeq_def)

theorem prefixeq_append:
  "prefixeq xs (ys @ zs) = (prefixeq xs ys \<or> (\<exists>us. xs = ys @ us \<and> prefixeq us zs))"
  apply (induct zs rule: rev_induct)
   apply force
  apply (simp del: append_assoc add: append_assoc [symmetric])
  apply (metis append_eq_appendI)
  done

lemma append_one_prefixeq:
  "prefixeq xs ys \<Longrightarrow> length xs < length ys \<Longrightarrow> prefixeq (xs @ [ys ! length xs]) ys"
  proof (unfold prefixeq_def)
    assume a1: "\<exists>zs. ys = xs @ zs"
    then obtain sk :: "'a list" where sk: "ys = xs @ sk" by fastforce
    assume a2: "length xs < length ys"
    have f1: "\<And>v. ([]\<Colon>'a list) @ v = v" using append_Nil2 by simp
    have "[] \<noteq> sk" using a1 a2 sk less_not_refl by force
    hence "\<exists>v. xs @ hd sk # v = ys" using sk by (metis hd_Cons_tl)
    thus "\<exists>zs. ys = (xs @ [ys ! length xs]) @ zs" using f1 by fastforce
  qed

theorem prefixeq_length_le: "prefixeq xs ys \<Longrightarrow> length xs \<le> length ys"
  by (auto simp add: prefixeq_def)

lemma prefixeq_same_cases:
  "prefixeq (xs\<^sub>1::'a list) ys \<Longrightarrow> prefixeq xs\<^sub>2 ys \<Longrightarrow> prefixeq xs\<^sub>1 xs\<^sub>2 \<or> prefixeq xs\<^sub>2 xs\<^sub>1"
  unfolding prefixeq_def by (force simp: append_eq_append_conv2)

lemma set_mono_prefixeq: "prefixeq xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (auto simp add: prefixeq_def)

lemma take_is_prefixeq: "prefixeq (take n xs) xs"
  unfolding prefixeq_def by (metis append_take_drop_id)

lemma map_prefixeqI: "prefixeq xs ys \<Longrightarrow> prefixeq (map f xs) (map f ys)"
  by (auto simp: prefixeq_def)

lemma prefixeq_length_less: "prefix xs ys \<Longrightarrow> length xs < length ys"
  by (auto simp: prefix_def prefixeq_def)

lemma prefix_simps [simp, code]:
  "prefix xs [] \<longleftrightarrow> False"
  "prefix [] (x # xs) \<longleftrightarrow> True"
  "prefix (x # xs) (y # ys) \<longleftrightarrow> x = y \<and> prefix xs ys"
  by (simp_all add: prefix_def cong: conj_cong)

lemma take_prefix: "prefix xs ys \<Longrightarrow> prefix (take n xs) ys"
  apply (induct n arbitrary: xs ys)
   apply (case_tac ys, simp_all)[1]
  apply (metis prefix_order.less_trans prefixI take_is_prefixeq)
  done

lemma not_prefixeq_cases:
  assumes pfx: "\<not> prefixeq ps ls"
  obtains
    (c1) "ps \<noteq> []" and "ls = []"
  | (c2) a as x xs where "ps = a#as" and "ls = x#xs" and "x = a" and "\<not> prefixeq as xs"
  | (c3) a as x xs where "ps = a#as" and "ls = x#xs" and "x \<noteq> a"
proof (cases ps)
  case Nil
  then show ?thesis using pfx by simp
next
  case (Cons a as)
  note c = `ps = a#as`
  show ?thesis
  proof (cases ls)
    case Nil then show ?thesis by (metis append_Nil2 pfx c1 same_prefixeq_nil)
  next
    case (Cons x xs)
    show ?thesis
    proof (cases "x = a")
      case True
      have "\<not> prefixeq as xs" using pfx c Cons True by simp
      with c Cons True show ?thesis by (rule c2)
    next
      case False
      with c Cons show ?thesis by (rule c3)
    qed
  qed
qed

lemma not_prefixeq_induct [consumes 1, case_names Nil Neq Eq]:
  assumes np: "\<not> prefixeq ps ls"
    and base: "\<And>x xs. P (x#xs) []"
    and r1: "\<And>x xs y ys. x \<noteq> y \<Longrightarrow> P (x#xs) (y#ys)"
    and r2: "\<And>x xs y ys. \<lbrakk> x = y; \<not> prefixeq xs ys; P xs ys \<rbrakk> \<Longrightarrow> P (x#xs) (y#ys)"
  shows "P ps ls" using np
proof (induct ls arbitrary: ps)
  case Nil then show ?case
    by (auto simp: neq_Nil_conv elim!: not_prefixeq_cases intro!: base)
next
  case (Cons y ys)
  then have npfx: "\<not> prefixeq ps (y # ys)" by simp
  then obtain x xs where pv: "ps = x # xs"
    by (rule not_prefixeq_cases) auto
  show ?case by (metis Cons.hyps Cons_prefixeq_Cons npfx pv r1 r2)
qed


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

inductive list_emb :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for P :: "('a \<Rightarrow> 'a \<Rightarrow> bool)"
where
  list_emb_Nil [intro, simp]: "list_emb P [] ys"
| list_emb_Cons [intro] : "list_emb P xs ys \<Longrightarrow> list_emb P xs (y#ys)"
| list_emb_Cons2 [intro]: "P\<^sup>=\<^sup>= x y \<Longrightarrow> list_emb P xs ys \<Longrightarrow> list_emb P (x#xs) (y#ys)"

lemma list_emb_Nil2 [simp]:
  assumes "list_emb P xs []" shows "xs = []"
  using assms by (cases rule: list_emb.cases) auto

lemma list_emb_refl [simp, intro!]:
  "list_emb P xs xs"
  by (induct xs) auto

lemma list_emb_Cons_Nil [simp]: "list_emb P (x#xs) [] = False"
proof -
  { assume "list_emb P (x#xs) []"
    from list_emb_Nil2 [OF this] have False by simp
  } moreover {
    assume False
    then have "list_emb P (x#xs) []" by simp
  } ultimately show ?thesis by blast
qed

lemma list_emb_append2 [intro]: "list_emb P xs ys \<Longrightarrow> list_emb P xs (zs @ ys)"
  by (induct zs) auto

lemma list_emb_prefix [intro]:
  assumes "list_emb P xs ys" shows "list_emb P xs (ys @ zs)"
  using assms
  by (induct arbitrary: zs) auto

lemma list_emb_ConsD:
  assumes "list_emb P (x#xs) ys"
  shows "\<exists>us v vs. ys = us @ v # vs \<and> P\<^sup>=\<^sup>= x v \<and> list_emb P xs vs"
using assms
proof (induct x \<equiv> "x # xs" ys arbitrary: x xs)
  case list_emb_Cons
  then show ?case by (metis append_Cons)
next
  case (list_emb_Cons2 x y xs ys)
  then show ?case by blast
qed

lemma list_emb_appendD:
  assumes "list_emb P (xs @ ys) zs"
  shows "\<exists>us vs. zs = us @ vs \<and> list_emb P xs us \<and> list_emb P ys vs"
using assms
proof (induction xs arbitrary: ys zs)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  then obtain us v vs where
    zs: "zs = us @ v # vs" and p: "P\<^sup>=\<^sup>= x v" and lh: "list_emb P (xs @ ys) vs"
    by (auto dest: list_emb_ConsD)
  obtain sk\<^sub>0 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" and sk\<^sub>1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    sk: "\<forall>x\<^sub>0 x\<^sub>1. \<not> list_emb P (xs @ x\<^sub>0) x\<^sub>1 \<or> sk\<^sub>0 x\<^sub>0 x\<^sub>1 @ sk\<^sub>1 x\<^sub>0 x\<^sub>1 = x\<^sub>1 \<and> list_emb P xs (sk\<^sub>0 x\<^sub>0 x\<^sub>1) \<and> list_emb P x\<^sub>0 (sk\<^sub>1 x\<^sub>0 x\<^sub>1)"
    using Cons(1) by (metis (no_types))
  hence "\<forall>x\<^sub>2. list_emb P (x # xs) (x\<^sub>2 @ v # sk\<^sub>0 ys vs)" using p lh by auto
  thus ?case using lh zs sk by (metis (no_types) append_Cons append_assoc)
qed

lemma list_emb_suffix:
  assumes "list_emb P xs ys" and "suffix ys zs"
  shows "list_emb P xs zs"
  using assms(2) and list_emb_append2 [OF assms(1)] by (auto simp: suffix_def)

lemma list_emb_suffixeq:
  assumes "list_emb P xs ys" and "suffixeq ys zs"
  shows "list_emb P xs zs"
  using assms and list_emb_suffix unfolding suffixeq_suffix_reflclp_conv by auto

lemma list_emb_length: "list_emb P xs ys \<Longrightarrow> length xs \<le> length ys"
  by (induct rule: list_emb.induct) auto

lemma list_emb_trans:
  assumes "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A; P x y; P y z\<rbrakk> \<Longrightarrow> P x z"
  shows "\<And>xs ys zs. \<lbrakk>xs \<in> lists A; ys \<in> lists A; zs \<in> lists A;
    list_emb P xs ys; list_emb P ys zs\<rbrakk> \<Longrightarrow> list_emb P xs zs"
proof -
  fix xs ys zs
  assume "list_emb P xs ys" and "list_emb P ys zs"
    and "xs \<in> lists A" and "ys \<in> lists A" and "zs \<in> lists A"
  then show "list_emb P xs zs"
  proof (induction arbitrary: zs)
    case list_emb_Nil show ?case by blast
  next
    case (list_emb_Cons xs ys y)
    from list_emb_ConsD [OF `list_emb P (y#ys) zs`] obtain us v vs
      where zs: "zs = us @ v # vs" and "P\<^sup>=\<^sup>= y v" and "list_emb P ys vs" by blast
    then have "list_emb P ys (v#vs)" by blast
    then have "list_emb P ys zs" unfolding zs by (rule list_emb_append2)
    from list_emb_Cons.IH [OF this] and list_emb_Cons.prems show ?case by simp
  next
    case (list_emb_Cons2 x y xs ys)
    from list_emb_ConsD [OF `list_emb P (y#ys) zs`] obtain us v vs
      where zs: "zs = us @ v # vs" and "P\<^sup>=\<^sup>= y v" and "list_emb P ys vs" by blast
    with list_emb_Cons2 have "list_emb P xs vs" by simp
    moreover have "P\<^sup>=\<^sup>= x v"
    proof -
      from zs and `zs \<in> lists A` have "v \<in> A" by auto
      moreover have "x \<in> A" and "y \<in> A" using list_emb_Cons2 by simp_all
      ultimately show ?thesis
        using `P\<^sup>=\<^sup>= x y` and `P\<^sup>=\<^sup>= y v` and assms
        by blast
    qed
    ultimately have "list_emb P (x#xs) (v#vs)" by blast
    then show ?case unfolding zs by (rule list_emb_append2)
  qed
qed


subsection {* Sublists (special case of homeomorphic embedding) *}

abbreviation sublisteq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "sublisteq xs ys \<equiv> list_emb (op =) xs ys"

lemma sublisteq_Cons2: "sublisteq xs ys \<Longrightarrow> sublisteq (x#xs) (x#ys)" by auto

lemma sublisteq_same_length:
  assumes "sublisteq xs ys" and "length xs = length ys" shows "xs = ys"
  using assms by (induct) (auto dest: list_emb_length)

lemma not_sublisteq_length [simp]: "length ys < length xs \<Longrightarrow> \<not> sublisteq xs ys"
  by (metis list_emb_length linorder_not_less)

lemma [code]:
  "list_emb P [] ys \<longleftrightarrow> True"
  "list_emb P (x#xs) [] \<longleftrightarrow> False"
  by (simp_all)

lemma sublisteq_Cons': "sublisteq (x#xs) ys \<Longrightarrow> sublisteq xs ys"
  by (induct xs, simp, blast dest: list_emb_ConsD)

lemma sublisteq_Cons2':
  assumes "sublisteq (x#xs) (x#ys)" shows "sublisteq xs ys"
  using assms by (cases) (rule sublisteq_Cons')

lemma sublisteq_Cons2_neq:
  assumes "sublisteq (x#xs) (y#ys)"
  shows "x \<noteq> y \<Longrightarrow> sublisteq (x#xs) ys"
  using assms by (cases) auto

lemma sublisteq_Cons2_iff [simp, code]:
  "sublisteq (x#xs) (y#ys) = (if x = y then sublisteq xs ys else sublisteq (x#xs) ys)"
  by (metis list_emb_Cons sublisteq_Cons2 sublisteq_Cons2' sublisteq_Cons2_neq)

lemma sublisteq_append': "sublisteq (zs @ xs) (zs @ ys) \<longleftrightarrow> sublisteq xs ys"
  by (induct zs) simp_all

lemma sublisteq_refl [simp, intro!]: "sublisteq xs xs" by (induct xs) simp_all

lemma sublisteq_antisym:
  assumes "sublisteq xs ys" and "sublisteq ys xs"
  shows "xs = ys"
using assms
proof (induct)
  case list_emb_Nil
  from list_emb_Nil2 [OF this] show ?case by simp
next
  case list_emb_Cons2
  thus ?case by simp
next
  case list_emb_Cons
  hence False using sublisteq_Cons' by fastforce
  thus ?case ..
qed

lemma sublisteq_trans: "sublisteq xs ys \<Longrightarrow> sublisteq ys zs \<Longrightarrow> sublisteq xs zs"
  by (rule list_emb_trans [of UNIV "op ="]) auto

lemma sublisteq_append_le_same_iff: "sublisteq (xs @ ys) ys \<longleftrightarrow> xs = []"
  by (auto dest: list_emb_length)

lemma list_emb_append_mono:
  "\<lbrakk> list_emb P xs xs'; list_emb P ys ys' \<rbrakk> \<Longrightarrow> list_emb P (xs@ys) (xs'@ys')"
  apply (induct rule: list_emb.induct)
    apply (metis eq_Nil_appendI list_emb_append2)
   apply (metis append_Cons list_emb_Cons)
  apply (metis append_Cons list_emb_Cons2)
  done


subsection {* Appending elements *}

lemma sublisteq_append [simp]:
  "sublisteq (xs @ zs) (ys @ zs) \<longleftrightarrow> sublisteq xs ys" (is "?l = ?r")
proof
  { fix xs' ys' xs ys zs :: "'a list" assume "sublisteq xs' ys'"
    then have "xs' = xs @ zs & ys' = ys @ zs \<longrightarrow> sublisteq xs ys"
    proof (induct arbitrary: xs ys zs)
      case list_emb_Nil show ?case by simp
    next
      case (list_emb_Cons xs' ys' x)
      { assume "ys=[]" then have ?case using list_emb_Cons(1) by auto }
      moreover
      { fix us assume "ys = x#us"
        then have ?case using list_emb_Cons(2) by(simp add: list_emb.list_emb_Cons) }
      ultimately show ?case by (auto simp:Cons_eq_append_conv)
    next
      case (list_emb_Cons2 x y xs' ys')
      { assume "xs=[]" then have ?case using list_emb_Cons2(1) by auto }
      moreover
      { fix us vs assume "xs=x#us" "ys=x#vs" then have ?case using list_emb_Cons2 by auto}
      moreover
      { fix us assume "xs=x#us" "ys=[]" then have ?case using list_emb_Cons2(2) by bestsimp }
      ultimately show ?case using `op =\<^sup>=\<^sup>= x y` by (auto simp: Cons_eq_append_conv)
    qed }
  moreover assume ?l
  ultimately show ?r by blast
next
  assume ?r then show ?l by (metis list_emb_append_mono sublisteq_refl)
qed

lemma sublisteq_drop_many: "sublisteq xs ys \<Longrightarrow> sublisteq xs (zs @ ys)"
  by (induct zs) auto

lemma sublisteq_rev_drop_many: "sublisteq xs ys \<Longrightarrow> sublisteq xs (ys @ zs)"
  by (metis append_Nil2 list_emb_Nil list_emb_append_mono)


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
    case list_emb_Nil show ?case by (metis sublist_empty)
  next
    case (list_emb_Cons xs ys x)
    then obtain N where "xs = sublist ys N" by blast
    then have "xs = sublist (x#ys) (Suc ` N)"
      by (clarsimp simp add:sublist_Cons inj_image_mem_iff)
    then show ?case by blast
  next
    case (list_emb_Cons2 x y xs ys)
    then obtain N where "xs = sublist ys N" by blast
    then have "x#xs = sublist (x#ys) (insert 0 (Suc ` N))"
      by (clarsimp simp add:sublist_Cons inj_image_mem_iff)
    moreover from list_emb_Cons2 have "x = y" by simp
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
