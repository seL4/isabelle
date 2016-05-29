(*  Title:      HOL/Library/Sublist.thy
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
    Author:     Christian Sternagel, JAIST
*)

section \<open>List prefixes, suffixes, and homeomorphic embedding\<close>

theory Sublist
imports Main
begin

subsection \<open>Prefix order on lists\<close>

definition prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "prefix xs ys \<longleftrightarrow> (\<exists>zs. ys = xs @ zs)"

definition strict_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "strict_prefix xs ys \<longleftrightarrow> prefix xs ys \<and> xs \<noteq> ys"

interpretation prefix_order: order prefix strict_prefix
  by standard (auto simp: prefix_def strict_prefix_def)

interpretation prefix_bot: order_bot Nil prefix strict_prefix
  by standard (simp add: prefix_def)

lemma prefixI [intro?]: "ys = xs @ zs \<Longrightarrow> prefix xs ys"
  unfolding prefix_def by blast

lemma prefixE [elim?]:
  assumes "prefix xs ys"
  obtains zs where "ys = xs @ zs"
  using assms unfolding prefix_def by blast

lemma strict_prefixI' [intro?]: "ys = xs @ z # zs \<Longrightarrow> strict_prefix xs ys"
  unfolding strict_prefix_def prefix_def by blast

lemma strict_prefixE' [elim?]:
  assumes "strict_prefix xs ys"
  obtains z zs where "ys = xs @ z # zs"
proof -
  from \<open>strict_prefix xs ys\<close> obtain us where "ys = xs @ us" and "xs \<noteq> ys"
    unfolding strict_prefix_def prefix_def by blast
  with that show ?thesis by (auto simp add: neq_Nil_conv)
qed

(* FIXME rm *)
lemma strict_prefixI [intro?]: "prefix xs ys \<Longrightarrow> xs \<noteq> ys \<Longrightarrow> strict_prefix xs ys"
by(fact prefix_order.le_neq_trans)

lemma strict_prefixE [elim?]:
  fixes xs ys :: "'a list"
  assumes "strict_prefix xs ys"
  obtains "prefix xs ys" and "xs \<noteq> ys"
  using assms unfolding strict_prefix_def by blast


subsection \<open>Basic properties of prefixes\<close>

(* FIXME rm *)
theorem Nil_prefix [iff]: "prefix [] xs"
by(fact prefix_bot.bot_least)

(* FIXME rm *)
theorem prefix_Nil [simp]: "(prefix xs []) = (xs = [])"
by(fact prefix_bot.bot_unique)

lemma prefix_snoc [simp]: "prefix xs (ys @ [y]) \<longleftrightarrow> xs = ys @ [y] \<or> prefix xs ys"
proof
  assume "prefix xs (ys @ [y])"
  then obtain zs where zs: "ys @ [y] = xs @ zs" ..
  show "xs = ys @ [y] \<or> prefix xs ys"
    by (metis append_Nil2 butlast_append butlast_snoc prefixI zs)
next
  assume "xs = ys @ [y] \<or> prefix xs ys"
  then show "prefix xs (ys @ [y])"
    by (metis prefix_order.eq_iff prefix_order.order_trans prefixI)
qed

lemma Cons_prefix_Cons [simp]: "prefix (x # xs) (y # ys) = (x = y \<and> prefix xs ys)"
  by (auto simp add: prefix_def)

lemma prefix_code [code]:
  "prefix [] xs \<longleftrightarrow> True"
  "prefix (x # xs) [] \<longleftrightarrow> False"
  "prefix (x # xs) (y # ys) \<longleftrightarrow> x = y \<and> prefix xs ys"
  by simp_all

lemma same_prefix_prefix [simp]: "prefix (xs @ ys) (xs @ zs) = prefix ys zs"
  by (induct xs) simp_all

lemma same_prefix_nil [iff]: "prefix (xs @ ys) xs = (ys = [])"
  by (metis append_Nil2 append_self_conv prefix_order.eq_iff prefixI)

lemma prefix_prefix [simp]: "prefix xs ys \<Longrightarrow> prefix xs (ys @ zs)"
  by (metis prefix_order.le_less_trans prefixI strict_prefixE strict_prefixI)

lemma append_prefixD: "prefix (xs @ ys) zs \<Longrightarrow> prefix xs zs"
  by (auto simp add: prefix_def)

theorem prefix_Cons: "prefix xs (y # ys) = (xs = [] \<or> (\<exists>zs. xs = y # zs \<and> prefix zs ys))"
  by (cases xs) (auto simp add: prefix_def)

theorem prefix_append:
  "prefix xs (ys @ zs) = (prefix xs ys \<or> (\<exists>us. xs = ys @ us \<and> prefix us zs))"
  apply (induct zs rule: rev_induct)
   apply force
  apply (simp del: append_assoc add: append_assoc [symmetric])
  apply (metis append_eq_appendI)
  done

lemma append_one_prefix:
  "prefix xs ys \<Longrightarrow> length xs < length ys \<Longrightarrow> prefix (xs @ [ys ! length xs]) ys"
  proof (unfold prefix_def)
    assume a1: "\<exists>zs. ys = xs @ zs"
    then obtain sk :: "'a list" where sk: "ys = xs @ sk" by fastforce
    assume a2: "length xs < length ys"
    have f1: "\<And>v. ([]::'a list) @ v = v" using append_Nil2 by simp
    have "[] \<noteq> sk" using a1 a2 sk less_not_refl by force
    hence "\<exists>v. xs @ hd sk # v = ys" using sk by (metis hd_Cons_tl)
    thus "\<exists>zs. ys = (xs @ [ys ! length xs]) @ zs" using f1 by fastforce
  qed

theorem prefix_length_le: "prefix xs ys \<Longrightarrow> length xs \<le> length ys"
  by (auto simp add: prefix_def)

lemma prefix_same_cases:
  "prefix (xs\<^sub>1::'a list) ys \<Longrightarrow> prefix xs\<^sub>2 ys \<Longrightarrow> prefix xs\<^sub>1 xs\<^sub>2 \<or> prefix xs\<^sub>2 xs\<^sub>1"
  unfolding prefix_def by (force simp: append_eq_append_conv2)

lemma prefix_length_prefix:
  "prefix ps xs \<Longrightarrow> prefix qs xs \<Longrightarrow> length ps \<le> length qs \<Longrightarrow> prefix ps qs"
by (auto simp: prefix_def) (metis append_Nil2 append_eq_append_conv_if)

lemma set_mono_prefix: "prefix xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (auto simp add: prefix_def)

lemma take_is_prefix: "prefix (take n xs) xs"
  unfolding prefix_def by (metis append_take_drop_id)

lemma prefixeq_butlast: "prefix (butlast xs) xs"
by (simp add: butlast_conv_take take_is_prefix)

lemma map_prefixI: "prefix xs ys \<Longrightarrow> prefix (map f xs) (map f ys)"
  by (auto simp: prefix_def)

lemma prefix_length_less: "strict_prefix xs ys \<Longrightarrow> length xs < length ys"
  by (auto simp: strict_prefix_def prefix_def)

lemma prefix_snocD: "prefix (xs@[x]) ys \<Longrightarrow> strict_prefix xs ys"
  by (simp add: strict_prefixI' prefix_order.dual_order.strict_trans1)

lemma strict_prefix_simps [simp, code]:
  "strict_prefix xs [] \<longleftrightarrow> False"
  "strict_prefix [] (x # xs) \<longleftrightarrow> True"
  "strict_prefix (x # xs) (y # ys) \<longleftrightarrow> x = y \<and> strict_prefix xs ys"
  by (simp_all add: strict_prefix_def cong: conj_cong)

lemma take_strict_prefix: "strict_prefix xs ys \<Longrightarrow> strict_prefix (take n xs) ys"
  apply (induct n arbitrary: xs ys)
   apply (case_tac ys; simp)
  apply (metis prefix_order.less_trans strict_prefixI take_is_prefix)
  done

lemma not_prefix_cases:
  assumes pfx: "\<not> prefix ps ls"
  obtains
    (c1) "ps \<noteq> []" and "ls = []"
  | (c2) a as x xs where "ps = a#as" and "ls = x#xs" and "x = a" and "\<not> prefix as xs"
  | (c3) a as x xs where "ps = a#as" and "ls = x#xs" and "x \<noteq> a"
proof (cases ps)
  case Nil
  then show ?thesis using pfx by simp
next
  case (Cons a as)
  note c = \<open>ps = a#as\<close>
  show ?thesis
  proof (cases ls)
    case Nil then show ?thesis by (metis append_Nil2 pfx c1 same_prefix_nil)
  next
    case (Cons x xs)
    show ?thesis
    proof (cases "x = a")
      case True
      have "\<not> prefix as xs" using pfx c Cons True by simp
      with c Cons True show ?thesis by (rule c2)
    next
      case False
      with c Cons show ?thesis by (rule c3)
    qed
  qed
qed

lemma not_prefix_induct [consumes 1, case_names Nil Neq Eq]:
  assumes np: "\<not> prefix ps ls"
    and base: "\<And>x xs. P (x#xs) []"
    and r1: "\<And>x xs y ys. x \<noteq> y \<Longrightarrow> P (x#xs) (y#ys)"
    and r2: "\<And>x xs y ys. \<lbrakk> x = y; \<not> prefix xs ys; P xs ys \<rbrakk> \<Longrightarrow> P (x#xs) (y#ys)"
  shows "P ps ls" using np
proof (induct ls arbitrary: ps)
  case Nil then show ?case
    by (auto simp: neq_Nil_conv elim!: not_prefix_cases intro!: base)
next
  case (Cons y ys)
  then have npfx: "\<not> prefix ps (y # ys)" by simp
  then obtain x xs where pv: "ps = x # xs"
    by (rule not_prefix_cases) auto
  show ?case by (metis Cons.hyps Cons_prefix_Cons npfx pv r1 r2)
qed


subsection \<open>Prefixes\<close>

fun prefixes where
"prefixes [] = [[]]" |
"prefixes (x#xs) = [] # map (op # x) (prefixes xs)"

lemma in_set_prefixes[simp]: "xs \<in> set (prefixes ys) \<longleftrightarrow> prefix xs ys"
by (induction "xs" arbitrary: "ys"; rename_tac "ys", case_tac "ys"; auto)

lemma length_prefixes[simp]: "length (prefixes xs) = length xs+1"
by (induction xs) auto

lemma prefixes_snoc[simp]:
  "prefixes (xs@[x]) = prefixes xs @ [xs@[x]]"
by (induction xs) auto

lemma prefixes_eq_Snoc:
  "prefixes ys = xs @ [x] \<longleftrightarrow>
  (ys = [] \<and> xs = [] \<or> (\<exists>z zs. ys = zs@[z] \<and> xs = prefixes zs)) \<and> x = ys"
by (cases ys rule: rev_cases) auto


subsection \<open>Longest Common Prefix\<close>

definition Longest_common_prefix :: "'a list set \<Rightarrow> 'a list" where
"Longest_common_prefix L = (GREATEST ps WRT length. \<forall>xs \<in> L. prefix ps xs)"

lemma Longest_common_prefix_ex: "L \<noteq> {} \<Longrightarrow>
  \<exists>ps. (\<forall>xs \<in> L. prefix ps xs) \<and> (\<forall>qs. (\<forall>xs \<in> L. prefix qs xs) \<longrightarrow> size qs \<le> size ps)"
  (is "_ \<Longrightarrow> \<exists>ps. ?P L ps")
proof(induction "LEAST n. \<exists>xs \<in>L. n = length xs" arbitrary: L)
  case 0
  have "[] : L" using "0.hyps" LeastI[of "\<lambda>n. \<exists>xs\<in>L. n = length xs"] \<open>L \<noteq> {}\<close>
    by auto
  hence "?P L []" by(auto)
  thus ?case ..
next
  case (Suc n)
  let ?EX = "\<lambda>n. \<exists>xs\<in>L. n = length xs"
  obtain x xs where xxs: "x#xs \<in> L" "size xs = n" using Suc.prems Suc.hyps(2)
    by(metis LeastI_ex[of ?EX] Suc_length_conv ex_in_conv)
  hence "[] \<notin> L" using Suc.hyps(2) by auto
  show ?case
  proof (cases "\<forall>xs \<in> L. \<exists>ys. xs = x#ys")
    case True
    let ?L = "{ys. x#ys \<in> L}"
    have 1: "(LEAST n. \<exists>xs \<in> ?L. n = length xs) = n"
      using xxs Suc.prems Suc.hyps(2) Least_le[of "?EX"]
      by - (rule Least_equality, fastforce+)
    have 2: "?L \<noteq> {}" using \<open>x # xs \<in> L\<close> by auto
    from Suc.hyps(1)[OF 1[symmetric] 2] obtain ps where IH: "?P ?L ps" ..
    { fix qs
      assume "\<forall>qs. (\<forall>xa. x # xa \<in> L \<longrightarrow> prefix qs xa) \<longrightarrow> length qs \<le> length ps"
      and "\<forall>xs\<in>L. prefix qs xs"
      hence "length (tl qs) \<le> length ps"
        by (metis Cons_prefix_Cons hd_Cons_tl list.sel(2) Nil_prefix) 
      hence "length qs \<le> Suc (length ps)" by auto
    }
    hence "?P L (x#ps)" using True IH by auto
    thus ?thesis ..
  next
    case False
    then obtain y ys where yys: "x\<noteq>y" "y#ys \<in> L" using \<open>[] \<notin> L\<close>
      by (auto) (metis list.exhaust)
    have "\<forall>qs. (\<forall>xs\<in>L. prefix qs xs) \<longrightarrow> qs = []" using yys \<open>x#xs \<in> L\<close>
      by auto (metis Cons_prefix_Cons prefix_Cons)
    hence "?P L []" by auto
    thus ?thesis ..
  qed
qed

lemma Longest_common_prefix_unique: "L \<noteq> {} \<Longrightarrow>
  \<exists>! ps. (\<forall>xs \<in> L. prefix ps xs) \<and> (\<forall>qs. (\<forall>xs \<in> L. prefix qs xs) \<longrightarrow> size qs \<le> size ps)"
by(rule ex_ex1I[OF Longest_common_prefix_ex];
   meson equals0I prefix_length_prefix prefix_order.antisym)

lemma Longest_common_prefix_eq:
 "\<lbrakk> L \<noteq> {};  \<forall>xs \<in> L. prefix ps xs;
    \<forall>qs. (\<forall>xs \<in> L. prefix qs xs) \<longrightarrow> size qs \<le> size ps \<rbrakk>
  \<Longrightarrow> Longest_common_prefix L = ps"
unfolding Longest_common_prefix_def GreatestM_def
by(rule some1_equality[OF Longest_common_prefix_unique]) auto

lemma Longest_common_prefix_prefix:
  "xs \<in> L \<Longrightarrow> prefix (Longest_common_prefix L) xs"
unfolding Longest_common_prefix_def GreatestM_def
by(rule someI2_ex[OF Longest_common_prefix_ex]) auto

lemma Longest_common_prefix_longest:
  "L \<noteq> {} \<Longrightarrow> \<forall>xs\<in>L. prefix ps xs \<Longrightarrow> length ps \<le> length(Longest_common_prefix L)"
unfolding Longest_common_prefix_def GreatestM_def
by(rule someI2_ex[OF Longest_common_prefix_ex]) auto

lemma Longest_common_prefix_max_prefix:
  "L \<noteq> {} \<Longrightarrow> \<forall>xs\<in>L. prefix ps xs \<Longrightarrow> prefix ps (Longest_common_prefix L)"
by(metis Longest_common_prefix_prefix Longest_common_prefix_longest
     prefix_length_prefix ex_in_conv)

lemma Longest_common_prefix_Nil: "[] \<in> L \<Longrightarrow> Longest_common_prefix L = []"
using Longest_common_prefix_prefix prefix_Nil by blast

lemma Longest_common_prefix_image_Cons: "L \<noteq> {} \<Longrightarrow>
  Longest_common_prefix (op # x ` L) = x # Longest_common_prefix L"
apply(rule Longest_common_prefix_eq)
  apply(simp)
 apply (simp add: Longest_common_prefix_prefix)
apply simp
by(metis Longest_common_prefix_longest[of L] Cons_prefix_Cons Nitpick.size_list_simp(2)
     Suc_le_mono hd_Cons_tl order.strict_implies_order zero_less_Suc)

lemma Longest_common_prefix_eq_Cons: assumes "L \<noteq> {}" "[] \<notin> L"  "\<forall>xs\<in>L. hd xs = x"
shows "Longest_common_prefix L = x # Longest_common_prefix {ys. x#ys \<in> L}"
proof -
  have "L = op # x ` {ys. x#ys \<in> L}" using assms(2,3)
    by (auto simp: image_def)(metis hd_Cons_tl)
  thus ?thesis
    by (metis Longest_common_prefix_image_Cons image_is_empty assms(1))
qed

lemma Longest_common_prefix_eq_Nil:
  "\<lbrakk>x#ys \<in> L; y#zs \<in> L; x \<noteq> y \<rbrakk> \<Longrightarrow> Longest_common_prefix L = []"
by (metis Longest_common_prefix_prefix list.inject prefix_Cons)


fun longest_common_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"longest_common_prefix (x#xs) (y#ys) =
  (if x=y then x # longest_common_prefix xs ys else [])" |
"longest_common_prefix _ _ = []"

lemma longest_common_prefix_prefix1:
  "prefix (longest_common_prefix xs ys) xs"
by(induction xs ys rule: longest_common_prefix.induct) auto

lemma longest_common_prefix_prefix2:
  "prefix (longest_common_prefix xs ys) ys"
by(induction xs ys rule: longest_common_prefix.induct) auto

lemma longest_common_prefix_max_prefix:
  "\<lbrakk> prefix ps xs; prefix ps ys \<rbrakk>
   \<Longrightarrow> prefix ps (longest_common_prefix xs ys)"
by(induction xs ys arbitrary: ps rule: longest_common_prefix.induct)
  (auto simp: prefix_Cons)


subsection \<open>Parallel lists\<close>

definition parallel :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infixl "\<parallel>" 50)
  where "(xs \<parallel> ys) = (\<not> prefix xs ys \<and> \<not> prefix ys xs)"

lemma parallelI [intro]: "\<not> prefix xs ys \<Longrightarrow> \<not> prefix ys xs \<Longrightarrow> xs \<parallel> ys"
  unfolding parallel_def by blast

lemma parallelE [elim]:
  assumes "xs \<parallel> ys"
  obtains "\<not> prefix xs ys \<and> \<not> prefix ys xs"
  using assms unfolding parallel_def by blast

theorem prefix_cases:
  obtains "prefix xs ys" | "strict_prefix ys xs" | "xs \<parallel> ys"
  unfolding parallel_def strict_prefix_def by blast

theorem parallel_decomp:
  "xs \<parallel> ys \<Longrightarrow> \<exists>as b bs c cs. b \<noteq> c \<and> xs = as @ b # bs \<and> ys = as @ c # cs"
proof (induct xs rule: rev_induct)
  case Nil
  then have False by auto
  then show ?case ..
next
  case (snoc x xs)
  show ?case
  proof (rule prefix_cases)
    assume le: "prefix xs ys"
    then obtain ys' where ys: "ys = xs @ ys'" ..
    show ?thesis
    proof (cases ys')
      assume "ys' = []"
      then show ?thesis by (metis append_Nil2 parallelE prefixI snoc.prems ys)
    next
      fix c cs assume ys': "ys' = c # cs"
      have "x \<noteq> c" using snoc.prems ys ys' by fastforce
      thus "\<exists>as b bs c cs. b \<noteq> c \<and> xs @ [x] = as @ b # bs \<and> ys = as @ c # cs"
        using ys ys' by blast
    qed
  next
    assume "strict_prefix ys xs"
    then have "prefix ys (xs @ [x])" by (simp add: strict_prefix_def)
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
      induct rule: not_prefix_induct, simp+)+
  done

lemma parallel_appendI: "xs \<parallel> ys \<Longrightarrow> x = xs @ xs' \<Longrightarrow> y = ys @ ys' \<Longrightarrow> x \<parallel> y"
  by (simp add: parallel_append)

lemma parallel_commute: "a \<parallel> b \<longleftrightarrow> b \<parallel> a"
  unfolding parallel_def by auto


subsection \<open>Suffix order on lists\<close>

definition suffix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "suffix xs ys = (\<exists>zs. ys = zs @ xs)"

definition strict_suffix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "strict_suffix xs ys \<longleftrightarrow> (\<exists>us. ys = us @ xs \<and> us \<noteq> [])"

lemma strict_suffix_imp_suffix:
  "strict_suffix xs ys \<Longrightarrow> suffix xs ys"
  by (auto simp: suffix_def strict_suffix_def)

lemma suffixI [intro?]: "ys = zs @ xs \<Longrightarrow> suffix xs ys"
  unfolding suffix_def by blast

lemma suffixE [elim?]:
  assumes "suffix xs ys"
  obtains zs where "ys = zs @ xs"
  using assms unfolding suffix_def by blast

lemma suffix_refl [iff]: "suffix xs xs"
  by (auto simp add: suffix_def)

lemma suffix_trans:
  "suffix xs ys \<Longrightarrow> suffix ys zs \<Longrightarrow> suffix xs zs"
  by (auto simp: suffix_def)

lemma strict_suffix_trans:
  "\<lbrakk>strict_suffix xs ys; strict_suffix ys zs\<rbrakk> \<Longrightarrow> strict_suffix xs zs"
by (auto simp add: strict_suffix_def)

lemma suffix_antisym: "\<lbrakk>suffix xs ys; suffix ys xs\<rbrakk> \<Longrightarrow> xs = ys"
  by (auto simp add: suffix_def)

lemma suffix_tl [simp]: "suffix (tl xs) xs"
  by (induct xs) (auto simp: suffix_def)

lemma strict_suffix_tl [simp]: "xs \<noteq> [] \<Longrightarrow> strict_suffix (tl xs) xs"
  by (induct xs) (auto simp: strict_suffix_def)

lemma Nil_suffix [iff]: "suffix [] xs"
  by (simp add: suffix_def)

lemma suffix_Nil [simp]: "(suffix xs []) = (xs = [])"
  by (auto simp add: suffix_def)

lemma suffix_ConsI: "suffix xs ys \<Longrightarrow> suffix xs (y # ys)"
  by (auto simp add: suffix_def)

lemma suffix_ConsD: "suffix (x # xs) ys \<Longrightarrow> suffix xs ys"
  by (auto simp add: suffix_def)

lemma suffix_appendI: "suffix xs ys \<Longrightarrow> suffix xs (zs @ ys)"
  by (auto simp add: suffix_def)

lemma suffix_appendD: "suffix (zs @ xs) ys \<Longrightarrow> suffix xs ys"
  by (auto simp add: suffix_def)

lemma strict_suffix_set_subset: "strict_suffix xs ys \<Longrightarrow> set xs \<subseteq> set ys"
by (auto simp: strict_suffix_def)

lemma suffix_set_subset: "suffix xs ys \<Longrightarrow> set xs \<subseteq> set ys"
by (auto simp: suffix_def)

lemma suffix_ConsD2: "suffix (x # xs) (y # ys) \<Longrightarrow> suffix xs ys"
proof -
  assume "suffix (x # xs) (y # ys)"
  then obtain zs where "y # ys = zs @ x # xs" ..
  then show ?thesis
    by (induct zs) (auto intro!: suffix_appendI suffix_ConsI)
qed

lemma suffix_to_prefix [code]: "suffix xs ys \<longleftrightarrow> prefix (rev xs) (rev ys)"
proof
  assume "suffix xs ys"
  then obtain zs where "ys = zs @ xs" ..
  then have "rev ys = rev xs @ rev zs" by simp
  then show "prefix (rev xs) (rev ys)" ..
next
  assume "prefix (rev xs) (rev ys)"
  then obtain zs where "rev ys = rev xs @ zs" ..
  then have "rev (rev ys) = rev zs @ rev (rev xs)" by simp
  then have "ys = rev zs @ xs" by simp
  then show "suffix xs ys" ..
qed

lemma distinct_suffix: "distinct ys \<Longrightarrow> suffix xs ys \<Longrightarrow> distinct xs"
  by (clarsimp elim!: suffixE)

lemma suffix_map: "suffix xs ys \<Longrightarrow> suffix (map f xs) (map f ys)"
  by (auto elim!: suffixE intro: suffixI)

lemma suffix_drop: "suffix (drop n as) as"
  unfolding suffix_def
  apply (rule exI [where x = "take n as"])
  apply simp
  done

lemma suffix_take: "suffix xs ys \<Longrightarrow> ys = take (length ys - length xs) ys @ xs"
  by (auto elim!: suffixE)

lemma strict_suffix_reflclp_conv: "strict_suffix\<^sup>=\<^sup>= = suffix"
by (intro ext) (auto simp: suffix_def strict_suffix_def)

lemma suffix_lists: "suffix xs ys \<Longrightarrow> ys \<in> lists A \<Longrightarrow> xs \<in> lists A"
  unfolding suffix_def by auto

lemma parallelD1: "x \<parallel> y \<Longrightarrow> \<not> prefix x y"
  by blast

lemma parallelD2: "x \<parallel> y \<Longrightarrow> \<not> prefix y x"
  by blast

lemma parallel_Nil1 [simp]: "\<not> x \<parallel> []"
  unfolding parallel_def by simp

lemma parallel_Nil2 [simp]: "\<not> [] \<parallel> x"
  unfolding parallel_def by simp

lemma Cons_parallelI1: "a \<noteq> b \<Longrightarrow> a # as \<parallel> b # bs"
  by auto

lemma Cons_parallelI2: "\<lbrakk> a = b; as \<parallel> bs \<rbrakk> \<Longrightarrow> a # as \<parallel> b # bs"
  by (metis Cons_prefix_Cons parallelE parallelI)

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


subsection \<open>Homeomorphic embedding on lists\<close>

inductive list_emb :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for P :: "('a \<Rightarrow> 'a \<Rightarrow> bool)"
where
  list_emb_Nil [intro, simp]: "list_emb P [] ys"
| list_emb_Cons [intro] : "list_emb P xs ys \<Longrightarrow> list_emb P xs (y#ys)"
| list_emb_Cons2 [intro]: "P x y \<Longrightarrow> list_emb P xs ys \<Longrightarrow> list_emb P (x#xs) (y#ys)"

lemma list_emb_mono:                         
  assumes "\<And>x y. P x y \<longrightarrow> Q x y"
  shows "list_emb P xs ys \<longrightarrow> list_emb Q xs ys"
proof                                        
  assume "list_emb P xs ys"                    
  then show "list_emb Q xs ys" by (induct) (auto simp: assms)
qed 

lemma list_emb_Nil2 [simp]:
  assumes "list_emb P xs []" shows "xs = []"
  using assms by (cases rule: list_emb.cases) auto

lemma list_emb_refl:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> P x x"
  shows "list_emb P xs xs"
  using assms by (induct xs) auto

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
  shows "\<exists>us v vs. ys = us @ v # vs \<and> P x v \<and> list_emb P xs vs"
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
    zs: "zs = us @ v # vs" and p: "P x v" and lh: "list_emb P (xs @ ys) vs"
    by (auto dest: list_emb_ConsD)
  obtain sk\<^sub>0 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" and sk\<^sub>1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    sk: "\<forall>x\<^sub>0 x\<^sub>1. \<not> list_emb P (xs @ x\<^sub>0) x\<^sub>1 \<or> sk\<^sub>0 x\<^sub>0 x\<^sub>1 @ sk\<^sub>1 x\<^sub>0 x\<^sub>1 = x\<^sub>1 \<and> list_emb P xs (sk\<^sub>0 x\<^sub>0 x\<^sub>1) \<and> list_emb P x\<^sub>0 (sk\<^sub>1 x\<^sub>0 x\<^sub>1)"
    using Cons(1) by (metis (no_types))
  hence "\<forall>x\<^sub>2. list_emb P (x # xs) (x\<^sub>2 @ v # sk\<^sub>0 ys vs)" using p lh by auto
  thus ?case using lh zs sk by (metis (no_types) append_Cons append_assoc)
qed

lemma list_emb_strict_suffix:
  assumes "list_emb P xs ys" and "strict_suffix ys zs"
  shows "list_emb P xs zs"
  using assms(2) and list_emb_append2 [OF assms(1)] by (auto simp: strict_suffix_def)

lemma list_emb_suffix:
  assumes "list_emb P xs ys" and "suffix ys zs"
  shows "list_emb P xs zs"
using assms and list_emb_strict_suffix
unfolding strict_suffix_reflclp_conv[symmetric] by auto

lemma list_emb_length: "list_emb P xs ys \<Longrightarrow> length xs \<le> length ys"
  by (induct rule: list_emb.induct) auto

lemma list_emb_trans:
  assumes "\<And>x y z. \<lbrakk>x \<in> set xs; y \<in> set ys; z \<in> set zs; P x y; P y z\<rbrakk> \<Longrightarrow> P x z"
  shows "\<lbrakk>list_emb P xs ys; list_emb P ys zs\<rbrakk> \<Longrightarrow> list_emb P xs zs"
proof -
  assume "list_emb P xs ys" and "list_emb P ys zs"
  then show "list_emb P xs zs" using assms
  proof (induction arbitrary: zs)
    case list_emb_Nil show ?case by blast
  next
    case (list_emb_Cons xs ys y)
    from list_emb_ConsD [OF \<open>list_emb P (y#ys) zs\<close>] obtain us v vs
      where zs: "zs = us @ v # vs" and "P\<^sup>=\<^sup>= y v" and "list_emb P ys vs" by blast
    then have "list_emb P ys (v#vs)" by blast
    then have "list_emb P ys zs" unfolding zs by (rule list_emb_append2)
    from list_emb_Cons.IH [OF this] and list_emb_Cons.prems show ?case by auto
  next
    case (list_emb_Cons2 x y xs ys)
    from list_emb_ConsD [OF \<open>list_emb P (y#ys) zs\<close>] obtain us v vs
      where zs: "zs = us @ v # vs" and "P y v" and "list_emb P ys vs" by blast
    with list_emb_Cons2 have "list_emb P xs vs" by auto
    moreover have "P x v"
    proof -
      from zs have "v \<in> set zs" by auto
      moreover have "x \<in> set (x#xs)" and "y \<in> set (y#ys)" by simp_all
      ultimately show ?thesis
        using \<open>P x y\<close> and \<open>P y v\<close> and list_emb_Cons2
        by blast
    qed
    ultimately have "list_emb P (x#xs) (v#vs)" by blast
    then show ?case unfolding zs by (rule list_emb_append2)
  qed
qed

lemma list_emb_set:
  assumes "list_emb P xs ys" and "x \<in> set xs"
  obtains y where "y \<in> set ys" and "P x y"
  using assms by (induct) auto


subsection \<open>Sublists (special case of homeomorphic embedding)\<close>

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
  by (rule list_emb_trans [of _ _ _ "op ="]) auto

lemma sublisteq_append_le_same_iff: "sublisteq (xs @ ys) ys \<longleftrightarrow> xs = []"
  by (auto dest: list_emb_length)

lemma list_emb_append_mono:
  "\<lbrakk> list_emb P xs xs'; list_emb P ys ys' \<rbrakk> \<Longrightarrow> list_emb P (xs@ys) (xs'@ys')"
  apply (induct rule: list_emb.induct)
    apply (metis eq_Nil_appendI list_emb_append2)
   apply (metis append_Cons list_emb_Cons)
  apply (metis append_Cons list_emb_Cons2)
  done


subsection \<open>Appending elements\<close>

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
      ultimately show ?case using \<open>op = x y\<close> by (auto simp: Cons_eq_append_conv)
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


subsection \<open>Relation to standard list operations\<close>

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
