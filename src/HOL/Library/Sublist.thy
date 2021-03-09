(*  Title:      HOL/Library/Sublist.thy
    Author:     Tobias Nipkow and Markus Wenzel, TU München
    Author:     Christian Sternagel, JAIST
    Author:     Manuel Eberl, TU München
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
theorem Nil_prefix [simp]: "prefix [] xs"
  by (fact prefix_bot.bot_least)

(* FIXME rm *)
theorem prefix_Nil [simp]: "(prefix xs []) = (xs = [])"
  by (fact prefix_bot.bot_unique)

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

lemma same_prefix_nil [simp]: "prefix (xs @ ys) xs = (ys = [])"
  by (metis append_Nil2 append_self_conv prefix_order.eq_iff prefixI)

lemma prefix_prefix [simp]: "prefix xs ys \<Longrightarrow> prefix xs (ys @ zs)"
  unfolding prefix_def by fastforce

lemma append_prefixD: "prefix (xs @ ys) zs \<Longrightarrow> prefix xs zs"
  by (auto simp add: prefix_def)

theorem prefix_Cons: "prefix xs (y # ys) = (xs = [] \<or> (\<exists>zs. xs = y # zs \<and> prefix zs ys))"
  by (cases xs) (auto simp add: prefix_def)

theorem prefix_append:
  "prefix xs (ys @ zs) = (prefix xs ys \<or> (\<exists>us. xs = ys @ us \<and> prefix us zs))"
  apply (induct zs rule: rev_induct)
   apply force
  apply (simp flip: append_assoc)
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

lemma takeWhile_is_prefix: "prefix (takeWhile P xs) xs"
  unfolding prefix_def by (metis takeWhile_dropWhile_id)

lemma prefixeq_butlast: "prefix (butlast xs) xs"
by (simp add: butlast_conv_take take_is_prefix)

lemma prefix_map_rightE:
  assumes "prefix xs (map f ys)"
  shows   "\<exists>xs'. prefix xs' ys \<and> xs = map f xs'"
proof -
  define n where "n = length xs"
  have "xs = take n (map f ys)"
    using assms by (auto simp: prefix_def n_def)
  thus ?thesis
    by (intro exI[of _ "take n ys"]) (auto simp: take_map take_is_prefix)
qed

lemma map_mono_prefix: "prefix xs ys \<Longrightarrow> prefix (map f xs) (map f ys)"
by (auto simp: prefix_def)

lemma filter_mono_prefix: "prefix xs ys \<Longrightarrow> prefix (filter P xs) (filter P ys)"
by (auto simp: prefix_def)

lemma sorted_antimono_prefix: "prefix xs ys \<Longrightarrow> sorted ys \<Longrightarrow> sorted xs"
by (metis sorted_append prefix_def)

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
proof (induct n arbitrary: xs ys)
  case 0
  then show ?case by (cases ys) simp_all
next
  case (Suc n)
  then show ?case by (metis prefix_order.less_trans strict_prefixI take_is_prefix)
qed

lemma prefix_takeWhile:
  assumes "prefix xs ys"
  shows   "prefix (takeWhile P xs) (takeWhile P ys)"
proof -
  from assms obtain zs where ys: "ys = xs @ zs"
    by (auto simp: prefix_def)
  have "prefix (takeWhile P xs) (takeWhile P (xs @ zs))"
    by (induction xs) auto
  thus ?thesis by (simp add: ys)
qed

lemma prefix_dropWhile:
  assumes "prefix xs ys"
  shows   "prefix (dropWhile P xs) (dropWhile P ys)"
proof -
  from assms obtain zs where ys: "ys = xs @ zs"
    by (auto simp: prefix_def)
  have "prefix (dropWhile P xs) (dropWhile P (xs @ zs))"
    by (induction xs) auto
  thus ?thesis by (simp add: ys)
qed

lemma prefix_remdups_adj:
  assumes "prefix xs ys"
  shows   "prefix (remdups_adj xs) (remdups_adj ys)"
  using assms
proof (induction "length xs" arbitrary: xs ys rule: less_induct)
  case (less xs)
  show ?case
  proof (cases xs)
    case [simp]: (Cons x xs')
    then obtain y ys' where [simp]: "ys = y # ys'"
      using \<open>prefix xs ys\<close> by (cases ys) auto
    from less show ?thesis
      by (auto simp: remdups_adj_Cons' less_Suc_eq_le length_dropWhile_le
               intro!: less prefix_dropWhile)
  qed auto
qed

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
  case Nil
  then show ?case
    by (auto simp: neq_Nil_conv elim!: not_prefix_cases intro!: base)
next
  case (Cons y ys)
  then have npfx: "\<not> prefix ps (y # ys)" by simp
  then obtain x xs where pv: "ps = x # xs"
    by (rule not_prefix_cases) auto
  show ?case by (metis Cons.hyps Cons_prefix_Cons npfx pv r1 r2)
qed


subsection \<open>Prefixes\<close>

primrec prefixes where
"prefixes [] = [[]]" |
"prefixes (x#xs) = [] # map ((#) x) (prefixes xs)"

lemma in_set_prefixes[simp]: "xs \<in> set (prefixes ys) \<longleftrightarrow> prefix xs ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by (cases ys) auto
next
  case (Cons a xs)
  then show ?case by (cases ys) auto
qed

lemma length_prefixes[simp]: "length (prefixes xs) = length xs+1"
  by (induction xs) auto
    
lemma distinct_prefixes [intro]: "distinct (prefixes xs)"
  by (induction xs) (auto simp: distinct_map)

lemma prefixes_snoc [simp]: "prefixes (xs@[x]) = prefixes xs @ [xs@[x]]"
  by (induction xs) auto

lemma prefixes_not_Nil [simp]: "prefixes xs \<noteq> []"
  by (cases xs) auto

lemma hd_prefixes [simp]: "hd (prefixes xs) = []"
  by (cases xs) simp_all

lemma last_prefixes [simp]: "last (prefixes xs) = xs"
  by (induction xs) (simp_all add: last_map)
    
lemma prefixes_append: 
  "prefixes (xs @ ys) = prefixes xs @ map (\<lambda>ys'. xs @ ys') (tl (prefixes ys))"
proof (induction xs)
  case Nil
  thus ?case by (cases ys) auto
qed simp_all

lemma prefixes_eq_snoc:
  "prefixes ys = xs @ [x] \<longleftrightarrow>
  (ys = [] \<and> xs = [] \<or> (\<exists>z zs. ys = zs@[z] \<and> xs = prefixes zs)) \<and> x = ys"
  by (cases ys rule: rev_cases) auto

lemma prefixes_tailrec [code]: 
  "prefixes xs = rev (snd (foldl (\<lambda>(acc1, acc2) x. (x#acc1, rev (x#acc1)#acc2)) ([],[[]]) xs))"
proof -
  have "foldl (\<lambda>(acc1, acc2) x. (x#acc1, rev (x#acc1)#acc2)) (ys, rev ys # zs) xs =
          (rev xs @ ys, rev (map (\<lambda>as. rev ys @ as) (prefixes xs)) @ zs)" for ys zs
  proof (induction xs arbitrary: ys zs)
    case (Cons x xs ys zs)
    from Cons.IH[of "x # ys" "rev ys # zs"]
      show ?case by (simp add: o_def)
  qed simp_all
  from this [of "[]" "[]"] show ?thesis by simp
qed
  
lemma set_prefixes_eq: "set (prefixes xs) = {ys. prefix ys xs}"
  by auto

lemma card_set_prefixes [simp]: "card (set (prefixes xs)) = Suc (length xs)"
  by (subst distinct_card) auto

lemma set_prefixes_append: 
  "set (prefixes (xs @ ys)) = set (prefixes xs) \<union> {xs @ ys' |ys'. ys' \<in> set (prefixes ys)}"
  by (subst prefixes_append, cases ys) auto


subsection \<open>Longest Common Prefix\<close>

definition Longest_common_prefix :: "'a list set \<Rightarrow> 'a list" where
"Longest_common_prefix L = (ARG_MAX length ps. \<forall>xs \<in> L. prefix ps xs)"

lemma Longest_common_prefix_ex: "L \<noteq> {} \<Longrightarrow>
  \<exists>ps. (\<forall>xs \<in> L. prefix ps xs) \<and> (\<forall>qs. (\<forall>xs \<in> L. prefix qs xs) \<longrightarrow> size qs \<le> size ps)"
  (is "_ \<Longrightarrow> \<exists>ps. ?P L ps")
proof(induction "LEAST n. \<exists>xs \<in>L. n = length xs" arbitrary: L)
  case 0
  have "[] \<in> L" using "0.hyps" LeastI[of "\<lambda>n. \<exists>xs\<in>L. n = length xs"] \<open>L \<noteq> {}\<close>
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
unfolding Longest_common_prefix_def arg_max_def is_arg_max_linorder
by(rule some1_equality[OF Longest_common_prefix_unique]) auto

lemma Longest_common_prefix_prefix:
  "xs \<in> L \<Longrightarrow> prefix (Longest_common_prefix L) xs"
unfolding Longest_common_prefix_def arg_max_def is_arg_max_linorder
by(rule someI2_ex[OF Longest_common_prefix_ex]) auto

lemma Longest_common_prefix_longest:
  "L \<noteq> {} \<Longrightarrow> \<forall>xs\<in>L. prefix ps xs \<Longrightarrow> length ps \<le> length(Longest_common_prefix L)"
unfolding Longest_common_prefix_def arg_max_def is_arg_max_linorder
by(rule someI2_ex[OF Longest_common_prefix_ex]) auto

lemma Longest_common_prefix_max_prefix:
  "L \<noteq> {} \<Longrightarrow> \<forall>xs\<in>L. prefix ps xs \<Longrightarrow> prefix ps (Longest_common_prefix L)"
by(metis Longest_common_prefix_prefix Longest_common_prefix_longest
     prefix_length_prefix ex_in_conv)

lemma Longest_common_prefix_Nil: "[] \<in> L \<Longrightarrow> Longest_common_prefix L = []"
using Longest_common_prefix_prefix prefix_Nil by blast

lemma Longest_common_prefix_image_Cons: "L \<noteq> {} \<Longrightarrow>
  Longest_common_prefix ((#) x ` L) = x # Longest_common_prefix L"
apply(rule Longest_common_prefix_eq)
  apply(simp)
 apply (simp add: Longest_common_prefix_prefix)
apply simp
by(metis Longest_common_prefix_longest[of L] Cons_prefix_Cons Nitpick.size_list_simp(2)
     Suc_le_mono hd_Cons_tl order.strict_implies_order zero_less_Suc)

lemma Longest_common_prefix_eq_Cons: assumes "L \<noteq> {}" "[] \<notin> L"  "\<forall>xs\<in>L. hd xs = x"
shows "Longest_common_prefix L = x # Longest_common_prefix {ys. x#ys \<in> L}"
proof -
  have "L = (#) x ` {ys. x#ys \<in> L}" using assms(2,3)
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

lemma parallel_cancel:  "a#xs \<parallel> a#ys \<Longrightarrow> xs \<parallel> ys"
  by (simp add: parallel_def)

theorem parallel_decomp:
  "xs \<parallel> ys \<Longrightarrow> \<exists>as b bs c cs. b \<noteq> c \<and> xs = as @ b # bs \<and> ys = as @ c # cs"
proof (induct rule: list_induct2', blast, force, force)
  case (4 x xs y ys)
  then show ?case
  proof (cases "x \<noteq> y", blast)
    assume "\<not> x \<noteq> y" hence "x = y" by blast
    then show ?thesis
      using "4.hyps"[OF parallel_cancel[OF "4.prems"[folded \<open>x = y\<close>]]]
      by (meson Cons_eq_appendI)
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
  where "strict_suffix xs ys \<longleftrightarrow> suffix xs ys \<and> xs \<noteq> ys"

interpretation suffix_order: order suffix strict_suffix
  by standard (auto simp: suffix_def strict_suffix_def)

interpretation suffix_bot: order_bot Nil suffix strict_suffix
  by standard (simp add: suffix_def)

lemma suffixI [intro?]: "ys = zs @ xs \<Longrightarrow> suffix xs ys"
  unfolding suffix_def by blast

lemma suffixE [elim?]:
  assumes "suffix xs ys"
  obtains zs where "ys = zs @ xs"
  using assms unfolding suffix_def by blast
    
lemma suffix_tl [simp]: "suffix (tl xs) xs"
  by (induct xs) (auto simp: suffix_def)

lemma strict_suffix_tl [simp]: "xs \<noteq> [] \<Longrightarrow> strict_suffix (tl xs) xs"
  by (induct xs) (auto simp: strict_suffix_def suffix_def)

lemma Nil_suffix [simp]: "suffix [] xs"
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
  by (auto simp: strict_suffix_def suffix_def)

lemma set_mono_suffix: "suffix xs ys \<Longrightarrow> set xs \<subseteq> set ys"
by (auto simp: suffix_def)

lemma sorted_antimono_suffix: "suffix xs ys \<Longrightarrow> sorted ys \<Longrightarrow> sorted xs"
by (metis sorted_append suffix_def)

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
  
lemma strict_suffix_to_prefix [code]: "strict_suffix xs ys \<longleftrightarrow> strict_prefix (rev xs) (rev ys)"
  by (auto simp: suffix_to_prefix strict_suffix_def strict_prefix_def)

lemma distinct_suffix: "distinct ys \<Longrightarrow> suffix xs ys \<Longrightarrow> distinct xs"
  by (clarsimp elim!: suffixE)

lemma map_mono_suffix: "suffix xs ys \<Longrightarrow> suffix (map f xs) (map f ys)"
by (auto elim!: suffixE intro: suffixI)

lemma filter_mono_suffix: "suffix xs ys \<Longrightarrow> suffix (filter P xs) (filter P ys)"
by (auto simp: suffix_def)

lemma suffix_drop: "suffix (drop n as) as"
  unfolding suffix_def by (metis append_take_drop_id)

lemma suffix_dropWhile: "suffix (dropWhile P xs) xs"
  unfolding suffix_def by (metis takeWhile_dropWhile_id)

lemma suffix_take: "suffix xs ys \<Longrightarrow> ys = take (length ys - length xs) ys @ xs"
  by (auto elim!: suffixE)

lemma strict_suffix_reflclp_conv: "strict_suffix\<^sup>=\<^sup>= = suffix"
  by (intro ext) (auto simp: suffix_def strict_suffix_def)

lemma suffix_lists: "suffix xs ys \<Longrightarrow> ys \<in> lists A \<Longrightarrow> xs \<in> lists A"
  unfolding suffix_def by auto

lemma suffix_snoc [simp]: "suffix xs (ys @ [y]) \<longleftrightarrow> xs = [] \<or> (\<exists>zs. xs = zs @ [y] \<and> suffix zs ys)"
  by (cases xs rule: rev_cases) (auto simp: suffix_def)

lemma snoc_suffix_snoc [simp]: "suffix (xs @ [x]) (ys @ [y]) = (x = y \<and> suffix xs ys)"
  by (auto simp add: suffix_def)

lemma same_suffix_suffix [simp]: "suffix (ys @ xs) (zs @ xs) = suffix ys zs"
  by (simp add: suffix_to_prefix)

lemma same_suffix_nil [simp]: "suffix (ys @ xs) xs = (ys = [])"
  by (simp add: suffix_to_prefix)

theorem suffix_Cons: "suffix xs (y # ys) \<longleftrightarrow> xs = y # ys \<or> suffix xs ys"
  unfolding suffix_def by (auto simp: Cons_eq_append_conv)

theorem suffix_append: 
  "suffix xs (ys @ zs) \<longleftrightarrow> suffix xs zs \<or> (\<exists>xs'. xs = xs' @ zs \<and> suffix xs' ys)"
  by (auto simp: suffix_def append_eq_append_conv2)

theorem suffix_length_le: "suffix xs ys \<Longrightarrow> length xs \<le> length ys"
  by (auto simp add: suffix_def)

lemma suffix_same_cases:
  "suffix (xs\<^sub>1::'a list) ys \<Longrightarrow> suffix xs\<^sub>2 ys \<Longrightarrow> suffix xs\<^sub>1 xs\<^sub>2 \<or> suffix xs\<^sub>2 xs\<^sub>1"
  unfolding suffix_def by (force simp: append_eq_append_conv2)

lemma suffix_length_suffix:
  "suffix ps xs \<Longrightarrow> suffix qs xs \<Longrightarrow> length ps \<le> length qs \<Longrightarrow> suffix ps qs"
  by (auto simp: suffix_to_prefix intro: prefix_length_prefix)

lemma suffix_length_less: "strict_suffix xs ys \<Longrightarrow> length xs < length ys"
  by (auto simp: strict_suffix_def suffix_def)

lemma suffix_ConsD': "suffix (x#xs) ys \<Longrightarrow> strict_suffix xs ys"
  by (auto simp: strict_suffix_def suffix_def)

lemma drop_strict_suffix: "strict_suffix xs ys \<Longrightarrow> strict_suffix (drop n xs) ys"
proof (induct n arbitrary: xs ys)
  case 0
  then show ?case by (cases ys) simp_all
next
  case (Suc n)
  then show ?case 
    by (cases xs) (auto intro: Suc dest: suffix_ConsD' suffix_order.less_imp_le)
qed

lemma suffix_map_rightE:
  assumes "suffix xs (map f ys)"
  shows   "\<exists>xs'. suffix xs' ys \<and> xs = map f xs'"
proof -
  from assms obtain xs' where xs': "map f ys = xs' @ xs"
    by (auto simp: suffix_def)
  define n where "n = length xs'"
  have "xs = drop n (map f ys)"
    by (simp add: xs' n_def)
  thus ?thesis
    by (intro exI[of _ "drop n ys"]) (auto simp: drop_map suffix_drop)
qed

lemma suffix_remdups_adj: "suffix xs ys \<Longrightarrow> suffix (remdups_adj xs) (remdups_adj ys)"
  using prefix_remdups_adj[of "rev xs" "rev ys"]
  by (simp add: suffix_to_prefix)

lemma not_suffix_cases:
  assumes pfx: "\<not> suffix ps ls"
  obtains
    (c1) "ps \<noteq> []" and "ls = []"
  | (c2) a as x xs where "ps = as@[a]" and "ls = xs@[x]" and "x = a" and "\<not> suffix as xs"
  | (c3) a as x xs where "ps = as@[a]" and "ls = xs@[x]" and "x \<noteq> a"
proof (cases ps rule: rev_cases)
  case Nil
  then show ?thesis using pfx by simp
next
  case (snoc as a)
  note c = \<open>ps = as@[a]\<close>
  show ?thesis
  proof (cases ls rule: rev_cases)
    case Nil then show ?thesis by (metis append_Nil2 pfx c1 same_suffix_nil)
  next
    case (snoc xs x)
    show ?thesis
    proof (cases "x = a")
      case True
      have "\<not> suffix as xs" using pfx c snoc True by simp
      with c snoc True show ?thesis by (rule c2)
    next
      case False
      with c snoc show ?thesis by (rule c3)
    qed
  qed
qed

lemma not_suffix_induct [consumes 1, case_names Nil Neq Eq]:
  assumes np: "\<not> suffix ps ls"
    and base: "\<And>x xs. P (xs@[x]) []"
    and r1: "\<And>x xs y ys. x \<noteq> y \<Longrightarrow> P (xs@[x]) (ys@[y])"
    and r2: "\<And>x xs y ys. \<lbrakk> x = y; \<not> suffix xs ys; P xs ys \<rbrakk> \<Longrightarrow> P (xs@[x]) (ys@[y])"
  shows "P ps ls" using np
proof (induct ls arbitrary: ps rule: rev_induct)
  case Nil
  then show ?case by (cases ps rule: rev_cases) (auto intro: base)
next
  case (snoc y ys ps)
  then have npfx: "\<not> suffix ps (ys @ [y])" by simp
  then obtain x xs where pv: "ps = xs @ [x]"
    by (rule not_suffix_cases) auto
  show ?case by (metis snoc.hyps snoc_suffix_snoc npfx pv r1 r2)
qed


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


subsection \<open>Suffixes\<close>

primrec suffixes where
  "suffixes [] = [[]]"
| "suffixes (x#xs) = suffixes xs @ [x # xs]"

lemma in_set_suffixes [simp]: "xs \<in> set (suffixes ys) \<longleftrightarrow> suffix xs ys"
  by (induction ys) (auto simp: suffix_def Cons_eq_append_conv)

lemma distinct_suffixes [intro]: "distinct (suffixes xs)"
  by (induction xs) (auto simp: suffix_def)

lemma length_suffixes [simp]: "length (suffixes xs) = Suc (length xs)"
  by (induction xs) auto

lemma suffixes_snoc [simp]: "suffixes (xs @ [x]) = [] # map (\<lambda>ys. ys @ [x]) (suffixes xs)"
  by (induction xs) auto

lemma suffixes_not_Nil [simp]: "suffixes xs \<noteq> []"
  by (cases xs) auto

lemma hd_suffixes [simp]: "hd (suffixes xs) = []"
  by (induction xs) simp_all

lemma last_suffixes [simp]: "last (suffixes xs) = xs"
  by (cases xs) simp_all

lemma suffixes_append: 
  "suffixes (xs @ ys) = suffixes ys @ map (\<lambda>xs'. xs' @ ys) (tl (suffixes xs))"
proof (induction ys rule: rev_induct)
  case Nil
  thus ?case by (cases xs rule: rev_cases) auto
next
  case (snoc y ys)
  show ?case
    by (simp only: append.assoc [symmetric] suffixes_snoc snoc.IH) simp
qed

lemma suffixes_eq_snoc:
  "suffixes ys = xs @ [x] \<longleftrightarrow>
     (ys = [] \<and> xs = [] \<or> (\<exists>z zs. ys = z#zs \<and> xs = suffixes zs)) \<and> x = ys"
  by (cases ys) auto

lemma suffixes_tailrec [code]: 
  "suffixes xs = rev (snd (foldl (\<lambda>(acc1, acc2) x. (x#acc1, (x#acc1)#acc2)) ([],[[]]) (rev xs)))"
proof -
  have "foldl (\<lambda>(acc1, acc2) x. (x#acc1, (x#acc1)#acc2)) (ys, ys # zs) (rev xs) =
          (xs @ ys, rev (map (\<lambda>as. as @ ys) (suffixes xs)) @ zs)" for ys zs
  proof (induction xs arbitrary: ys zs)
    case (Cons x xs ys zs)
    from Cons.IH[of ys zs]
      show ?case by (simp add: o_def case_prod_unfold)
  qed simp_all
  from this [of "[]" "[]"] show ?thesis by simp
qed
  
lemma set_suffixes_eq: "set (suffixes xs) = {ys. suffix ys xs}"
  by auto
    
lemma card_set_suffixes [simp]: "card (set (suffixes xs)) = Suc (length xs)"
  by (subst distinct_card) auto
  
lemma set_suffixes_append: 
  "set (suffixes (xs @ ys)) = set (suffixes ys) \<union> {xs' @ ys |xs'. xs' \<in> set (suffixes xs)}"
  by (subst suffixes_append, cases xs rule: rev_cases) auto


lemma suffixes_conv_prefixes: "suffixes xs = map rev (prefixes (rev xs))"
  by (induction xs) auto

lemma prefixes_conv_suffixes: "prefixes xs = map rev (suffixes (rev xs))"
  by (induction xs) auto
    
lemma prefixes_rev: "prefixes (rev xs) = map rev (suffixes xs)"
  by (induction xs) auto
    
lemma suffixes_rev: "suffixes (rev xs) = map rev (prefixes xs)"
  by (induction xs) auto


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
  using assms(2) and list_emb_append2 [OF assms(1)] by (auto simp: strict_suffix_def suffix_def)

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

lemma list_emb_Cons_iff1 [simp]:
  assumes "P x y"
  shows   "list_emb P (x#xs) (y#ys) \<longleftrightarrow> list_emb P xs ys"
  using assms by (subst list_emb.simps) (auto dest: list_emb_ConsD)

lemma list_emb_Cons_iff2 [simp]:
  assumes "\<not>P x y"
  shows   "list_emb P (x#xs) (y#ys) \<longleftrightarrow> list_emb P (x#xs) ys"
  using assms by (subst list_emb.simps) auto

lemma list_emb_code [code]:
  "list_emb P [] ys \<longleftrightarrow> True"
  "list_emb P (x#xs) [] \<longleftrightarrow> False"
  "list_emb P (x#xs) (y#ys) \<longleftrightarrow> (if P x y then list_emb P xs ys else list_emb P (x#xs) ys)"
  by simp_all
    

subsection \<open>Subsequences (special case of homeomorphic embedding)\<close>

abbreviation subseq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "subseq xs ys \<equiv> list_emb (=) xs ys"
  
definition strict_subseq where "strict_subseq xs ys \<longleftrightarrow> xs \<noteq> ys \<and> subseq xs ys"

lemma subseq_Cons2: "subseq xs ys \<Longrightarrow> subseq (x#xs) (x#ys)" by auto

lemma subseq_same_length:
  assumes "subseq xs ys" and "length xs = length ys" shows "xs = ys"
  using assms by (induct) (auto dest: list_emb_length)

lemma not_subseq_length [simp]: "length ys < length xs \<Longrightarrow> \<not> subseq xs ys"
  by (metis list_emb_length linorder_not_less)

lemma subseq_Cons': "subseq (x#xs) ys \<Longrightarrow> subseq xs ys"
  by (induct xs, simp, blast dest: list_emb_ConsD)

lemma subseq_Cons2':
  assumes "subseq (x#xs) (x#ys)" shows "subseq xs ys"
  using assms by (cases) (rule subseq_Cons')

lemma subseq_Cons2_neq:
  assumes "subseq (x#xs) (y#ys)"
  shows "x \<noteq> y \<Longrightarrow> subseq (x#xs) ys"
  using assms by (cases) auto

lemma subseq_Cons2_iff [simp]:
  "subseq (x#xs) (y#ys) = (if x = y then subseq xs ys else subseq (x#xs) ys)"
  by simp

lemma subseq_append': "subseq (zs @ xs) (zs @ ys) \<longleftrightarrow> subseq xs ys"
  by (induct zs) simp_all
    
interpretation subseq_order: order subseq strict_subseq
proof
  fix xs ys :: "'a list"
  {
    assume "subseq xs ys" and "subseq ys xs"
    thus "xs = ys"
    proof (induct)
      case list_emb_Nil
      from list_emb_Nil2 [OF this] show ?case by simp
    next
      case list_emb_Cons2
      thus ?case by simp
    next
      case list_emb_Cons
      hence False using subseq_Cons' by fastforce
      thus ?case ..
    qed
  }
  thus "strict_subseq xs ys \<longleftrightarrow> (subseq xs ys \<and> \<not>subseq ys xs)"
    by (auto simp: strict_subseq_def)
qed (auto simp: list_emb_refl intro: list_emb_trans)

lemma in_set_subseqs [simp]: "xs \<in> set (subseqs ys) \<longleftrightarrow> subseq xs ys"
proof
  assume "xs \<in> set (subseqs ys)"
  thus "subseq xs ys"
    by (induction ys arbitrary: xs) (auto simp: Let_def)
next
  have [simp]: "[] \<in> set (subseqs ys)" for ys :: "'a list" 
    by (induction ys) (auto simp: Let_def)
  assume "subseq xs ys"
  thus "xs \<in> set (subseqs ys)"
    by (induction xs ys rule: list_emb.induct) (auto simp: Let_def)
qed

lemma set_subseqs_eq: "set (subseqs ys) = {xs. subseq xs ys}"
  by auto

lemma subseq_append_le_same_iff: "subseq (xs @ ys) ys \<longleftrightarrow> xs = []"
  by (auto dest: list_emb_length)

lemma subseq_singleton_left: "subseq [x] ys \<longleftrightarrow> x \<in> set ys"
  by (fastforce dest: list_emb_ConsD split_list_last)

lemma list_emb_append_mono:
  "\<lbrakk> list_emb P xs xs'; list_emb P ys ys' \<rbrakk> \<Longrightarrow> list_emb P (xs@ys) (xs'@ys')"
  by (induct rule: list_emb.induct) auto

lemma prefix_imp_subseq [intro]: "prefix xs ys \<Longrightarrow> subseq xs ys"
  by (auto simp: prefix_def)

lemma suffix_imp_subseq [intro]: "suffix xs ys \<Longrightarrow> subseq xs ys"
  by (auto simp: suffix_def)


subsection \<open>Appending elements\<close>

lemma subseq_append [simp]:
  "subseq (xs @ zs) (ys @ zs) \<longleftrightarrow> subseq xs ys" (is "?l = ?r")
proof
  { fix xs' ys' xs ys zs :: "'a list" assume "subseq xs' ys'"
    then have "xs' = xs @ zs \<and> ys' = ys @ zs \<longrightarrow> subseq xs ys"
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
      ultimately show ?case using \<open>(=) x y\<close> by (auto simp: Cons_eq_append_conv)
    qed }
  moreover assume ?l
  ultimately show ?r by blast
next
  assume ?r then show ?l by (metis list_emb_append_mono subseq_order.order_refl)
qed

lemma subseq_append_iff: 
  "subseq xs (ys @ zs) \<longleftrightarrow> (\<exists>xs1 xs2. xs = xs1 @ xs2 \<and> subseq xs1 ys \<and> subseq xs2 zs)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs
  proof (induction xs "ys @ zs" arbitrary: ys zs rule: list_emb.induct)
    case (list_emb_Cons xs ws y ys zs)
    from list_emb_Cons(2)[of "tl ys" zs] and list_emb_Cons(2)[of "[]" "tl zs"] and list_emb_Cons(1,3)
      show ?case by (cases ys) auto
  next
    case (list_emb_Cons2 x y xs ws ys zs)
    from list_emb_Cons2(3)[of "tl ys" zs] and list_emb_Cons2(3)[of "[]" "tl zs"]
       and list_emb_Cons2(1,2,4)
    show ?case by (cases ys) (auto simp: Cons_eq_append_conv)
  qed auto
qed (auto intro: list_emb_append_mono)

lemma subseq_appendE [case_names append]: 
  assumes "subseq xs (ys @ zs)"
  obtains xs1 xs2 where "xs = xs1 @ xs2" "subseq xs1 ys" "subseq xs2 zs"
  using assms by (subst (asm) subseq_append_iff) auto

lemma subseq_drop_many: "subseq xs ys \<Longrightarrow> subseq xs (zs @ ys)"
  by (induct zs) auto

lemma subseq_rev_drop_many: "subseq xs ys \<Longrightarrow> subseq xs (ys @ zs)"
  by (metis append_Nil2 list_emb_Nil list_emb_append_mono)


subsection \<open>Relation to standard list operations\<close>

lemma subseq_map:
  assumes "subseq xs ys" shows "subseq (map f xs) (map f ys)"
  using assms by (induct) auto

lemma subseq_filter_left [simp]: "subseq (filter P xs) xs"
  by (induct xs) auto

lemma subseq_filter [simp]:
  assumes "subseq xs ys" shows "subseq (filter P xs) (filter P ys)"
  using assms by induct auto

lemma subseq_conv_nths: 
  "subseq xs ys \<longleftrightarrow> (\<exists>N. xs = nths ys N)" (is "?L = ?R")
proof
  assume ?L
  then show ?R
  proof (induct)
    case list_emb_Nil show ?case by (metis nths_empty)
  next
    case (list_emb_Cons xs ys x)
    then obtain N where "xs = nths ys N" by blast
    then have "xs = nths (x#ys) (Suc ` N)"
      by (clarsimp simp add: nths_Cons inj_image_mem_iff)
    then show ?case by blast
  next
    case (list_emb_Cons2 x y xs ys)
    then obtain N where "xs = nths ys N" by blast
    then have "x#xs = nths (x#ys) (insert 0 (Suc ` N))"
      by (clarsimp simp add: nths_Cons inj_image_mem_iff)
    moreover from list_emb_Cons2 have "x = y" by simp
    ultimately show ?case by blast
  qed
next
  assume ?R
  then obtain N where "xs = nths ys N" ..
  moreover have "subseq (nths ys N) ys"
  proof (induct ys arbitrary: N)
    case Nil show ?case by simp
  next
    case Cons then show ?case by (auto simp: nths_Cons)
  qed
  ultimately show ?L by simp
qed
  
  
subsection \<open>Contiguous sublists\<close>

subsubsection \<open>\<open>sublist\<close>\<close>

definition sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "sublist xs ys = (\<exists>ps ss. ys = ps @ xs @ ss)"
  
definition strict_sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "strict_sublist xs ys \<longleftrightarrow> sublist xs ys \<and> xs \<noteq> ys"

interpretation sublist_order: order sublist strict_sublist
proof
  fix xs ys zs :: "'a list"
  assume "sublist xs ys" "sublist ys zs"
  then obtain xs1 xs2 ys1 ys2 where "ys = xs1 @ xs @ xs2" "zs = ys1 @ ys @ ys2"
    by (auto simp: sublist_def)
  hence "zs = (ys1 @ xs1) @ xs @ (xs2 @ ys2)" by simp
  thus "sublist xs zs" unfolding sublist_def by blast
next
  fix xs ys :: "'a list"
  {
    assume "sublist xs ys" "sublist ys xs"
    then obtain as bs cs ds 
      where xs: "xs = as @ ys @ bs" and ys: "ys = cs @ xs @ ds" 
      by (auto simp: sublist_def)
    have "xs = as @ cs @ xs @ ds @ bs" by (subst xs, subst ys) auto
    also have "length \<dots> = length as + length cs + length xs + length bs + length ds" 
      by simp
    finally have "as = []" "bs = []" by simp_all
    with xs show "xs = ys" by simp
  }
  thus "strict_sublist xs ys \<longleftrightarrow> (sublist xs ys \<and> \<not>sublist ys xs)"
    by (auto simp: strict_sublist_def)
qed (auto simp: strict_sublist_def sublist_def intro: exI[of _ "[]"])
  
lemma sublist_Nil_left [simp, intro]: "sublist [] ys"
  by (auto simp: sublist_def)
    
lemma sublist_Cons_Nil [simp]: "\<not>sublist (x#xs) []"
  by (auto simp: sublist_def)
    
lemma sublist_Nil_right [simp]: "sublist xs [] \<longleftrightarrow> xs = []"
  by (cases xs) auto
    
lemma sublist_appendI [simp, intro]: "sublist xs (ps @ xs @ ss)"
  by (auto simp: sublist_def)
    
lemma sublist_append_leftI [simp, intro]: "sublist xs (ps @ xs)"
  by (auto simp: sublist_def intro: exI[of _ "[]"])
    
lemma sublist_append_rightI [simp, intro]: "sublist xs (xs @ ss)"
  by (auto simp: sublist_def intro: exI[of _ "[]"]) 

lemma sublist_altdef: "sublist xs ys \<longleftrightarrow> (\<exists>ys'. prefix ys' ys \<and> suffix xs ys')"
proof safe
  assume "sublist xs ys"
  then obtain ps ss where "ys = ps @ xs @ ss" by (auto simp: sublist_def)
  thus "\<exists>ys'. prefix ys' ys \<and> suffix xs ys'"
    by (intro exI[of _ "ps @ xs"] conjI suffix_appendI) auto
next
  fix ys'
  assume "prefix ys' ys" "suffix xs ys'"
  thus "sublist xs ys" by (auto simp: prefix_def suffix_def)
qed
  
lemma sublist_altdef': "sublist xs ys \<longleftrightarrow> (\<exists>ys'. suffix ys' ys \<and> prefix xs ys')"
proof safe
  assume "sublist xs ys"
  then obtain ps ss where "ys = ps @ xs @ ss" by (auto simp: sublist_def)
  thus "\<exists>ys'. suffix ys' ys \<and> prefix xs ys'"
    by (intro exI[of _ "xs @ ss"] conjI suffixI) auto
next
  fix ys'
  assume "suffix ys' ys" "prefix xs ys'"
  thus "sublist xs ys" by (auto simp: prefix_def suffix_def)
qed

lemma sublist_Cons_right: "sublist xs (y # ys) \<longleftrightarrow> prefix xs (y # ys) \<or> sublist xs ys"
  by (auto simp: sublist_def prefix_def Cons_eq_append_conv)
    
lemma sublist_code [code]:
  "sublist [] ys \<longleftrightarrow> True"
  "sublist (x # xs) [] \<longleftrightarrow> False"
  "sublist (x # xs) (y # ys) \<longleftrightarrow> prefix (x # xs) (y # ys) \<or> sublist (x # xs) ys"
  by (simp_all add: sublist_Cons_right)

lemma sublist_append:
  "sublist xs (ys @ zs) \<longleftrightarrow> 
     sublist xs ys \<or> sublist xs zs \<or> (\<exists>xs1 xs2. xs = xs1 @ xs2 \<and> suffix xs1 ys \<and> prefix xs2 zs)"
by (auto simp: sublist_altdef prefix_append suffix_append)

lemma map_mono_sublist:
  assumes "sublist xs ys"
  shows   "sublist (map f xs) (map f ys)"
proof -
  from assms obtain xs1 xs2 where ys: "ys = xs1 @ xs @ xs2"
    by (auto simp: sublist_def)
  have "map f ys = map f xs1 @ map f xs @ map f xs2"
    by (auto simp: ys)
  thus ?thesis
    by (auto simp: sublist_def)
qed

lemma sublist_length_le: "sublist xs ys \<Longrightarrow> length xs \<le> length ys"
  by (auto simp add: sublist_def)

lemma set_mono_sublist: "sublist xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (auto simp add: sublist_def)
    
lemma prefix_imp_sublist [simp, intro]: "prefix xs ys \<Longrightarrow> sublist xs ys"
  by (auto simp: sublist_def prefix_def intro: exI[of _ "[]"])
    
lemma suffix_imp_sublist [simp, intro]: "suffix xs ys \<Longrightarrow> sublist xs ys"
  by (auto simp: sublist_def suffix_def intro: exI[of _ "[]"])

lemma sublist_take [simp, intro]: "sublist (take n xs) xs"
  by (rule prefix_imp_sublist[OF take_is_prefix])

lemma sublist_takeWhile [simp, intro]: "sublist (takeWhile P xs) xs"
  by (rule prefix_imp_sublist[OF takeWhile_is_prefix])

lemma sublist_drop [simp, intro]: "sublist (drop n xs) xs"
  by (rule suffix_imp_sublist[OF suffix_drop])

lemma sublist_dropWhile [simp, intro]: "sublist (dropWhile P xs) xs"
  by (rule suffix_imp_sublist[OF suffix_dropWhile])
    
lemma sublist_tl [simp, intro]: "sublist (tl xs) xs"
  by (rule suffix_imp_sublist) (simp_all add: suffix_drop)
    
lemma sublist_butlast [simp, intro]: "sublist (butlast xs) xs"
  by (rule prefix_imp_sublist) (simp_all add: prefixeq_butlast)
    
lemma sublist_rev [simp]: "sublist (rev xs) (rev ys) = sublist xs ys"
proof
  assume "sublist (rev xs) (rev ys)"
  then obtain as bs where "rev ys = as @ rev xs @ bs"
    by (auto simp: sublist_def)
  also have "rev \<dots> = rev bs @ xs @ rev as" by simp
  finally show "sublist xs ys" by simp
next
  assume "sublist xs ys"
  then obtain as bs where "ys = as @ xs @ bs"
    by (auto simp: sublist_def)
  also have "rev \<dots> = rev bs @ rev xs @ rev as" by simp
  finally show "sublist (rev xs) (rev ys)" by simp
qed
    
lemma sublist_rev_left: "sublist (rev xs) ys = sublist xs (rev ys)"
  by (subst sublist_rev [symmetric]) (simp only: rev_rev_ident)
    
lemma sublist_rev_right: "sublist xs (rev ys) = sublist (rev xs) ys"
  by (subst sublist_rev [symmetric]) (simp only: rev_rev_ident)

lemma snoc_sublist_snoc: 
  "sublist (xs @ [x]) (ys @ [y]) \<longleftrightarrow> 
     (x = y \<and> suffix xs ys \<or> sublist (xs @ [x]) ys) "
  by (subst (1 2) sublist_rev [symmetric])
     (simp del: sublist_rev add: sublist_Cons_right suffix_to_prefix)

lemma sublist_snoc:
  "sublist xs (ys @ [y]) \<longleftrightarrow> suffix xs (ys @ [y]) \<or> sublist xs ys"
  by (subst (1 2) sublist_rev [symmetric])
     (simp del: sublist_rev add: sublist_Cons_right suffix_to_prefix)     
     
lemma sublist_imp_subseq [intro]: "sublist xs ys \<Longrightarrow> subseq xs ys"
  by (auto simp: sublist_def)

lemma sublist_map_rightE:
  assumes "sublist xs (map f ys)"
  shows   "\<exists>xs'. sublist xs' ys \<and> xs = map f xs'"
proof -
  note takedrop = sublist_take sublist_drop
  define n where "n = (length ys - length xs)"
  from assms obtain xs1 xs2 where xs12: "map f ys = xs1 @ xs @ xs2"
    by (auto simp: sublist_def)
  define n where "n = length xs1"
  have "xs = take (length xs) (drop n (map f ys))"
    by (simp add: xs12 n_def)
  thus ?thesis
    by (intro exI[of _ "take (length xs) (drop n ys)"])
       (auto simp: take_map drop_map intro!: takedrop[THEN sublist_order.order.trans])
qed

lemma sublist_remdups_adj:
  assumes "sublist xs ys"
  shows   "sublist (remdups_adj xs) (remdups_adj ys)"
proof -
  from assms obtain xs1 xs2 where ys: "ys = xs1 @ xs @ xs2"
    by (auto simp: sublist_def)
  have "suffix (remdups_adj (xs @ xs2)) (remdups_adj (xs1 @ xs @ xs2))"
    by (rule suffix_remdups_adj, rule  suffix_appendI) auto
  then obtain zs1 where zs1: "remdups_adj (xs1 @ xs @ xs2) = zs1 @ remdups_adj (xs @ xs2)"
    by (auto simp: suffix_def)
  have "prefix (remdups_adj xs) (remdups_adj (xs @ xs2))"
    by (intro prefix_remdups_adj) auto
  then obtain zs2 where zs2: "remdups_adj (xs @ xs2) = remdups_adj xs @ zs2"
    by (auto simp: prefix_def)
  show ?thesis
    by (simp add: ys zs1 zs2)
qed

subsubsection \<open>\<open>sublists\<close>\<close>

primrec sublists :: "'a list \<Rightarrow> 'a list list" where
  "sublists [] = [[]]"
| "sublists (x # xs) = sublists xs @ map ((#) x) (prefixes xs)"

lemma in_set_sublists [simp]: "xs \<in> set (sublists ys) \<longleftrightarrow> sublist xs ys" 
  by (induction ys arbitrary: xs) (auto simp: sublist_Cons_right prefix_Cons)

lemma set_sublists_eq: "set (sublists xs) = {ys. sublist ys xs}"
  by auto

lemma length_sublists [simp]: "length (sublists xs) = Suc (length xs * Suc (length xs) div 2)"
  by (induction xs) simp_all


subsection \<open>Parametricity\<close>

context includes lifting_syntax
begin    
  
private lemma prefix_primrec:
  "prefix = rec_list (\<lambda>xs. True) (\<lambda>x xs xsa ys.
              case ys of [] \<Rightarrow> False | y # ys \<Rightarrow> x = y \<and> xsa ys)"
proof (intro ext, goal_cases)
  case (1 xs ys)
  show ?case by (induction xs arbitrary: ys) (auto simp: prefix_Cons split: list.splits)
qed

private lemma sublist_primrec:
  "sublist = (\<lambda>xs ys. rec_list (\<lambda>xs. xs = []) (\<lambda>y ys ysa xs. prefix xs (y # ys) \<or> ysa xs) ys xs)"
proof (intro ext, goal_cases)
  case (1 xs ys)
  show ?case by (induction ys) (auto simp: sublist_Cons_right)
qed

private lemma list_emb_primrec:
  "list_emb = (\<lambda>uu uua uuaa. rec_list (\<lambda>P xs. List.null xs) (\<lambda>y ys ysa P xs. case xs of [] \<Rightarrow> True 
     | x # xs \<Rightarrow> if P x y then ysa P xs else ysa P (x # xs)) uuaa uu uua)"
proof (intro ext, goal_cases)
  case (1 P xs ys)
  show ?case
    by (induction ys arbitrary: xs)
       (auto simp: list_emb_code List.null_def split: list.splits)
qed

lemma prefix_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 A ===> (=)) prefix prefix"  
  unfolding prefix_primrec by transfer_prover
    
lemma suffix_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 A ===> (=)) suffix suffix"  
  unfolding suffix_to_prefix [abs_def] by transfer_prover

lemma sublist_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 A ===> (=)) sublist sublist"
  unfolding sublist_primrec by transfer_prover

lemma parallel_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 A ===> (=)) parallel parallel"
  unfolding parallel_def by transfer_prover
    


lemma list_emb_transfer [transfer_rule]:
  "((A ===> A ===> (=)) ===> list_all2 A ===> list_all2 A ===> (=)) list_emb list_emb"
  unfolding list_emb_primrec by transfer_prover

lemma strict_prefix_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 A ===> (=)) strict_prefix strict_prefix"  
  unfolding strict_prefix_def by transfer_prover
    
lemma strict_suffix_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 A ===> (=)) strict_suffix strict_suffix"  
  unfolding strict_suffix_def by transfer_prover
    
lemma strict_subseq_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 A ===> (=)) strict_subseq strict_subseq"  
  unfolding strict_subseq_def by transfer_prover
    
lemma strict_sublist_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 A ===> (=)) strict_sublist strict_sublist"  
  unfolding strict_sublist_def by transfer_prover

lemma prefixes_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 (list_all2 A)) prefixes prefixes"
  unfolding prefixes_def by transfer_prover
    
lemma suffixes_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 (list_all2 A)) suffixes suffixes"
  unfolding suffixes_def by transfer_prover
    
lemma sublists_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows   "(list_all2 A ===> list_all2 (list_all2 A)) sublists sublists"
  unfolding sublists_def by transfer_prover

end

end
