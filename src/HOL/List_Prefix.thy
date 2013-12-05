(*  Title:      HOL/List_Prefix.thy
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
    Author:     Christian Sternagel, JAIST
*)

header {* Parallel lists, list suffixes, and homeomorphic embedding *}

theory List_Prefix
imports List
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

end
