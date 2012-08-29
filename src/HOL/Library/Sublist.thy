(*  Title:      HOL/Library/Sublist.thy
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

header {* List prefixes and postfixes *}

theory Sublist
imports List Main
begin

subsection {* Prefix order on lists *}

instantiation list :: (type) "{order, bot}"
begin

definition
  prefixeq_def: "xs \<le> ys \<longleftrightarrow> (\<exists>zs. ys = xs @ zs)"

definition
  prefix_def: "xs < ys \<longleftrightarrow> xs \<le> ys \<and> xs \<noteq> (ys::'a list)"

definition
  "bot = []"

instance proof
qed (auto simp add: prefixeq_def prefix_def bot_list_def)

end

lemma prefixeqI [intro?]: "ys = xs @ zs ==> xs \<le> ys"
  unfolding prefixeq_def by blast

lemma prefixeqE [elim?]:
  assumes "xs \<le> ys"
  obtains zs where "ys = xs @ zs"
  using assms unfolding prefixeq_def by blast

lemma prefixI' [intro?]: "ys = xs @ z # zs ==> xs < ys"
  unfolding prefix_def prefixeq_def by blast

lemma prefixE' [elim?]:
  assumes "xs < ys"
  obtains z zs where "ys = xs @ z # zs"
proof -
  from `xs < ys` obtain us where "ys = xs @ us" and "xs \<noteq> ys"
    unfolding prefix_def prefixeq_def by blast
  with that show ?thesis by (auto simp add: neq_Nil_conv)
qed

lemma prefixI [intro?]: "xs \<le> ys ==> xs \<noteq> ys ==> xs < (ys::'a list)"
  unfolding prefix_def by blast

lemma prefixE [elim?]:
  fixes xs ys :: "'a list"
  assumes "xs < ys"
  obtains "xs \<le> ys" and "xs \<noteq> ys"
  using assms unfolding prefix_def by blast


subsection {* Basic properties of prefixes *}

theorem Nil_prefixeq [iff]: "[] \<le> xs"
  by (simp add: prefixeq_def)

theorem prefixeq_Nil [simp]: "(xs \<le> []) = (xs = [])"
  by (induct xs) (simp_all add: prefixeq_def)

lemma prefixeq_snoc [simp]: "(xs \<le> ys @ [y]) = (xs = ys @ [y] \<or> xs \<le> ys)"
proof
  assume "xs \<le> ys @ [y]"
  then obtain zs where zs: "ys @ [y] = xs @ zs" ..
  show "xs = ys @ [y] \<or> xs \<le> ys"
    by (metis append_Nil2 butlast_append butlast_snoc prefixeqI zs)
next
  assume "xs = ys @ [y] \<or> xs \<le> ys"
  then show "xs \<le> ys @ [y]"
    by (metis order_eq_iff order_trans prefixeqI)
qed

lemma Cons_prefixeq_Cons [simp]: "(x # xs \<le> y # ys) = (x = y \<and> xs \<le> ys)"
  by (auto simp add: prefixeq_def)

lemma less_eq_list_code [code]:
  "([]\<Colon>'a\<Colon>{equal, ord} list) \<le> xs \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{equal, ord}) # xs \<le> [] \<longleftrightarrow> False"
  "(x\<Colon>'a\<Colon>{equal, ord}) # xs \<le> y # ys \<longleftrightarrow> x = y \<and> xs \<le> ys"
  by simp_all

lemma same_prefixeq_prefixeq [simp]: "(xs @ ys \<le> xs @ zs) = (ys \<le> zs)"
  by (induct xs) simp_all

lemma same_prefixeq_nil [iff]: "(xs @ ys \<le> xs) = (ys = [])"
  by (metis append_Nil2 append_self_conv order_eq_iff prefixeqI)

lemma prefixeq_prefixeq [simp]: "xs \<le> ys ==> xs \<le> ys @ zs"
  by (metis order_le_less_trans prefixeqI prefixE prefixI)

lemma append_prefixeqD: "xs @ ys \<le> zs \<Longrightarrow> xs \<le> zs"
  by (auto simp add: prefixeq_def)

theorem prefixeq_Cons: "(xs \<le> y # ys) = (xs = [] \<or> (\<exists>zs. xs = y # zs \<and> zs \<le> ys))"
  by (cases xs) (auto simp add: prefixeq_def)

theorem prefixeq_append:
  "(xs \<le> ys @ zs) = (xs \<le> ys \<or> (\<exists>us. xs = ys @ us \<and> us \<le> zs))"
  apply (induct zs rule: rev_induct)
   apply force
  apply (simp del: append_assoc add: append_assoc [symmetric])
  apply (metis append_eq_appendI)
  done

lemma append_one_prefixeq:
  "xs \<le> ys ==> length xs < length ys ==> xs @ [ys ! length xs] \<le> ys"
  unfolding prefixeq_def
  by (metis Cons_eq_appendI append_eq_appendI append_eq_conv_conj
    eq_Nil_appendI nth_drop')

theorem prefixeq_length_le: "xs \<le> ys ==> length xs \<le> length ys"
  by (auto simp add: prefixeq_def)

lemma prefixeq_same_cases:
  "(xs\<^isub>1::'a list) \<le> ys \<Longrightarrow> xs\<^isub>2 \<le> ys \<Longrightarrow> xs\<^isub>1 \<le> xs\<^isub>2 \<or> xs\<^isub>2 \<le> xs\<^isub>1"
  unfolding prefixeq_def by (metis append_eq_append_conv2)

lemma set_mono_prefixeq: "xs \<le> ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (auto simp add: prefixeq_def)

lemma take_is_prefixeq: "take n xs \<le> xs"
  unfolding prefixeq_def by (metis append_take_drop_id)

lemma map_prefixeqI: "xs \<le> ys \<Longrightarrow> map f xs \<le> map f ys"
  by (auto simp: prefixeq_def)

lemma prefixeq_length_less: "xs < ys \<Longrightarrow> length xs < length ys"
  by (auto simp: prefix_def prefixeq_def)

lemma prefix_simps [simp, code]:
  "xs < [] \<longleftrightarrow> False"
  "[] < x # xs \<longleftrightarrow> True"
  "x # xs < y # ys \<longleftrightarrow> x = y \<and> xs < ys"
  by (simp_all add: prefix_def cong: conj_cong)

lemma take_prefix: "xs < ys \<Longrightarrow> take n xs < ys"
  apply (induct n arbitrary: xs ys)
   apply (case_tac ys, simp_all)[1]
  apply (metis order_less_trans prefixI take_is_prefixeq)
  done

lemma not_prefixeq_cases:
  assumes pfx: "\<not> ps \<le> ls"
  obtains
    (c1) "ps \<noteq> []" and "ls = []"
  | (c2) a as x xs where "ps = a#as" and "ls = x#xs" and "x = a" and "\<not> as \<le> xs"
  | (c3) a as x xs where "ps = a#as" and "ls = x#xs" and "x \<noteq> a"
proof (cases ps)
  case Nil then show ?thesis using pfx by simp
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
      have "\<not> as \<le> xs" using pfx c Cons True by simp
      with c Cons True show ?thesis by (rule c2)
    next
      case False
      with c Cons show ?thesis by (rule c3)
    qed
  qed
qed

lemma not_prefixeq_induct [consumes 1, case_names Nil Neq Eq]:
  assumes np: "\<not> ps \<le> ls"
    and base: "\<And>x xs. P (x#xs) []"
    and r1: "\<And>x xs y ys. x \<noteq> y \<Longrightarrow> P (x#xs) (y#ys)"
    and r2: "\<And>x xs y ys. \<lbrakk> x = y; \<not> xs \<le> ys; P xs ys \<rbrakk> \<Longrightarrow> P (x#xs) (y#ys)"
  shows "P ps ls" using np
proof (induct ls arbitrary: ps)
  case Nil then show ?case
    by (auto simp: neq_Nil_conv elim!: not_prefixeq_cases intro!: base)
next
  case (Cons y ys)
  then have npfx: "\<not> ps \<le> (y # ys)" by simp
  then obtain x xs where pv: "ps = x # xs"
    by (rule not_prefixeq_cases) auto
  show ?case by (metis Cons.hyps Cons_prefixeq_Cons npfx pv r1 r2)
qed


subsection {* Parallel lists *}

definition
  parallel :: "'a list => 'a list => bool"  (infixl "\<parallel>" 50) where
  "(xs \<parallel> ys) = (\<not> xs \<le> ys \<and> \<not> ys \<le> xs)"

lemma parallelI [intro]: "\<not> xs \<le> ys ==> \<not> ys \<le> xs ==> xs \<parallel> ys"
  unfolding parallel_def by blast

lemma parallelE [elim]:
  assumes "xs \<parallel> ys"
  obtains "\<not> xs \<le> ys \<and> \<not> ys \<le> xs"
  using assms unfolding parallel_def by blast

theorem prefixeq_cases:
  obtains "xs \<le> ys" | "ys < xs" | "xs \<parallel> ys"
  unfolding parallel_def prefix_def by blast

theorem parallel_decomp:
  "xs \<parallel> ys ==> \<exists>as b bs c cs. b \<noteq> c \<and> xs = as @ b # bs \<and> ys = as @ c # cs"
proof (induct xs rule: rev_induct)
  case Nil
  then have False by auto
  then show ?case ..
next
  case (snoc x xs)
  show ?case
  proof (rule prefixeq_cases)
    assume le: "xs \<le> ys"
    then obtain ys' where ys: "ys = xs @ ys'" ..
    show ?thesis
    proof (cases ys')
      assume "ys' = []"
      then show ?thesis by (metis append_Nil2 parallelE prefixeqI snoc.prems ys)
    next
      fix c cs assume ys': "ys' = c # cs"
      then show ?thesis
        by (metis Cons_eq_appendI eq_Nil_appendI parallelE prefixeqI
          same_prefixeq_prefixeq snoc.prems ys)
    qed
  next
    assume "ys < xs" then have "ys \<le> xs @ [x]" by (simp add: prefix_def)
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


subsection {* Postfix order on lists *}

definition
  postfix :: "'a list => 'a list => bool"  ("(_/ >>= _)" [51, 50] 50) where
  "(xs >>= ys) = (\<exists>zs. xs = zs @ ys)"

lemma postfixI [intro?]: "xs = zs @ ys ==> xs >>= ys"
  unfolding postfix_def by blast

lemma postfixE [elim?]:
  assumes "xs >>= ys"
  obtains zs where "xs = zs @ ys"
  using assms unfolding postfix_def by blast

lemma postfix_refl [iff]: "xs >>= xs"
  by (auto simp add: postfix_def)
lemma postfix_trans: "\<lbrakk>xs >>= ys; ys >>= zs\<rbrakk> \<Longrightarrow> xs >>= zs"
  by (auto simp add: postfix_def)
lemma postfix_antisym: "\<lbrakk>xs >>= ys; ys >>= xs\<rbrakk> \<Longrightarrow> xs = ys"
  by (auto simp add: postfix_def)

lemma Nil_postfix [iff]: "xs >>= []"
  by (simp add: postfix_def)
lemma postfix_Nil [simp]: "([] >>= xs) = (xs = [])"
  by (auto simp add: postfix_def)

lemma postfix_ConsI: "xs >>= ys \<Longrightarrow> x#xs >>= ys"
  by (auto simp add: postfix_def)
lemma postfix_ConsD: "xs >>= y#ys \<Longrightarrow> xs >>= ys"
  by (auto simp add: postfix_def)

lemma postfix_appendI: "xs >>= ys \<Longrightarrow> zs @ xs >>= ys"
  by (auto simp add: postfix_def)
lemma postfix_appendD: "xs >>= zs @ ys \<Longrightarrow> xs >>= ys"
  by (auto simp add: postfix_def)

lemma postfix_is_subset: "xs >>= ys ==> set ys \<subseteq> set xs"
proof -
  assume "xs >>= ys"
  then obtain zs where "xs = zs @ ys" ..
  then show ?thesis by (induct zs) auto
qed

lemma postfix_ConsD2: "x#xs >>= y#ys ==> xs >>= ys"
proof -
  assume "x#xs >>= y#ys"
  then obtain zs where "x#xs = zs @ y#ys" ..
  then show ?thesis
    by (induct zs) (auto intro!: postfix_appendI postfix_ConsI)
qed

lemma postfix_to_prefixeq [code]: "xs >>= ys \<longleftrightarrow> rev ys \<le> rev xs"
proof
  assume "xs >>= ys"
  then obtain zs where "xs = zs @ ys" ..
  then have "rev xs = rev ys @ rev zs" by simp
  then show "rev ys <= rev xs" ..
next
  assume "rev ys <= rev xs"
  then obtain zs where "rev xs = rev ys @ zs" ..
  then have "rev (rev xs) = rev zs @ rev (rev ys)" by simp
  then have "xs = rev zs @ ys" by simp
  then show "xs >>= ys" ..
qed

lemma distinct_postfix: "distinct xs \<Longrightarrow> xs >>= ys \<Longrightarrow> distinct ys"
  by (clarsimp elim!: postfixE)

lemma postfix_map: "xs >>= ys \<Longrightarrow> map f xs >>= map f ys"
  by (auto elim!: postfixE intro: postfixI)

lemma postfix_drop: "as >>= drop n as"
  unfolding postfix_def
  apply (rule exI [where x = "take n as"])
  apply simp
  done

lemma postfix_take: "xs >>= ys \<Longrightarrow> xs = take (length xs - length ys) xs @ ys"
  by (clarsimp elim!: postfixE)

lemma parallelD1: "x \<parallel> y \<Longrightarrow> \<not> x \<le> y"
  by blast

lemma parallelD2: "x \<parallel> y \<Longrightarrow> \<not> y \<le> x"
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

end
