(* Author: Andreas Lochbihler, ETH Zürich
   Author: Florian Haftmann, TU Muenchen  *)

header \<open>Less common functions on lists\<close>

theory More_List
imports Main
begin

definition strip_while :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "strip_while P = rev \<circ> dropWhile P \<circ> rev"

lemma strip_while_rev [simp]:
  "strip_while P (rev xs) = rev (dropWhile P xs)"
  by (simp add: strip_while_def)
  
lemma strip_while_Nil [simp]:
  "strip_while P [] = []"
  by (simp add: strip_while_def)

lemma strip_while_append [simp]:
  "\<not> P x \<Longrightarrow> strip_while P (xs @ [x]) = xs @ [x]"
  by (simp add: strip_while_def)

lemma strip_while_append_rec [simp]:
  "P x \<Longrightarrow> strip_while P (xs @ [x]) = strip_while P xs"
  by (simp add: strip_while_def)

lemma strip_while_Cons [simp]:
  "\<not> P x \<Longrightarrow> strip_while P (x # xs) = x # strip_while P xs"
  by (induct xs rule: rev_induct) (simp_all add: strip_while_def)

lemma strip_while_eq_Nil [simp]:
  "strip_while P xs = [] \<longleftrightarrow> (\<forall>x\<in>set xs. P x)"
  by (simp add: strip_while_def)

lemma strip_while_eq_Cons_rec:
  "strip_while P (x # xs) = x # strip_while P xs \<longleftrightarrow> \<not> (P x \<and> (\<forall>x\<in>set xs. P x))"
  by (induct xs rule: rev_induct) (simp_all add: strip_while_def)

lemma strip_while_not_last [simp]:
  "\<not> P (last xs) \<Longrightarrow> strip_while P xs = xs"
  by (cases xs rule: rev_cases) simp_all

lemma split_strip_while_append:
  fixes xs :: "'a list"
  obtains ys zs :: "'a list"
  where "strip_while P xs = ys" and "\<forall>x\<in>set zs. P x" and "xs = ys @ zs"
proof (rule that)
  show "strip_while P xs = strip_while P xs" ..
  show "\<forall>x\<in>set (rev (takeWhile P (rev xs))). P x" by (simp add: takeWhile_eq_all_conv [symmetric])
  have "rev xs = rev (strip_while P xs @ rev (takeWhile P (rev xs)))"
    by (simp add: strip_while_def)
  then show "xs = strip_while P xs @ rev (takeWhile P (rev xs))"
    by (simp only: rev_is_rev_conv)
qed

lemma strip_while_snoc [simp]:
  "strip_while P (xs @ [x]) = (if P x then strip_while P xs else xs @ [x])"
  by (simp add: strip_while_def)

lemma strip_while_map:
  "strip_while P (map f xs) = map f (strip_while (P \<circ> f) xs)"
  by (simp add: strip_while_def rev_map dropWhile_map)


definition no_leading :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "no_leading P xs \<longleftrightarrow> (xs \<noteq> [] \<longrightarrow> \<not> P (hd xs))"

lemma no_leading_Nil [simp, intro!]:
  "no_leading P []"
  by (simp add: no_leading_def)

lemma no_leading_Cons [simp, intro!]:
  "no_leading P (x # xs) \<longleftrightarrow> \<not> P x"
  by (simp add: no_leading_def)

lemma no_leading_append [simp]:
  "no_leading P (xs @ ys) \<longleftrightarrow> no_leading P xs \<and> (xs = [] \<longrightarrow> no_leading P ys)"
  by (induct xs) simp_all

lemma no_leading_dropWhile [simp]:
  "no_leading P (dropWhile P xs)"
  by (induct xs) simp_all

lemma dropWhile_eq_obtain_leading:
  assumes "dropWhile P xs = ys"
  obtains zs where "xs = zs @ ys" and "\<And>z. z \<in> set zs \<Longrightarrow> P z" and "no_leading P ys"
proof -
  from assms have "\<exists>zs. xs = zs @ ys \<and> (\<forall>z \<in> set zs. P z) \<and> no_leading P ys"
  proof (induct xs arbitrary: ys)
    case Nil then show ?case by simp
  next
    case (Cons x xs ys)
    show ?case proof (cases "P x")
      case True with Cons.hyps [of ys] Cons.prems
      have "\<exists>zs. xs = zs @ ys \<and> (\<forall>a\<in>set zs. P a) \<and> no_leading P ys"
        by simp
      then obtain zs where "xs = zs @ ys" and "\<And>z. z \<in> set zs \<Longrightarrow> P z"
        and *: "no_leading P ys"
        by blast
      with True have "x # xs = (x # zs) @ ys" and "\<And>z. z \<in> set (x # zs) \<Longrightarrow> P z"
        by auto
      with * show ?thesis
        by blast    next
      case False
      with Cons show ?thesis by (cases ys) simp_all
    qed
  qed
  with that show thesis
    by blast
qed

lemma dropWhile_idem_iff:
  "dropWhile P xs = xs \<longleftrightarrow> no_leading P xs"
  by (cases xs) (auto elim: dropWhile_eq_obtain_leading)


abbreviation no_trailing :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "no_trailing P xs \<equiv> no_leading P (rev xs)"

lemma no_trailing_unfold:
  "no_trailing P xs \<longleftrightarrow> (xs \<noteq> [] \<longrightarrow> \<not> P (last xs))"
  by (induct xs) simp_all

lemma no_trailing_Nil [simp, intro!]:
  "no_trailing P []"
  by simp

lemma no_trailing_Cons [simp]:
  "no_trailing P (x # xs) \<longleftrightarrow> no_trailing P xs \<and> (xs = [] \<longrightarrow> \<not> P x)"
  by simp

lemma no_trailing_append_Cons [simp]:
  "no_trailing P (xs @ y # ys) \<longleftrightarrow> no_trailing P (y # ys)"
  by simp

lemma no_trailing_strip_while [simp]:
  "no_trailing P (strip_while P xs)"
  by (induct xs rule: rev_induct) simp_all

lemma strip_while_eq_obtain_trailing:
  assumes "strip_while P xs = ys"
  obtains zs where "xs = ys @ zs" and "\<And>z. z \<in> set zs \<Longrightarrow> P z" and "no_trailing P ys"
proof -
  from assms have "rev (rev (dropWhile P (rev xs))) = rev ys"
    by (simp add: strip_while_def)
  then have "dropWhile P (rev xs) = rev ys"
    by simp
  then obtain zs where A: "rev xs = zs @ rev ys" and B: "\<And>z. z \<in> set zs \<Longrightarrow> P z"
    and C: "no_trailing P ys"
    using dropWhile_eq_obtain_leading by blast
  from A have "rev (rev xs) = rev (zs @ rev ys)"
    by simp
  then have "xs = ys @ rev zs"
    by simp
  moreover from B have "\<And>z. z \<in> set (rev zs) \<Longrightarrow> P z"
    by simp
  ultimately show thesis using that C by blast
qed

lemma strip_while_idem_iff:
  "strip_while P xs = xs \<longleftrightarrow> no_trailing P xs"
proof -
  def ys \<equiv> "rev xs"
  moreover have "strip_while P (rev ys) = rev ys \<longleftrightarrow> no_trailing P (rev ys)"
    by (simp add: dropWhile_idem_iff)
  ultimately show ?thesis by simp
qed

lemma no_trailing_map:
  "no_trailing P (map f xs) = no_trailing (P \<circ> f) xs"
  by (simp add: last_map no_trailing_unfold)

lemma no_trailing_upt [simp]:
  "no_trailing P [n..<m] \<longleftrightarrow> (n < m \<longrightarrow> \<not> P (m - 1))"
  by (auto simp add: no_trailing_unfold)


definition nth_default :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a"
where
  "nth_default x xs n = (if n < length xs then xs ! n else x)"

lemma nth_default_Nil [simp]:
  "nth_default y [] n = y"
  by (simp add: nth_default_def)

lemma nth_default_Cons_0 [simp]:
  "nth_default y (x # xs) 0 = x"
  by (simp add: nth_default_def)

lemma nth_default_Cons_Suc [simp]:
  "nth_default y (x # xs) (Suc n) = nth_default y xs n"
  by (simp add: nth_default_def)

lemma nth_default_map_eq:
  "f y = x \<Longrightarrow> nth_default x (map f xs) n = f (nth_default y xs n)"
  by (simp add: nth_default_def)

lemma nth_default_strip_while_eq [simp]:
  "nth_default x (strip_while (HOL.eq x) xs) n = nth_default x xs n"
proof -
  from split_strip_while_append obtain ys zs
    where "strip_while (HOL.eq x) xs = ys" and "\<forall>z\<in>set zs. x = z" and "xs = ys @ zs" by blast
  then show ?thesis by (simp add: nth_default_def not_less nth_append)
qed

lemma nth_default_Cons:
  "nth_default y (x # xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> nth_default y xs n')"
  by (simp split: nat.split)

lemma nth_default_nth:
  "n < length xs \<Longrightarrow> nth_default y xs n = xs ! n"
  by (simp add: nth_default_def)

lemma nth_default_beyond:
  "length xs \<le> n \<Longrightarrow> nth_default y xs n = y"
  by (simp add: nth_default_def)

lemma range_nth_default [simp]:
  "range (nth_default dflt xs) = insert dflt (set xs)"
  by (auto simp add: nth_default_def[abs_def] in_set_conv_nth)

lemma nth_strip_while:
  assumes "n < length (strip_while P xs)"
  shows "strip_while P xs ! n = xs ! n"
proof -
  have "length (dropWhile P (rev xs)) + length (takeWhile P (rev xs)) = length xs"
    by (subst add.commute)
      (simp add: arg_cong [where f=length, OF takeWhile_dropWhile_id, unfolded length_append])
  then show ?thesis using assms
    by (simp add: strip_while_def rev_nth dropWhile_nth)
qed

lemma length_strip_while_le:
  "length (strip_while P xs) \<le> length xs"
  unfolding strip_while_def o_def length_rev
  by (subst (2) length_rev[symmetric])
    (simp add: strip_while_def length_dropWhile_le del: length_rev)

lemma finite_nth_default_neq_default [simp]:
  "finite {k. nth_default dflt xs k \<noteq> dflt}"
  by (simp add: nth_default_def)

lemma sorted_list_of_set_nth_default:
  "sorted_list_of_set {k. nth_default dflt xs k \<noteq> dflt} = map fst (filter (\<lambda>(_, x). x \<noteq> dflt) (zip [0..<length xs] xs))"
  by (rule sorted_distinct_set_unique) (auto simp add: nth_default_def in_set_conv_nth sorted_filter distinct_map_filter intro: rev_image_eqI)

lemma nth_default_snoc_default [simp]:
  "nth_default dflt (xs @ [dflt]) = nth_default dflt xs"
  by (auto simp add: nth_default_def fun_eq_iff nth_append)

lemma nth_default_strip_while_dflt [simp]:
 "nth_default dflt (strip_while (op = dflt) xs) = nth_default dflt xs"
  by (induct xs rule: rev_induct) auto

lemma nth_default_eq_dflt_iff:
  "nth_default dflt xs k = dflt \<longleftrightarrow> (k < length xs \<longrightarrow> xs ! k = dflt)"
  by (simp add: nth_default_def)

end

