(* Author: Andreas Lochbihler, ETH Zürich
   Author: Florian Haftmann, TU Muenchen  *)

section \<open>Less common functions on lists\<close>

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

lemma strip_while_dropWhile_commute:
  "strip_while P (dropWhile Q xs) = dropWhile Q (strip_while P xs)"
proof (induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "\<forall>y\<in>set xs. P y")
    case True
    with dropWhile_append2 [of "rev xs"] show ?thesis
      by (auto simp add: strip_while_def dest: set_dropWhileD)
  next
    case False
    then obtain y where "y \<in> set xs" and "\<not> P y"
      by blast
    with Cons dropWhile_append3 [of P y "rev xs"] show ?thesis
      by (simp add: strip_while_def)
  qed
qed

lemma dropWhile_strip_while_commute:
  "dropWhile P (strip_while Q xs) = strip_while Q (dropWhile P xs)"
  by (simp add: strip_while_dropWhile_commute)


definition no_leading :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "no_leading P xs \<longleftrightarrow> (xs \<noteq> [] \<longrightarrow> \<not> P (hd xs))"

lemma no_leading_Nil [iff]:
  "no_leading P []"
  by (simp add: no_leading_def)

lemma no_leading_Cons [iff]:
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

lemma no_trailing_Nil [iff]:
  "no_trailing P []"
  by simp

lemma no_trailing_Cons [simp]:
  "no_trailing P (x # xs) \<longleftrightarrow> no_trailing P xs \<and> (xs = [] \<longrightarrow> \<not> P x)"
  by simp

lemma no_trailing_append:
  "no_trailing P (xs @ ys) \<longleftrightarrow> no_trailing P ys \<and> (ys = [] \<longrightarrow> no_trailing P xs)"
  by (induct xs) simp_all

lemma no_trailing_append_Cons [simp]:
  "no_trailing P (xs @ y # ys) \<longleftrightarrow> no_trailing P (y # ys)"
  by simp

lemma no_trailing_strip_while [simp]:
  "no_trailing P (strip_while P xs)"
  by (induct xs rule: rev_induct) simp_all

lemma strip_while_idem [simp]:
  "no_trailing P xs \<Longrightarrow> strip_while P xs = xs"
  by (cases xs rule: rev_cases) simp_all

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
  define ys where "ys = rev xs"
  moreover have "strip_while P (rev ys) = rev ys \<longleftrightarrow> no_trailing P (rev ys)"
    by (simp add: dropWhile_idem_iff)
  ultimately show ?thesis by simp
qed

lemma no_trailing_map:
  "no_trailing P (map f xs) \<longleftrightarrow> no_trailing (P \<circ> f) xs"
  by (simp add: last_map no_trailing_unfold)

lemma no_trailing_drop [simp]:
  "no_trailing P (drop n xs)" if "no_trailing P xs"
proof -
  from that have "no_trailing P (take n xs @ drop n xs)"
    by simp
  then show ?thesis
    by (simp only: no_trailing_append)
qed

lemma no_trailing_upt [simp]:
  "no_trailing P [n..<m] \<longleftrightarrow> (n < m \<longrightarrow> \<not> P (m - 1))"
  by (auto simp add: no_trailing_unfold)


definition nth_default :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a"
where
  "nth_default dflt xs n = (if n < length xs then xs ! n else dflt)"

lemma nth_default_nth:
  "n < length xs \<Longrightarrow> nth_default dflt xs n = xs ! n"
  by (simp add: nth_default_def)

lemma nth_default_beyond:
  "length xs \<le> n \<Longrightarrow> nth_default dflt xs n = dflt"
  by (simp add: nth_default_def)

lemma nth_default_Nil [simp]:
  "nth_default dflt [] n = dflt"
  by (simp add: nth_default_def)

lemma nth_default_Cons:
  "nth_default dflt (x # xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> nth_default dflt xs n')"
  by (simp add: nth_default_def split: nat.split)

lemma nth_default_Cons_0 [simp]:
  "nth_default dflt (x # xs) 0 = x"
  by (simp add: nth_default_Cons)

lemma nth_default_Cons_Suc [simp]:
  "nth_default dflt (x # xs) (Suc n) = nth_default dflt xs n"
  by (simp add: nth_default_Cons)

lemma nth_default_replicate_dflt [simp]:
  "nth_default dflt (replicate n dflt) m = dflt"
  by (simp add: nth_default_def)

lemma nth_default_append:
  "nth_default dflt (xs @ ys) n =
    (if n < length xs then nth xs n else nth_default dflt ys (n - length xs))"
  by (auto simp add: nth_default_def nth_append)

lemma nth_default_append_trailing [simp]:
  "nth_default dflt (xs @ replicate n dflt) = nth_default dflt xs"
  by (simp add: fun_eq_iff nth_default_append) (simp add: nth_default_def)

lemma nth_default_snoc_default [simp]:
  "nth_default dflt (xs @ [dflt]) = nth_default dflt xs"
  by (auto simp add: nth_default_def fun_eq_iff nth_append)

lemma nth_default_eq_dflt_iff:
  "nth_default dflt xs k = dflt \<longleftrightarrow> (k < length xs \<longrightarrow> xs ! k = dflt)"
  by (simp add: nth_default_def)

lemma nth_default_take_eq:
  "nth_default dflt (take m xs) n =
    (if n < m then nth_default dflt xs n else dflt)"
  by (simp add: nth_default_def)

lemma in_enumerate_iff_nth_default_eq:
  "x \<noteq> dflt \<Longrightarrow> (n, x) \<in> set (enumerate 0 xs) \<longleftrightarrow> nth_default dflt xs n = x"
  by (auto simp add: nth_default_def in_set_conv_nth enumerate_eq_zip)

lemma last_conv_nth_default:
  assumes "xs \<noteq> []"
  shows "last xs = nth_default dflt xs (length xs - 1)"
  using assms by (simp add: nth_default_def last_conv_nth)

lemma nth_default_map_eq:
  "f dflt' = dflt \<Longrightarrow> nth_default dflt (map f xs) n = f (nth_default dflt' xs n)"
  by (simp add: nth_default_def)

lemma finite_nth_default_neq_default [simp]:
  "finite {k. nth_default dflt xs k \<noteq> dflt}"
  by (simp add: nth_default_def)

lemma sorted_list_of_set_nth_default:
  "sorted_list_of_set {k. nth_default dflt xs k \<noteq> dflt} = map fst (filter (\<lambda>(_, x). x \<noteq> dflt) (enumerate 0 xs))"
  by (rule sorted_distinct_set_unique) (auto simp add: nth_default_def in_set_conv_nth
    sorted_filter distinct_map_filter enumerate_eq_zip intro: rev_image_eqI)

lemma map_nth_default:
  "map (nth_default x xs) [0..<length xs] = xs"
proof -
  have *: "map (nth_default x xs) [0..<length xs] = map (List.nth xs) [0..<length xs]"
    by (rule map_cong) (simp_all add: nth_default_nth)
  show ?thesis by (simp add: * map_nth)
qed

lemma range_nth_default [simp]:
  "range (nth_default dflt xs) = insert dflt (set xs)"
  by (auto simp add: nth_default_def [abs_def] in_set_conv_nth)

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

lemma nth_default_strip_while_dflt [simp]:
  "nth_default dflt (strip_while ((=) dflt) xs) = nth_default dflt xs"
  by (induct xs rule: rev_induct) auto

lemma nth_default_eq_iff:
  "nth_default dflt xs = nth_default dflt ys
     \<longleftrightarrow> strip_while (HOL.eq dflt) xs = strip_while (HOL.eq dflt) ys" (is "?P \<longleftrightarrow> ?Q")
proof
  let ?strip_while = \<open>strip_while (HOL.eq dflt)\<close>
  let ?xs = "?strip_while xs"
  let ?ys = "?strip_while ys"
  assume ?P
  then have eq: "nth_default dflt ?xs = nth_default dflt ?ys"
    by simp
  have len: "length ?xs = length ?ys"
  proof (rule ccontr)
    assume neq: "\<not> ?thesis"
    { fix xs ys :: "'a list"
      let ?xs = "?strip_while xs"
      let ?ys = "?strip_while ys"
      assume eq: "nth_default dflt ?xs = nth_default dflt ?ys"
      assume len: "length ?xs < length ?ys"
      then have "length ?ys > 0" by arith
      then have "?ys \<noteq> []" by simp
      with last_conv_nth_default [of ?ys dflt]
      have "last ?ys = nth_default dflt ?ys (length ?ys - 1)"
        by auto
      moreover from \<open>?ys \<noteq> []\<close> no_trailing_strip_while [of "HOL.eq dflt" ys]
        have "last ?ys \<noteq> dflt" by (simp add: no_trailing_unfold)
      ultimately have "nth_default dflt ?xs (length ?ys - 1) \<noteq> dflt"
        using eq by simp
      moreover from len have "length ?ys - 1 \<ge> length ?xs" by simp
      ultimately have False by (simp only: nth_default_beyond) simp
    }
    from this [of xs ys] this [of ys xs] neq eq show False
      by (auto simp only: linorder_class.neq_iff)
  qed
  then show ?Q
  proof (rule nth_equalityI [rule_format])
    fix n
    assume n: "n < length ?xs"
    with len have "n < length ?ys"
      by simp
    with n have xs: "nth_default dflt ?xs n = ?xs ! n"
      and ys: "nth_default dflt ?ys n = ?ys ! n"
      by (simp_all only: nth_default_nth)
    with eq show "?xs ! n = ?ys ! n"
      by simp
  qed
next
  assume ?Q
  then have "nth_default dflt (strip_while (HOL.eq dflt) xs) = nth_default dflt (strip_while (HOL.eq dflt) ys)"
    by simp
  then show ?P
    by simp
qed

lemma nth_default_map2:
  \<open>nth_default d (map2 f xs ys) n = f (nth_default d1 xs n) (nth_default d2 ys n)\<close>
    if \<open>length xs = length ys\<close> and \<open>f d1 d2 = d\<close> for bs cs
using that proof (induction xs ys arbitrary: n rule: list_induct2)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs y ys)
  then show ?case
    by (cases n) simp_all
qed

end

