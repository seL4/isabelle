(* Author: Andreas Lochbihler, ETH Zürich
   Author: Florian Haftmann, TU Muenchen  *)

header \<open>Less common functions on lists\<close>

theory More_List
imports Main
begin

text \<open>FIXME adapted from @{file "~~/src/HOL/Library/Polynomial.thy"}; to be merged back\<close>

definition strip_while :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "strip_while P = rev \<circ> dropWhile P \<circ> rev"

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

lemma dropWhile_idI:
  "(xs \<noteq> [] \<Longrightarrow> \<not> P (hd xs)) \<Longrightarrow> dropWhile P xs = xs"
  by (metis dropWhile.simps(1) dropWhile.simps(2) list.collapse)

lemma strip_while_idI:
  "(xs \<noteq> [] \<Longrightarrow> \<not> P (last xs)) \<Longrightarrow> strip_while P xs = xs"
  using dropWhile_idI [of "rev xs"] by (simp add: strip_while_def hd_rev)


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
