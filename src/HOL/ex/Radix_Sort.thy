(* Author: Tobias Nipkow *)

theory Radix_Sort
imports
  "HOL-Library.List_Lexorder" 
  "HOL-Library.Sublist" 
  "HOL-Library.Multiset" 
begin

text \<open>The \<open>Radix_Sort\<close> locale provides a sorting function \<open>radix_sort\<close> that sorts
lists of lists. It is parameterized by a sorting function \<open>sort1 f\<close> that also sorts
lists of lists, but only w.r.t. the column selected by \<open>f\<close>.
Working with lists, \<open>f\<close> is instantiated with \<^term>\<open>\<lambda>xs. xs ! n\<close> to select the \<open>n\<close>-th element.
A more efficient implementation would sort lists of arrays because arrays support
constant time access to every element.\<close>

locale Radix_Sort =
fixes sort1 :: "('a list \<Rightarrow> 'a::linorder) \<Rightarrow> 'a list list \<Rightarrow> 'a list list"
assumes sorted: "sorted (map f (sort1 f xss))"
assumes mset: "mset (sort1 f xss) = mset xss"
assumes stable: "stable_sort_key sort1"
begin

lemma set_sort1[simp]: "set(sort1 f xss) = set xss"
by (metis mset set_mset_mset)

abbreviation "sort_col i xss \<equiv> sort1 (\<lambda>xs. xs ! i) xss"
abbreviation "sorted_col i xss \<equiv> sorted (map (\<lambda>xs. xs ! i) xss)"

fun radix_sort :: "nat \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
"radix_sort 0 xss = xss" |
"radix_sort (Suc i) xss = radix_sort i (sort_col i xss)"

lemma mset_radix_sort: "mset (radix_sort i xss) = mset xss"
by(induction i arbitrary: xss) (auto simp: mset)

abbreviation "sorted_from i xss \<equiv> sorted (map (drop i) xss)"

definition "cols xss n = (\<forall>xs \<in> set xss. length xs = n)"

lemma cols_sort1: "cols xss n \<Longrightarrow> cols (sort1 f xss) n"
by(simp add: cols_def)

lemma sorted_from_Suc2:
  "\<lbrakk> cols xss n; i < n;
    sorted_col i xss;
    \<And>x. sorted_from (i+1) [ys \<leftarrow> xss. ys!i = x] \<rbrakk>
  \<Longrightarrow> sorted_from i xss"
proof(induction xss rule: induct_list012)
  case 1 show ?case by simp
next
  case 2 show ?case by simp
next
  case (3 xs1 xs2 xss)
  have lxs1: "length xs1 = n" and lxs2: "length xs2 = n"
    using "3.prems"(1) by(auto simp: cols_def)
  have *: "drop i xs1 \<le> drop i xs2"
  proof -
    have "drop i xs1 = xs1!i # drop (i+1) xs1"
      using \<open>i < n\<close> by (simp add: Cons_nth_drop_Suc lxs1)
    also have "\<dots> \<le> xs2!i # drop (i+1) xs2"
      using "3.prems"(3) "3.prems"(4)[of "xs2!i"] by(auto)
    also have "\<dots> = drop i xs2"
      using \<open>i < n\<close> by (simp add: Cons_nth_drop_Suc lxs2)
    finally show ?thesis .
  qed
  have "sorted_from i (xs2 # xss)"
  proof(rule "3.IH"[OF _ "3.prems"(2)])
    show "cols (xs2 # xss) n" using "3.prems"(1) by(simp add: cols_def)
    show "sorted_col i (xs2 # xss)" using "3.prems"(3) by simp
    show "\<And>x. sorted_from (i+1) [ys\<leftarrow>xs2 # xss . ys ! i = x]"
      using "3.prems"(4)
        sorted_antimono_suffix[OF map_mono_suffix[OF filter_mono_suffix[OF suffix_ConsI[OF suffix_order.refl]]]]
      by fastforce
  qed
  with * show ?case by (auto)
qed

lemma sorted_from_radix_sort_step:
assumes "cols xss n" and "i < n" and "sorted_from (i+1) xss"
shows "sorted_from i (sort_col i xss)"
proof (rule sorted_from_Suc2[OF cols_sort1[OF assms(1)] assms(2)])
  show "sorted_col i (sort_col i xss)" by(simp add: sorted)
  fix x show "sorted_from (i+1) [ys \<leftarrow> sort_col i xss . ys ! i = x]"
  proof -
    from assms(3)
    have "sorted_from (i+1) (filter (\<lambda>ys. ys!i = x) xss)"
      by(rule sorted_filter)
    thus "sorted (map (drop (i+1)) (filter (\<lambda>ys. ys!i = x) (sort_col i xss)))"
      by (metis stable stable_sort_key_def)
  qed
qed

lemma sorted_from_radix_sort:
  "\<lbrakk> cols xss n;  i \<le> n;  sorted_from i xss \<rbrakk> \<Longrightarrow> sorted_from 0 (radix_sort i xss)"
proof(induction i arbitrary: xss)
  case 0 thus ?case by simp
next
  case (Suc i)
  thus ?case by(simp add: sorted_from_radix_sort_step cols_sort1)
qed

corollary sorted_radix_sort: "cols xss n \<Longrightarrow> sorted (radix_sort n xss)"
apply(frule sorted_from_radix_sort[OF _ le_refl])
 apply(auto simp add: cols_def sorted_iff_nth_mono)
done

end

end
