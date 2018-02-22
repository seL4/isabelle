(* Author: Tobias Nipkow *)

theory Radix_Sort
imports
  "HOL-Library.Multiset" 
  "HOL-Library.List_lexord" 
  "HOL-Library.Sublist" 
begin

fun radix_sort :: "nat \<Rightarrow> 'a::linorder list list \<Rightarrow> 'a list list" where
"radix_sort 0 xss = xss" |
"radix_sort (Suc n) xss = radix_sort n (sort_key (\<lambda>xs. xs ! n) xss)"

abbreviation "sorted_from i xss \<equiv> sorted (map (drop i) xss)"

definition "cols xss k = (\<forall>xs \<in> set xss. length xs = k)"

lemma mset_radix_sort: "mset (radix_sort k xss) = mset xss"
by(induction k arbitrary: xss) (auto)

lemma cols_sort_key: "cols xss n \<Longrightarrow> cols (sort_key f xss) n"
by(simp add: cols_def)

lemma sorted_from_Suc2: "\<lbrakk> cols xss n; i < n;
  sorted (map (\<lambda>xs. xs!i) xss);  \<forall>xs \<in> set xss. sorted_from (i+1) [ys \<leftarrow> xss. ys!i = xs!i] \<rbrakk>
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
    also have "\<dots> \<le> xs2!i # drop (i+1) xs2" using "3.prems"(3,4) by(auto)
    also have "\<dots> = drop i xs2"
      using \<open>i < n\<close> by (simp add: Cons_nth_drop_Suc lxs2)
    finally show ?thesis .
  qed
  have "sorted_from i (xs2 # xss)"
  proof(rule "3.IH"[OF _ "3.prems"(2)])
    show "cols (xs2 # xss) n" using "3.prems"(1) by(simp add: cols_def)
    show "sorted (map (\<lambda>xs. xs ! i) (xs2 # xss))" using "3.prems"(3) by simp
    show "\<forall>xs\<in>set (xs2 # xss). sorted_from (i+1) [ys\<leftarrow>xs2 # xss . ys ! i = xs ! i]"
      using "3.prems"(4)
        sorted_antimono_suffix[OF map_mono_suffix[OF filter_mono_suffix[OF suffix_ConsI[OF suffix_order.order.refl]]]]
      by fastforce
  qed
  with * show ?case by (auto)
qed

lemma sorted_from_radix_sort_step:
  "\<lbrakk> cols xss n; i < n; sorted_from (Suc i) xss \<rbrakk> \<Longrightarrow> sorted_from i (sort_key (\<lambda>xs. xs ! i) xss)"
apply (rule sorted_from_Suc2)
apply (auto simp add: sort_key_stable sorted_filter cols_def)
done

lemma sorted_from_radix_sort:
  "cols xss n \<Longrightarrow> i \<le> n \<Longrightarrow> sorted_from i xss \<Longrightarrow> sorted_from 0 (radix_sort i xss)"
apply(induction i arbitrary: xss)
 apply(simp add: sort_key_const)
apply(simp add: sorted_from_radix_sort_step cols_sort_key)
done

lemma sorted_radix_sort: "cols xss n \<Longrightarrow> sorted (radix_sort n xss)"
apply(frule sorted_from_radix_sort[OF _ le_refl])
 apply(auto simp add: cols_def sorted_equals_nth_mono)
done

end
