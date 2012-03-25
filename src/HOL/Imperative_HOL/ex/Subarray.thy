(*  Title:      HOL/Imperative_HOL/ex/Subarray.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

header {* Theorems about sub arrays *}

theory Subarray
imports "~~/src/HOL/Imperative_HOL/Array" Sublist
begin

definition subarray :: "nat \<Rightarrow> nat \<Rightarrow> ('a::heap) array \<Rightarrow> heap \<Rightarrow> 'a list" where
  "subarray n m a h \<equiv> sublist' n m (Array.get h a)"

lemma subarray_upd: "i \<ge> m \<Longrightarrow> subarray n m a (Array.update a i v h) = subarray n m a h"
apply (simp add: subarray_def Array.update_def)
apply (simp add: sublist'_update1)
done

lemma subarray_upd2: " i < n  \<Longrightarrow> subarray n m a (Array.update a i v h) = subarray n m a h"
apply (simp add: subarray_def Array.update_def)
apply (subst sublist'_update2)
apply fastforce
apply simp
done

lemma subarray_upd3: "\<lbrakk> n \<le> i; i < m\<rbrakk> \<Longrightarrow> subarray n m a (Array.update a i v h) = subarray n m a h[i - n := v]"
unfolding subarray_def Array.update_def
by (simp add: sublist'_update3)

lemma subarray_Nil: "n \<ge> m \<Longrightarrow> subarray n m a h = []"
by (simp add: subarray_def sublist'_Nil')

lemma subarray_single: "\<lbrakk> n < Array.length h a \<rbrakk> \<Longrightarrow> subarray n (Suc n) a h = [Array.get h a ! n]" 
by (simp add: subarray_def length_def sublist'_single)

lemma length_subarray: "m \<le> Array.length h a \<Longrightarrow> List.length (subarray n m a h) = m - n"
by (simp add: subarray_def length_def length_sublist')

lemma length_subarray_0: "m \<le> Array.length h a \<Longrightarrow> List.length (subarray 0 m a h) = m"
by (simp add: length_subarray)

lemma subarray_nth_array_Cons: "\<lbrakk> i < Array.length h a; i < j \<rbrakk> \<Longrightarrow> (Array.get h a ! i) # subarray (Suc i) j a h = subarray i j a h"
unfolding Array.length_def subarray_def
by (simp add: sublist'_front)

lemma subarray_nth_array_back: "\<lbrakk> i < j; j \<le> Array.length h a\<rbrakk> \<Longrightarrow> subarray i j a h = subarray i (j - 1) a h @ [Array.get h a ! (j - 1)]"
unfolding Array.length_def subarray_def
by (simp add: sublist'_back)

lemma subarray_append: "\<lbrakk> i < j; j < k \<rbrakk> \<Longrightarrow> subarray i j a h @ subarray j k a h = subarray i k a h"
unfolding subarray_def
by (simp add: sublist'_append)

lemma subarray_all: "subarray 0 (Array.length h a) a h = Array.get h a"
unfolding Array.length_def subarray_def
by (simp add: sublist'_all)

lemma nth_subarray: "\<lbrakk> k < j - i; j \<le> Array.length h a \<rbrakk> \<Longrightarrow> subarray i j a h ! k = Array.get h a ! (i + k)"
unfolding Array.length_def subarray_def
by (simp add: nth_sublist')

lemma subarray_eq_samelength_iff: "Array.length h a = Array.length h' a \<Longrightarrow> (subarray i j a h = subarray i j a h') = (\<forall>i'. i \<le> i' \<and> i' < j \<longrightarrow> Array.get h a ! i' = Array.get h' a ! i')"
unfolding Array.length_def subarray_def by (rule sublist'_eq_samelength_iff)

lemma all_in_set_subarray_conv: "(\<forall>j. j \<in> set (subarray l r a h) \<longrightarrow> P j) = (\<forall>k. l \<le> k \<and> k < r \<and> k < Array.length h a \<longrightarrow> P (Array.get h a ! k))"
unfolding subarray_def Array.length_def by (rule all_in_set_sublist'_conv)

lemma ball_in_set_subarray_conv: "(\<forall>j \<in> set (subarray l r a h). P j) = (\<forall>k. l \<le> k \<and> k < r \<and> k < Array.length h a \<longrightarrow> P (Array.get h a ! k))"
unfolding subarray_def Array.length_def by (rule ball_in_set_sublist'_conv)

end