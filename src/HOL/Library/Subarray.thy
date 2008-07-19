theory Subarray
imports Array Sublist
begin

definition subarray :: "nat \<Rightarrow> nat \<Rightarrow> ('a::heap) array \<Rightarrow> heap \<Rightarrow> 'a list"
where
  "subarray n m a h \<equiv> sublist' n m (get_array a h)"

lemma subarray_upd: "i \<ge> m \<Longrightarrow> subarray n m a (Heap.upd a i v h) = subarray n m a h"
apply (simp add: subarray_def Heap.upd_def)
apply (simp add: sublist'_update1)
done

lemma subarray_upd2: " i < n  \<Longrightarrow> subarray n m a (Heap.upd a i v h) = subarray n m a h"
apply (simp add: subarray_def Heap.upd_def)
apply (subst sublist'_update2)
apply fastsimp
apply simp
done

lemma subarray_upd3: "\<lbrakk> n \<le> i; i < m\<rbrakk> \<Longrightarrow> subarray n m a (Heap.upd a i v h) = subarray n m a h[i - n := v]"
unfolding subarray_def Heap.upd_def
by (simp add: sublist'_update3)

lemma subarray_Nil: "n \<ge> m \<Longrightarrow> subarray n m a h = []"
by (simp add: subarray_def sublist'_Nil')

lemma subarray_single: "\<lbrakk> n < Heap.length a h \<rbrakk> \<Longrightarrow> subarray n (Suc n) a h = [get_array a h ! n]" 
by (simp add: subarray_def Heap.length_def sublist'_single)

lemma length_subarray: "m \<le> Heap.length a h \<Longrightarrow> List.length (subarray n m a h) = m - n"
by (simp add: subarray_def Heap.length_def length_sublist')

lemma length_subarray_0: "m \<le> Heap.length a h \<Longrightarrow> List.length (subarray 0 m a h) = m"
by (simp add: length_subarray)

lemma subarray_nth_array_Cons: "\<lbrakk> i < Heap.length a h; i < j \<rbrakk> \<Longrightarrow> (get_array a h ! i) # subarray (Suc i) j a h = subarray i j a h"
unfolding Heap.length_def subarray_def
by (simp add: sublist'_front)

lemma subarray_nth_array_back: "\<lbrakk> i < j; j \<le> Heap.length a h\<rbrakk> \<Longrightarrow> subarray i j a h = subarray i (j - 1) a h @ [get_array a h ! (j - 1)]"
unfolding Heap.length_def subarray_def
by (simp add: sublist'_back)

lemma subarray_append: "\<lbrakk> i < j; j < k \<rbrakk> \<Longrightarrow> subarray i j a h @ subarray j k a h = subarray i k a h"
unfolding subarray_def
by (simp add: sublist'_append)

lemma subarray_all: "subarray 0 (Heap.length a h) a h = get_array a h"
unfolding Heap.length_def subarray_def
by (simp add: sublist'_all)

lemma nth_subarray: "\<lbrakk> k < j - i; j \<le> Heap.length a h \<rbrakk> \<Longrightarrow> subarray i j a h ! k = get_array a h ! (i + k)"
unfolding Heap.length_def subarray_def
by (simp add: nth_sublist')

lemma subarray_eq_samelength_iff: "Heap.length a h = Heap.length a h' \<Longrightarrow> (subarray i j a h = subarray i j a h') = (\<forall>i'. i \<le> i' \<and> i' < j \<longrightarrow> get_array a h ! i' = get_array a h' ! i')"
unfolding Heap.length_def subarray_def by (rule sublist'_eq_samelength_iff)

lemma all_in_set_subarray_conv: "(\<forall>j. j \<in> set (subarray l r a h) \<longrightarrow> P j) = (\<forall>k. l \<le> k \<and> k < r \<and> k < Heap.length a h \<longrightarrow> P (get_array a h ! k))"
unfolding subarray_def Heap.length_def by (rule all_in_set_sublist'_conv)

lemma ball_in_set_subarray_conv: "(\<forall>j \<in> set (subarray l r a h). P j) = (\<forall>k. l \<le> k \<and> k < r \<and> k < Heap.length a h \<longrightarrow> P (get_array a h ! k))"
unfolding subarray_def Heap.length_def by (rule ball_in_set_sublist'_conv)

end