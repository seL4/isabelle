(*  Author:     Lawrence C Paulson and Thomas M Rasmussen and Norbert Voelker
*)

section \<open>Permuted Lists\<close>

theory List_Permutation
imports Permutations
begin

text \<open>
  Note that multisets already provide the notion of permutated list and hence
  this theory mostly echoes material already logically present in theory
  \<^text>\<open>Permutations\<close>; it should be seldom needed.
\<close>

subsection \<open>An existing notion\<close>

abbreviation (input) perm :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>  (infixr \<open><~~>\<close> 50)
  where \<open>xs <~~> ys \<equiv> mset xs = mset ys\<close>


subsection \<open>Nontrivial conclusions\<close>

proposition perm_swap:
  \<open>xs[i := xs ! j, j := xs ! i] <~~> xs\<close>
  if \<open>i < length xs\<close> \<open>j < length xs\<close>
  using that by (simp add: mset_swap)

proposition mset_le_perm_append: "mset xs \<subseteq># mset ys \<longleftrightarrow> (\<exists>zs. xs @ zs <~~> ys)"
  by (auto simp add: mset_subset_eq_exists_conv ex_mset dest: sym)

proposition perm_set_eq: "xs <~~> ys \<Longrightarrow> set xs = set ys"
  by (rule mset_eq_setD) simp

proposition perm_distinct_iff: "xs <~~> ys \<Longrightarrow> distinct xs \<longleftrightarrow> distinct ys"
  by (rule mset_eq_imp_distinct_iff) simp

theorem eq_set_perm_remdups: "set xs = set ys \<Longrightarrow> remdups xs <~~> remdups ys"
  by (simp add: set_eq_iff_mset_remdups_eq)

proposition perm_remdups_iff_eq_set: "remdups x <~~> remdups y \<longleftrightarrow> set x = set y"
  by (simp add: set_eq_iff_mset_remdups_eq)

theorem permutation_Ex_bij:
  assumes "xs <~~> ys"
  shows "\<exists>f. bij_betw f {..<length xs} {..<length ys} \<and> (\<forall>i<length xs. xs ! i = ys ! (f i))"
proof -
  from assms have \<open>mset xs = mset ys\<close> \<open>length xs = length ys\<close>
    by (auto simp add: dest: mset_eq_length)
  from \<open>mset xs = mset ys\<close> obtain p where \<open>p permutes {..<length ys}\<close> \<open>permute_list p ys = xs\<close>
    by (rule mset_eq_permutation)
  then have \<open>bij_betw p {..<length xs} {..<length ys}\<close>
    by (simp add: \<open>length xs = length ys\<close> permutes_imp_bij)
  moreover have \<open>\<forall>i<length xs. xs ! i = ys ! (p i)\<close>
    using \<open>permute_list p ys = xs\<close> \<open>length xs = length ys\<close> \<open>p permutes {..<length ys}\<close> permute_list_nth
    by auto
  ultimately show ?thesis
    by blast
qed

proposition perm_finite: "finite {B. B <~~> A}"
  using mset_eq_finite by auto


subsection \<open>Trivial conclusions:\<close>

proposition perm_empty_imp: "[] <~~> ys \<Longrightarrow> ys = []"
  by simp


text \<open>\medskip This more general theorem is easier to understand!\<close>

proposition perm_length: "xs <~~> ys \<Longrightarrow> length xs = length ys"
  by (rule mset_eq_length) simp

proposition perm_sym: "xs <~~> ys \<Longrightarrow> ys <~~> xs"
  by simp


text \<open>We can insert the head anywhere in the list.\<close>

proposition perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  by simp

proposition perm_append_swap: "xs @ ys <~~> ys @ xs"
  by simp

proposition perm_append_single: "a # xs <~~> xs @ [a]"
  by simp

proposition perm_rev: "rev xs <~~> xs"
  by simp

proposition perm_append1: "xs <~~> ys \<Longrightarrow> l @ xs <~~> l @ ys"
  by simp

proposition perm_append2: "xs <~~> ys \<Longrightarrow> xs @ l <~~> ys @ l"
  by simp

proposition perm_empty [iff]: "[] <~~> xs \<longleftrightarrow> xs = []"
  by simp

proposition perm_empty2 [iff]: "xs <~~> [] \<longleftrightarrow> xs = []"
  by simp

proposition perm_sing_imp: "ys <~~> xs \<Longrightarrow> xs = [y] \<Longrightarrow> ys = [y]"
  by simp

proposition perm_sing_eq [iff]: "ys <~~> [y] \<longleftrightarrow> ys = [y]"
  by simp

proposition perm_sing_eq2 [iff]: "[y] <~~> ys \<longleftrightarrow> ys = [y]"
  by simp

proposition perm_remove: "x \<in> set ys \<Longrightarrow> ys <~~> x # remove1 x ys"
  by simp


text \<open>\medskip Congruence rule\<close>

proposition perm_remove_perm: "xs <~~> ys \<Longrightarrow> remove1 z xs <~~> remove1 z ys"
  by simp

proposition remove_hd [simp]: "remove1 z (z # xs) = xs"
  by simp

proposition cons_perm_imp_perm: "z # xs <~~> z # ys \<Longrightarrow> xs <~~> ys"
  by simp

proposition cons_perm_eq [simp]: "z#xs <~~> z#ys \<longleftrightarrow> xs <~~> ys"
  by simp

proposition append_perm_imp_perm: "zs @ xs <~~> zs @ ys \<Longrightarrow> xs <~~> ys"
  by simp

proposition perm_append1_eq [iff]: "zs @ xs <~~> zs @ ys \<longleftrightarrow> xs <~~> ys"
  by simp

proposition perm_append2_eq [iff]: "xs @ zs <~~> ys @ zs \<longleftrightarrow> xs <~~> ys"
  by simp

end
