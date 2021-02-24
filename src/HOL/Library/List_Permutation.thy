(*  Title:      HOL/Library/List_Permutation.thy
    Author:     Lawrence C Paulson and Thomas M Rasmussen and Norbert Voelker
*)

section \<open>Permuted Lists\<close>

theory List_Permutation
imports Multiset
begin

subsection \<open>An inductive definition\<dots>\<close>

inductive perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infixr \<open><~~>\<close> 50)
where
  Nil [intro!]: "[] <~~> []"
| swap [intro!]: "y # x # l <~~> x # y # l"
| Cons [intro!]: "xs <~~> ys \<Longrightarrow> z # xs <~~> z # ys"
| trans [intro]: "xs <~~> ys \<Longrightarrow> ys <~~> zs \<Longrightarrow> xs <~~> zs"

proposition perm_refl [iff]: "l <~~> l"
  by (induct l) auto

text \<open>\<dots>that is equivalent to an already existing notion:\<close>

lemma perm_iff_eq_mset:
  \<open>xs <~~> ys \<longleftrightarrow> mset xs = mset ys\<close>
proof
  assume \<open>mset xs = mset ys\<close>
  then show \<open>xs <~~> ys\<close>
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    from Cons.prems [symmetric] have \<open>mset xs = mset (remove1 x ys)\<close>
      by simp
    then have \<open>xs <~~> remove1 x ys\<close>
      by (rule Cons.IH)
    then have \<open>x # xs <~~> x # remove1 x ys\<close>
      by (rule perm.Cons)
    moreover from Cons.prems have \<open>x \<in> set ys\<close>
      by (auto dest: union_single_eq_member)
    then have \<open>x # remove1 x ys <~~> ys\<close>
      by (induction ys) auto
    ultimately show \<open>x # xs <~~> ys\<close>
      by (rule perm.trans)
  qed
next
  assume \<open>xs <~~> ys\<close>
  then show \<open>mset xs = mset ys\<close>
    by induction simp_all
qed

theorem mset_eq_perm: \<open>mset xs = mset ys \<longleftrightarrow> xs <~~> ys\<close>
  by (simp add: perm_iff_eq_mset)


subsection \<open>Nontrivial conclusions\<close>

proposition perm_swap:
  \<open>xs[i := xs ! j, j := xs ! i] <~~> xs\<close>
  if \<open>i < length xs\<close> \<open>j < length xs\<close>
  using that by (simp add: perm_iff_eq_mset mset_swap)

proposition mset_le_perm_append: "mset xs \<subseteq># mset ys \<longleftrightarrow> (\<exists>zs. xs @ zs <~~> ys)"
  by (auto simp add: perm_iff_eq_mset mset_subset_eq_exists_conv ex_mset dest: sym)

proposition perm_set_eq: "xs <~~> ys \<Longrightarrow> set xs = set ys"
  by (rule mset_eq_setD) (simp add: perm_iff_eq_mset)

proposition perm_distinct_iff: "xs <~~> ys \<Longrightarrow> distinct xs \<longleftrightarrow> distinct ys"
  by (rule mset_eq_imp_distinct_iff) (simp add: perm_iff_eq_mset)

theorem eq_set_perm_remdups: "set xs = set ys \<Longrightarrow> remdups xs <~~> remdups ys"
  by (simp add: perm_iff_eq_mset set_eq_iff_mset_remdups_eq)

proposition perm_remdups_iff_eq_set: "remdups x <~~> remdups y \<longleftrightarrow> set x = set y"
  by (simp add: perm_iff_eq_mset set_eq_iff_mset_remdups_eq)

theorem permutation_Ex_bij:
  assumes "xs <~~> ys"
  shows "\<exists>f. bij_betw f {..<length xs} {..<length ys} \<and> (\<forall>i<length xs. xs ! i = ys ! (f i))"
proof -
  from assms have \<open>mset ys = mset xs\<close>
    by (simp add: perm_iff_eq_mset)
  then obtain f where \<open>bij_betw f {..<length ys} {..<length xs}\<close>
    \<open>xs = map (\<lambda>n. ys ! f n) [0..<length ys]\<close>
    by (rule mset_eq_permutation)
  then show ?thesis by auto
qed

proposition perm_finite: "finite {B. B <~~> A}"
  using mset_eq_finite by (auto simp add: perm_iff_eq_mset)


subsection \<open>Trivial conclusions:\<close>

proposition perm_empty_imp: "[] <~~> ys \<Longrightarrow> ys = []"
  by (simp add: perm_iff_eq_mset)


text \<open>\medskip This more general theorem is easier to understand!\<close>

proposition perm_length: "xs <~~> ys \<Longrightarrow> length xs = length ys"
  by (rule mset_eq_length) (simp add: perm_iff_eq_mset)

proposition perm_sym: "xs <~~> ys \<Longrightarrow> ys <~~> xs"
  by (simp add: perm_iff_eq_mset)


text \<open>We can insert the head anywhere in the list.\<close>

proposition perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  by (simp add: perm_iff_eq_mset)

proposition perm_append_swap: "xs @ ys <~~> ys @ xs"
  by (simp add: perm_iff_eq_mset)

proposition perm_append_single: "a # xs <~~> xs @ [a]"
  by (simp add: perm_iff_eq_mset)

proposition perm_rev: "rev xs <~~> xs"
  by (simp add: perm_iff_eq_mset)

proposition perm_append1: "xs <~~> ys \<Longrightarrow> l @ xs <~~> l @ ys"
  by (simp add: perm_iff_eq_mset)

proposition perm_append2: "xs <~~> ys \<Longrightarrow> xs @ l <~~> ys @ l"
  by (simp add: perm_iff_eq_mset)

proposition perm_empty [iff]: "[] <~~> xs \<longleftrightarrow> xs = []"
  by (simp add: perm_iff_eq_mset)

proposition perm_empty2 [iff]: "xs <~~> [] \<longleftrightarrow> xs = []"
  by (simp add: perm_iff_eq_mset)

proposition perm_sing_imp: "ys <~~> xs \<Longrightarrow> xs = [y] \<Longrightarrow> ys = [y]"
  by (simp add: perm_iff_eq_mset)

proposition perm_sing_eq [iff]: "ys <~~> [y] \<longleftrightarrow> ys = [y]"
  by (simp add: perm_iff_eq_mset)

proposition perm_sing_eq2 [iff]: "[y] <~~> ys \<longleftrightarrow> ys = [y]"
  by (simp add: perm_iff_eq_mset)

proposition perm_remove: "x \<in> set ys \<Longrightarrow> ys <~~> x # remove1 x ys"
  by (simp add: perm_iff_eq_mset)


text \<open>\medskip Congruence rule\<close>

proposition perm_remove_perm: "xs <~~> ys \<Longrightarrow> remove1 z xs <~~> remove1 z ys"
  by (simp add: perm_iff_eq_mset)

proposition remove_hd [simp]: "remove1 z (z # xs) = xs"
  by (simp add: perm_iff_eq_mset)

proposition cons_perm_imp_perm: "z # xs <~~> z # ys \<Longrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

proposition cons_perm_eq [simp]: "z#xs <~~> z#ys \<longleftrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

proposition append_perm_imp_perm: "zs @ xs <~~> zs @ ys \<Longrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

proposition perm_append1_eq [iff]: "zs @ xs <~~> zs @ ys \<longleftrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

proposition perm_append2_eq [iff]: "xs @ zs <~~> ys @ zs \<longleftrightarrow> xs <~~> ys"
  by (simp add: perm_iff_eq_mset)

end
