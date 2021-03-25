(*  Author:     Lars Hupel, TU München
*)

section \<open>Disjoint FSets\<close>

theory Disjoint_FSets
  imports
    "HOL-Library.Finite_Map"
    Disjoint_Sets
begin

context
  includes fset.lifting
begin

lift_definition fdisjnt :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" is disjnt .

lemma fdisjnt_alt_def: "fdisjnt M N \<longleftrightarrow> (M |\<inter>| N = {||})"
by transfer (simp add: disjnt_def)

lemma fdisjnt_insert: "x |\<notin>| N \<Longrightarrow> fdisjnt M N \<Longrightarrow> fdisjnt (finsert x M) N"
by transfer' (rule disjnt_insert)

lemma fdisjnt_subset_right: "N' |\<subseteq>| N \<Longrightarrow> fdisjnt M N \<Longrightarrow> fdisjnt M N'"
unfolding fdisjnt_alt_def by auto

lemma fdisjnt_subset_left: "N' |\<subseteq>| N \<Longrightarrow> fdisjnt N M \<Longrightarrow> fdisjnt N' M"
unfolding fdisjnt_alt_def by auto

lemma fdisjnt_union_right: "fdisjnt M A \<Longrightarrow> fdisjnt M B \<Longrightarrow> fdisjnt M (A |\<union>| B)"
unfolding fdisjnt_alt_def by auto

lemma fdisjnt_union_left: "fdisjnt A M \<Longrightarrow> fdisjnt B M \<Longrightarrow> fdisjnt (A |\<union>| B) M"
unfolding fdisjnt_alt_def by auto

lemma fdisjnt_swap: "fdisjnt M N \<Longrightarrow> fdisjnt N M"
including fset.lifting by transfer' (auto simp: disjnt_def)

lemma distinct_append_fset:
  assumes "distinct xs" "distinct ys" "fdisjnt (fset_of_list xs) (fset_of_list ys)"
  shows "distinct (xs @ ys)"
using assms
by transfer' (simp add: disjnt_def)

lemma fdisjnt_contrI:
  assumes "\<And>x. x |\<in>| M \<Longrightarrow> x |\<in>| N \<Longrightarrow> False"
  shows "fdisjnt M N"
using assms
by transfer' (auto simp: disjnt_def)

lemma fdisjnt_Union_left: "fdisjnt (ffUnion S) T \<longleftrightarrow> fBall S (\<lambda>S. fdisjnt S T)"
by transfer' (auto simp: disjnt_def)

lemma fdisjnt_Union_right: "fdisjnt T (ffUnion S) \<longleftrightarrow> fBall S (\<lambda>S. fdisjnt T S)"
by transfer' (auto simp: disjnt_def)

lemma fdisjnt_ge_max: "fBall X (\<lambda>x. x > fMax Y) \<Longrightarrow> fdisjnt X Y"
by transfer (auto intro: disjnt_ge_max)

end

(* FIXME should be provable without lifting *)
lemma fmadd_disjnt: "fdisjnt (fmdom m) (fmdom n) \<Longrightarrow> m ++\<^sub>f n = n ++\<^sub>f m"
unfolding fdisjnt_alt_def
including fset.lifting fmap.lifting
apply transfer
apply (rule ext)
apply (auto simp: map_add_def split: option.splits)
done

end
