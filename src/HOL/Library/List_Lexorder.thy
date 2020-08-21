(*  Title:      HOL/Library/List_Lexorder.thy
    Author:     Norbert Voelker
*)

section \<open>Lexicographic order on lists\<close>

theory List_Lexorder
imports Main
begin

instantiation list :: (ord) ord
begin

definition
  list_less_def: "xs < ys \<longleftrightarrow> (xs, ys) \<in> lexord {(u, v). u < v}"

definition
  list_le_def: "(xs :: _ list) \<le> ys \<longleftrightarrow> xs < ys \<or> xs = ys"

instance ..

end

instance list :: (order) order
proof
  let ?r = "{(u, v::'a). u < v}"
  have tr: "trans ?r"
    using trans_def by fastforce
  have \<section>: False
    if "(xs,ys) \<in> lexord ?r" "(ys,xs) \<in> lexord ?r" for xs ys :: "'a list"
  proof -
    have "(xs,xs) \<in> lexord ?r"
      using that transD [OF lexord_transI [OF tr]] by blast
    then show False
      by (meson case_prodD lexord_irreflexive less_irrefl mem_Collect_eq)
  qed
  show "xs \<le> xs" for xs :: "'a list" by (simp add: list_le_def)
  show "xs \<le> zs" if "xs \<le> ys" and "ys \<le> zs" for xs ys zs :: "'a list"
    using that transD [OF lexord_transI [OF tr]] by (auto simp add: list_le_def list_less_def)
  show "xs = ys" if "xs \<le> ys" "ys \<le> xs" for xs ys :: "'a list"
    using \<section> that list_le_def list_less_def by blast
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs" for xs ys :: "'a list"
    by (auto simp add: list_less_def list_le_def dest: \<section>)
qed

instance list :: (linorder) linorder
proof
  fix xs ys :: "'a list"
  have "total (lexord {(u, v::'a). u < v})"
    by (rule total_lexord) (auto simp: total_on_def)
  then show "xs \<le> ys \<or> ys \<le> xs"
    by (auto simp add: total_on_def list_le_def list_less_def)
qed

instantiation list :: (linorder) distrib_lattice
begin

definition "(inf :: 'a list \<Rightarrow> _) = min"

definition "(sup :: 'a list \<Rightarrow> _) = max"

instance
  by standard (auto simp add: inf_list_def sup_list_def max_min_distrib2)

end

lemma not_less_Nil [simp]: "\<not> x < []"
  by (simp add: list_less_def)

lemma Nil_less_Cons [simp]: "[] < a # x"
  by (simp add: list_less_def)

lemma Cons_less_Cons [simp]: "a # x < b # y \<longleftrightarrow> a < b \<or> a = b \<and> x < y"
  by (simp add: list_less_def)

lemma le_Nil [simp]: "x \<le> [] \<longleftrightarrow> x = []"
  unfolding list_le_def by (cases x) auto

lemma Nil_le_Cons [simp]: "[] \<le> x"
  unfolding list_le_def by (cases x) auto

lemma Cons_le_Cons [simp]: "a # x \<le> b # y \<longleftrightarrow> a < b \<or> a = b \<and> x \<le> y"
  unfolding list_le_def by auto

instantiation list :: (order) order_bot
begin

definition "bot = []"

instance
  by standard (simp add: bot_list_def)

end

lemma less_list_code [code]:
  "xs < ([]::'a::{equal, order} list) \<longleftrightarrow> False"
  "[] < (x::'a::{equal, order}) # xs \<longleftrightarrow> True"
  "(x::'a::{equal, order}) # xs < y # ys \<longleftrightarrow> x < y \<or> x = y \<and> xs < ys"
  by simp_all

lemma less_eq_list_code [code]:
  "x # xs \<le> ([]::'a::{equal, order} list) \<longleftrightarrow> False"
  "[] \<le> (xs::'a::{equal, order} list) \<longleftrightarrow> True"
  "(x::'a::{equal, order}) # xs \<le> y # ys \<longleftrightarrow> x < y \<or> x = y \<and> xs \<le> ys"
  by simp_all

end
