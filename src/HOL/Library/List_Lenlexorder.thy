(*  Title:      HOL/Library/List_Lenlexorder.thy
*)

section \<open>Lexicographic order on lists\<close>

text \<open>This version prioritises length and can yield wellorderings\<close>

theory List_Lenlexorder
imports Main
begin


instantiation list :: (ord) ord
begin

definition
  list_less_def: "xs < ys \<longleftrightarrow> (xs, ys) \<in> lenlex {(u, v). u < v}"

definition
  list_le_def: "(xs :: _ list) \<le> ys \<longleftrightarrow> xs < ys \<or> xs = ys"

instance ..

end

instance list :: (order) order
proof
  have tr: "trans {(u, v::'a). u < v}"
    using trans_def by fastforce
  have \<section>: False
    if "(xs,ys) \<in> lenlex {(u, v). u < v}" "(ys,xs) \<in> lenlex {(u, v). u < v}" for xs ys :: "'a list"
  proof -
    have "(xs,xs) \<in> lenlex {(u, v). u < v}"
      using that transD [OF lenlex_transI [OF tr]] by blast
    then show False
      by (meson case_prodD lenlex_irreflexive less_irrefl mem_Collect_eq)
  qed
  show "xs \<le> xs" for xs :: "'a list" by (simp add: list_le_def)
  show "xs \<le> zs" if "xs \<le> ys" and "ys \<le> zs" for xs ys zs :: "'a list"
    using that transD [OF lenlex_transI [OF tr]] by (auto simp add: list_le_def list_less_def)
  show "xs = ys" if "xs \<le> ys" "ys \<le> xs" for xs ys :: "'a list"
    using \<section> that list_le_def list_less_def by blast
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs" for xs ys :: "'a list"
    by (auto simp add: list_less_def list_le_def dest: \<section>)
qed

instance list :: (linorder) linorder
proof
  fix xs ys :: "'a list"
  have "total (lenlex {(u, v::'a). u < v})"
    by (rule total_lenlex) (auto simp: total_on_def)
  then show "xs \<le> ys \<or> ys \<le> xs"
    by (auto simp add: total_on_def list_le_def list_less_def)
qed

instance list :: (wellorder) wellorder
proof
  fix P :: "'a list \<Rightarrow> bool" and a
  assume "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x" 
  then show "P a"
    unfolding list_less_def by (metis wf_lenlex wf_induct wf_lenlex wf)
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

lemma Cons_less_Cons: "a # x < b # y \<longleftrightarrow> length x < length y \<or> length x = length y \<and> (a < b \<or> a = b \<and> x < y)"
  using lenlex_length
  by (fastforce simp: list_less_def Cons_lenlex_iff)

lemma le_Nil [simp]: "x \<le> [] \<longleftrightarrow> x = []"
  unfolding list_le_def by (cases x) auto

lemma Nil_le_Cons [simp]: "[] \<le> x"
  unfolding list_le_def by (cases x) auto

lemma Cons_le_Cons: "a # x \<le> b # y \<longleftrightarrow> length x < length y \<or> length x = length y \<and> (a < b \<or> a = b \<and> x \<le> y)"
  by (auto simp: list_le_def Cons_less_Cons)

instantiation list :: (order) order_bot
begin

definition "bot = []"

instance
  by standard (simp add: bot_list_def)

end

end
