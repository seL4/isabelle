(*  Title:      HOL/Library/List_lexord.thy
    Author:     Norbert Voelker
*)

section {* Lexicographic order on lists *}

theory List_lexord
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
  fix xs :: "'a list"
  show "xs \<le> xs" by (simp add: list_le_def)
next
  fix xs ys zs :: "'a list"
  assume "xs \<le> ys" and "ys \<le> zs"
  then show "xs \<le> zs"
    apply (auto simp add: list_le_def list_less_def)
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "'a list"
  assume "xs \<le> ys" and "ys \<le> xs"
  then show "xs = ys"
    apply (auto simp add: list_le_def list_less_def)
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "'a list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    apply (auto simp add: list_less_def list_le_def)
    defer
    apply (rule lexord_irreflexive [THEN notE])
    apply auto
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
qed

instance list :: (linorder) linorder
proof
  fix xs ys :: "'a list"
  have "(xs, ys) \<in> lexord {(u, v). u < v} \<or> xs = ys \<or> (ys, xs) \<in> lexord {(u, v). u < v}"
    by (rule lexord_linear) auto
  then show "xs \<le> ys \<or> ys \<le> xs"
    by (auto simp add: list_le_def list_less_def)
qed

instantiation list :: (linorder) distrib_lattice
begin

definition "(inf \<Colon> 'a list \<Rightarrow> _) = min"

definition "(sup \<Colon> 'a list \<Rightarrow> _) = max"

instance
  by default (auto simp add: inf_list_def sup_list_def max_min_distrib2)

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
  by default (simp add: bot_list_def)

end

lemma less_list_code [code]:
  "xs < ([]\<Colon>'a\<Colon>{equal, order} list) \<longleftrightarrow> False"
  "[] < (x\<Colon>'a\<Colon>{equal, order}) # xs \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{equal, order}) # xs < y # ys \<longleftrightarrow> x < y \<or> x = y \<and> xs < ys"
  by simp_all

lemma less_eq_list_code [code]:
  "x # xs \<le> ([]\<Colon>'a\<Colon>{equal, order} list) \<longleftrightarrow> False"
  "[] \<le> (xs\<Colon>'a\<Colon>{equal, order} list) \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{equal, order}) # xs \<le> y # ys \<longleftrightarrow> x < y \<or> x = y \<and> xs \<le> ys"
  by simp_all

end
