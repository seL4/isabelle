(*  Title:      HOL/Library/List_lexord.thy
    Author:     Norbert Voelker
*)

header {* Lexicographic order on lists *}

theory List_lexord
imports List Main
begin

instantiation list :: (ord) ord
begin

definition
  list_less_def [code del]: "(xs::('a::ord) list) < ys \<longleftrightarrow> (xs, ys) \<in> lexord {(u,v). u < v}"

definition
  list_le_def [code del]: "(xs::('a::ord) list) \<le> ys \<longleftrightarrow> (xs < ys \<or> xs = ys)"

instance ..

end

instance list :: (order) order
proof
  fix xs :: "'a list"
  show "xs \<le> xs" by (simp add: list_le_def)
next
  fix xs ys zs :: "'a list"
  assume "xs \<le> ys" and "ys \<le> zs"
  then show "xs \<le> zs" by (auto simp add: list_le_def list_less_def)
    (rule lexord_trans, auto intro: transI)
next
  fix xs ys :: "'a list"
  assume "xs \<le> ys" and "ys \<le> xs"
  then show "xs = ys" apply (auto simp add: list_le_def list_less_def)
  apply (rule lexord_irreflexive [THEN notE])
  defer
  apply (rule lexord_trans) apply (auto intro: transI) done
next
  fix xs ys :: "'a list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs" 
  apply (auto simp add: list_less_def list_le_def)
  defer
  apply (rule lexord_irreflexive [THEN notE])
  apply auto
  apply (rule lexord_irreflexive [THEN notE])
  defer
  apply (rule lexord_trans) apply (auto intro: transI) done
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

definition
  [code del]: "(inf \<Colon> 'a list \<Rightarrow> _) = min"

definition
  [code del]: "(sup \<Colon> 'a list \<Rightarrow> _) = max"

instance
  by intro_classes
    (auto simp add: inf_list_def sup_list_def min_max.sup_inf_distrib1)

end

lemma not_less_Nil [simp]: "\<not> (x < [])"
  by (unfold list_less_def) simp

lemma Nil_less_Cons [simp]: "[] < a # x"
  by (unfold list_less_def) simp

lemma Cons_less_Cons [simp]: "a # x < b # y \<longleftrightarrow> a < b \<or> a = b \<and> x < y"
  by (unfold list_less_def) simp

lemma le_Nil [simp]: "x \<le> [] \<longleftrightarrow> x = []"
  by (unfold list_le_def, cases x) auto

lemma Nil_le_Cons [simp]: "[] \<le> x"
  by (unfold list_le_def, cases x) auto

lemma Cons_le_Cons [simp]: "a # x \<le> b # y \<longleftrightarrow> a < b \<or> a = b \<and> x \<le> y"
  by (unfold list_le_def) auto

lemma less_code [code]:
  "xs < ([]\<Colon>'a\<Colon>{eq, order} list) \<longleftrightarrow> False"
  "[] < (x\<Colon>'a\<Colon>{eq, order}) # xs \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{eq, order}) # xs < y # ys \<longleftrightarrow> x < y \<or> x = y \<and> xs < ys"
  by simp_all

lemma less_eq_code [code]:
  "x # xs \<le> ([]\<Colon>'a\<Colon>{eq, order} list) \<longleftrightarrow> False"
  "[] \<le> (xs\<Colon>'a\<Colon>{eq, order} list) \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{eq, order}) # xs \<le> y # ys \<longleftrightarrow> x < y \<or> x = y \<and> xs \<le> ys"
  by simp_all

end
