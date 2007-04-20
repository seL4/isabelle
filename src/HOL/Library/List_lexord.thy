(*  Title:      HOL/Library/List_lexord.thy
    ID:         $Id$
    Author:     Norbert Voelker
*)

header {* Lexicographic order on lists *}

theory List_lexord
imports Main
begin

instance list :: (ord) ord
  list_le_def:  "(xs::('a::ord) list) \<le> ys \<equiv> (xs < ys \<or> xs = ys)"
  list_less_def: "(xs::('a::ord) list) < ys \<equiv> (xs, ys) \<in> lexord {(u,v). u < v}" ..

lemmas list_ord_defs [code nofunc] = list_less_def list_le_def

instance list :: (order) order
  apply (intro_classes, unfold list_ord_defs)
  apply safe
  apply (rule_tac r1 = "{(a::'a,b). a < b}" in lexord_irreflexive [THEN notE])
  apply simp
  apply assumption
  apply (blast intro: lexord_trans transI order_less_trans)
  apply (rule_tac r1 = "{(a::'a,b). a < b}" in lexord_irreflexive [THEN notE])
  apply simp
  apply (blast intro: lexord_trans transI order_less_trans)
  done

instance list :: (linorder) linorder
  apply (intro_classes, unfold list_le_def list_less_def, safe)
  apply (cut_tac x = x and y = y and  r = "{(a,b). a < b}"  in lexord_linear)
   apply force
  apply simp
  done

instance list :: (linorder) distrib_lattice
  "inf \<equiv> min"
  "sup \<equiv> max"
  by intro_classes
    (auto simp add: inf_list_def sup_list_def min_max.sup_inf_distrib1)

lemmas [code nofunc] = inf_list_def sup_list_def

lemma not_less_Nil [simp]: "\<not> (x < [])"
  by (unfold list_less_def) simp

lemma Nil_less_Cons [simp]: "[] < a # x"
  by (unfold list_less_def) simp

lemma Cons_less_Cons [simp]: "a # x < b # y \<longleftrightarrow> a < b \<or> a = b \<and> x < y"
  by (unfold list_less_def) simp

lemma le_Nil [simp]: "x \<le> [] \<longleftrightarrow> x = []"
  by (unfold list_ord_defs, cases x) auto

lemma Nil_le_Cons [simp]: "[] \<le> x"
  by (unfold list_ord_defs, cases x) auto

lemma Cons_le_Cons [simp]: "a # x \<le> b # y \<longleftrightarrow> a < b \<or> a = b \<and> x \<le> y"
  by (unfold list_ord_defs) auto

lemma less_code [code func]:
  "xs < ([]\<Colon>'a\<Colon>{eq, order} list) \<longleftrightarrow> False"
  "[] < (x\<Colon>'a\<Colon>{eq, order}) # xs \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{eq, order}) # xs < y # ys \<longleftrightarrow> x < y \<or> x = y \<and> xs < ys"
  by simp_all

lemma less_eq_code [code func]:
  "x # xs \<le> ([]\<Colon>'a\<Colon>{eq, order} list) \<longleftrightarrow> False"
  "[] \<le> (xs\<Colon>'a\<Colon>{eq, order} list) \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{eq, order}) # xs \<le> y # ys \<longleftrightarrow> x < y \<or> x = y \<and> xs \<le> ys"
  by simp_all

end
