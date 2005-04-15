(*  Title:      HOL/Library/List_lexord.thy
    ID:         $Id$
    Author:     Norbert Voelker
*)

header {* Instantiation of order classes for lexord on lists *}

theory List_lexord
imports Main
begin

instance list :: (ord) ord ..
defs(overloaded)
  list_le_def:  "(xs::('a::ord) list) \<le> ys \<equiv> (xs < ys \<or> xs = ys)" 
  list_less_def: "(xs::('a::ord) list) < ys \<equiv> (xs,ys) \<in> lexord {(u,v). u < v}"

lemmas list_ord_defs = list_less_def list_le_def

instance list::(order)order
  apply (intro_classes, unfold list_ord_defs)
  apply (rule disjI2, safe)
  apply (blast intro: lexord_trans transI order_less_trans)
  apply (rule_tac r1 = "{(a::'a,b). a < b}" in lexord_irreflexive [THEN notE])
  apply simp
  apply (blast intro: lexord_trans transI order_less_trans)
  apply (rule_tac r1 = "{(a::'a,b). a < b}" in lexord_irreflexive [THEN notE])
  apply simp
  by assumption

instance list::(linorder)linorder
  apply (intro_classes, unfold list_le_def list_less_def, safe)
  apply (cut_tac x="x" and y="y" and  r = "{(a,b). a < b}"  in lexord_linear)
  by (force, simp)

lemma not_less_Nil[simp]: "~(x < [])";
  by (unfold list_less_def, simp);

lemma Nil_less_Cons[simp]: "[] < a # x";
  by (unfold list_less_def, simp);

lemma Cons_less_Cons[simp]: "(a # x < b # y) = (a < b | a = b & x < y)";
  by (unfold list_less_def, simp);

lemma le_Nil[simp]: "(x <= [])   = (x = [])";
  by (unfold list_ord_defs, case_tac x, auto);

lemma Nil_le_Cons[simp]: "([] <= x)";
  by (unfold list_ord_defs, case_tac x, auto);

lemma Cons_le_Cons[simp]: "(a # x <= b # y) = (a < b | a = b & x <= y)";
  by (unfold list_ord_defs, auto);

end