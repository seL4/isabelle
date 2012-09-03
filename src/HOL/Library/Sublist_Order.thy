(*  Title:      HOL/Library/Sublist_Order.thy
    Authors:    Peter Lammich, Uni Muenster <peter.lammich@uni-muenster.de>
                Florian Haftmann, Tobias Nipkow, TU Muenchen
*)

header {* Sublist Ordering *}

theory Sublist_Order
imports Sublist
begin

text {*
  This theory defines sublist ordering on lists.
  A list @{text ys} is a sublist of a list @{text xs},
  iff one obtains @{text ys} by erasing some elements from @{text xs}.
*}

subsection {* Definitions and basic lemmas *}

instantiation list :: (type) ord
begin

definition
  "(xs :: 'a list) \<le> ys \<longleftrightarrow> sub xs ys"

definition
  "(xs :: 'a list) < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"

instance ..

end

instance list :: (type) order
proof
  fix xs ys :: "'a list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs" unfolding less_list_def .. 
next
  fix xs :: "'a list"
  show "xs \<le> xs" by (simp add: less_eq_list_def)
next
  fix xs ys :: "'a list"
  assume "xs <= ys" and "ys <= xs"
  thus "xs = ys" by (unfold less_eq_list_def) (rule sub_antisym)
next
  fix xs ys zs :: "'a list"
  assume "xs <= ys" and "ys <= zs"
  thus "xs <= zs" by (unfold less_eq_list_def) (rule sub_trans)
qed

lemmas less_eq_list_induct [consumes 1, case_names empty drop take] =
  emb.induct [of "op =", folded less_eq_list_def]
lemmas less_eq_list_drop = emb.emb_Cons [of "op =", folded less_eq_list_def]
lemmas le_list_Cons2_iff [simp, code] = sub_Cons2_iff [folded less_eq_list_def]
lemmas le_list_map = sub_map [folded less_eq_list_def]
lemmas le_list_filter = sub_filter [folded less_eq_list_def]
lemmas le_list_length = emb_length [of "op =", folded less_eq_list_def]

lemma less_list_length: "xs < ys \<Longrightarrow> length xs < length ys"
  by (metis emb_length sub_same_length le_neq_implies_less less_list_def less_eq_list_def)

lemma less_list_empty [simp]: "[] < xs \<longleftrightarrow> xs \<noteq> []"
  by (metis less_eq_list_def emb_Nil order_less_le)

lemma less_list_below_empty [simp]: "xs < [] \<longleftrightarrow> False"
  by (metis emb_Nil less_eq_list_def less_list_def)

lemma less_list_drop: "xs < ys \<Longrightarrow> xs < x # ys"
  by (unfold less_le less_eq_list_def) (auto)

lemma less_list_take_iff: "x # xs < x # ys \<longleftrightarrow> xs < ys"
  by (metis sub_Cons2_iff less_list_def less_eq_list_def)

lemma less_list_drop_many: "xs < ys \<Longrightarrow> xs < zs @ ys"
  by (metis sub_append_le_same_iff sub_drop_many order_less_le self_append_conv2 less_eq_list_def)

lemma less_list_take_many_iff: "zs @ xs < zs @ ys \<longleftrightarrow> xs < ys"
  by (metis less_list_def less_eq_list_def sub_append')

lemma less_list_rev_take: "xs @ zs < ys @ zs \<longleftrightarrow> xs < ys"
  by (unfold less_le less_eq_list_def) auto

end
