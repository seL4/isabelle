(* Author: Tobias Nipkow *)

section {* List Insertion and Deletion *}

theory List_Ins_Del
imports Sorted_Less
begin

subsection \<open>Elements in a list\<close>

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x#xs) = Set.insert x (elems xs)"

lemma elems_app: "elems (xs @ ys) = (elems xs \<union> elems ys)"
by (induction xs) auto

lemma elems_eq_set: "elems xs = set xs"
by (induction xs) auto

lemma sorted_Cons_iff:
  "sorted(x # xs) = (sorted xs \<and> (\<forall>y \<in> elems xs. x < y))"
by(simp add: elems_eq_set Sorted_Less.sorted_Cons_iff)

lemma sorted_snoc_iff:
  "sorted(xs @ [x]) = (sorted xs \<and> (\<forall>y \<in> elems xs. y < x))"
by(simp add: elems_eq_set Sorted_Less.sorted_snoc_iff)

lemma sorted_ConsD: "sorted (y # xs) \<Longrightarrow> x \<in> elems xs \<Longrightarrow> y < x"
by (simp add: sorted_Cons_iff)

lemma sorted_snocD: "sorted (xs @ [y]) \<Longrightarrow> x \<in> elems xs \<Longrightarrow> x < y"
by (simp add: sorted_snoc_iff)

lemmas elems_simps0 = sorted_lems elems_app
lemmas elems_simps = elems_simps0 sorted_Cons_iff sorted_snoc_iff
lemmas sortedD = sorted_ConsD sorted_snocD


subsection \<open>Inserting into an ordered list without duplicates:\<close>

fun ins_list :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ins_list x [] = [x]" |
"ins_list x (y#zs) =
  (if x < y then x#y#zs else if x=y then x#zs else y # ins_list x zs)"

lemma set_ins_list[simp]: "elems (ins_list x xs) = insert x (elems xs)"
by(induction xs) auto

lemma distinct_if_sorted: "sorted xs \<Longrightarrow> distinct xs"
apply(induction xs rule: sorted.induct)
apply auto
by (metis in_set_conv_decomp_first less_imp_not_less sorted_mid_iff2)

lemma sorted_ins_list: "sorted xs \<Longrightarrow> sorted(ins_list x xs)"
by(induction xs rule: sorted.induct) auto

lemma ins_list_sorted1: "sorted (xs @ [y]) \<Longrightarrow> y \<le> x \<Longrightarrow>
  ins_list x (xs @ y # ys) = xs @ ins_list x (y#ys)"
by(induction xs) (auto simp: sorted_lems)

lemma ins_list_sorted2: "sorted (xs @ [y]) \<Longrightarrow> x < y \<Longrightarrow>
  ins_list x (xs @ y # ys) = ins_list x xs @ (y#ys)"
by(induction xs) (auto simp: sorted_lems)

lemmas ins_simps = sorted_lems ins_list_sorted1 ins_list_sorted2


subsection \<open>Delete one occurrence of an element from a list:\<close>

fun del_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"del_list a [] = []" |
"del_list a (x#xs) = (if a=x then xs else x # del_list a xs)"

lemma del_list_idem: "x \<notin> elems xs \<Longrightarrow> del_list x xs = xs"
by (induct xs) simp_all

lemma elems_del_list_eq [simp]:
  "distinct xs \<Longrightarrow> elems (del_list x xs) = elems xs - {x}"
apply(induct xs)
 apply simp
apply (simp add: elems_eq_set)
apply blast
done

lemma sorted_del_list: "sorted xs \<Longrightarrow> sorted(del_list x xs)"
apply(induction xs rule: sorted.induct)
apply auto
by (meson order.strict_trans sorted_Cons_iff)

lemma del_list_sorted1: "sorted (xs @ [x]) \<Longrightarrow> x \<le> y \<Longrightarrow>
  del_list y (xs @ x # ys) = xs @ del_list y (x # ys)"
by (induction xs) (auto simp: sorted_mid_iff2)

lemma del_list_sorted2: "sorted (xs @ x # ys) \<Longrightarrow> y < x \<Longrightarrow>
  del_list y (xs @ x # ys) = del_list y xs @ x # ys"
by (induction xs) (auto simp: sorted_Cons_iff intro!: del_list_idem)

lemma del_list_sorted3:
  "sorted (xs @ x # ys @ y # zs) \<Longrightarrow> a < y \<Longrightarrow>
  del_list a (xs @ x # ys @ y # zs) = del_list a (xs @ x # ys) @ y # zs"
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted2)

lemma del_list_sorted4:
  "sorted (xs @ x # ys @ y # zs @ z # us) \<Longrightarrow> a < z \<Longrightarrow>
  del_list a (xs @ x # ys @ y # zs @ z # us) = del_list a (xs @ x # ys @ y # zs) @ z # us"
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted3)

lemma del_list_sorted5:
  "sorted (xs @ x # ys @ y # zs @ z # us @ u # vs) \<Longrightarrow> a < u \<Longrightarrow>
   del_list a (xs @ x # ys @ y # zs @ z # us @ u # vs) =
   del_list a (xs @ x # ys @ y # zs @ z # us) @ u # vs" 
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted4)

lemmas del_simps = sorted_lems
  del_list_sorted1
  del_list_sorted2
  del_list_sorted3
  del_list_sorted4
  del_list_sorted5

end
