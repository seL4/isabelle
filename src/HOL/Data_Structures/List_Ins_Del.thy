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

text{* The above two rules introduce quantifiers. It turns out
that in practice this is not a problem because of the simplicity of
the "isin" functions that implement @{const elems}. Nevertheless
it is possible to avoid the quantifiers with the help of some rewrite rules: *}

lemma sorted_ConsD: "sorted (y # xs) \<Longrightarrow> x \<in> elems xs \<Longrightarrow> y < x"
by (simp add: sorted_Cons_iff)

lemma sorted_snocD: "sorted (xs @ [y]) \<Longrightarrow> x \<in> elems xs \<Longrightarrow> x < y"
by (simp add: sorted_snoc_iff)

lemma sorted_ConsD2: "sorted (y # xs) \<Longrightarrow> x \<le> y \<Longrightarrow> x \<notin> elems xs"
using leD sorted_ConsD by blast

lemma sorted_snocD2: "sorted (xs @ [y]) \<Longrightarrow> y \<le> x \<Longrightarrow> x \<notin> elems xs"
using leD sorted_snocD by blast

lemmas elems_simps = sorted_lems elems_app
lemmas elems_simps1 = elems_simps sorted_Cons_iff sorted_snoc_iff
lemmas elems_simps2 = elems_simps sorted_ConsD sorted_snocD sorted_ConsD2 sorted_snocD2


subsection \<open>Inserting into an ordered list without duplicates:\<close>

fun ins_list :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ins_list x [] = [x]" |
"ins_list x (a#xs) =
  (if x < a then x#a#xs else if x=a then a#xs else a # ins_list x xs)"

lemma set_ins_list: "elems (ins_list x xs) = insert x (elems xs)"
by(induction xs) auto

lemma distinct_if_sorted: "sorted xs \<Longrightarrow> distinct xs"
apply(induction xs rule: sorted.induct)
apply auto
by (metis in_set_conv_decomp_first less_imp_not_less sorted_mid_iff2)

lemma sorted_ins_list: "sorted xs \<Longrightarrow> sorted(ins_list x xs)"
by(induction xs rule: sorted.induct) auto

lemma ins_list_sorted1: "sorted (xs @ [a]) \<Longrightarrow> a \<le> x \<Longrightarrow>
  ins_list x (xs @ a # ys) = xs @ ins_list x (a#ys)"
by(induction xs) (auto simp: sorted_lems)

lemma ins_list_sorted2: "sorted (xs @ [a]) \<Longrightarrow> x < a \<Longrightarrow>
  ins_list x (xs @ a # ys) = ins_list x xs @ (a#ys)"
by(induction xs) (auto simp: sorted_lems)

lemmas ins_list_simps = sorted_lems ins_list_sorted1 ins_list_sorted2


subsection \<open>Delete one occurrence of an element from a list:\<close>

fun del_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"del_list x [] = []" |
"del_list x (a#xs) = (if x=a then xs else a # del_list x xs)"

lemma del_list_idem: "x \<notin> elems xs \<Longrightarrow> del_list x xs = xs"
by (induct xs) simp_all

lemma elems_del_list_eq:
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

lemma del_list_sorted1: "sorted (xs @ [a]) \<Longrightarrow> a \<le> x \<Longrightarrow>
  del_list x (xs @ a # ys) = xs @ del_list x (a # ys)"
by (induction xs) (auto simp: sorted_mid_iff2)

lemma del_list_sorted2: "sorted (xs @ a # ys) \<Longrightarrow> x < a \<Longrightarrow>
  del_list x (xs @ a # ys) = del_list x xs @ a # ys"
by (induction xs) (auto simp: sorted_Cons_iff intro!: del_list_idem)

lemma del_list_sorted3:
  "sorted (xs @ a # ys @ b # zs) \<Longrightarrow> x < b \<Longrightarrow>
  del_list x (xs @ a # ys @ b # zs) = del_list x (xs @ a # ys) @ b # zs"
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted2)

lemma del_list_sorted4:
  "sorted (xs @ a # ys @ b # zs @ c # us) \<Longrightarrow> x < c \<Longrightarrow>
  del_list x (xs @ a # ys @ b # zs @ c # us) = del_list x (xs @ a # ys @ b # zs) @ c # us"
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted3)

lemma del_list_sorted5:
  "sorted (xs @ a # ys @ b # zs @ c # us @ d # vs) \<Longrightarrow> x < d \<Longrightarrow>
   del_list x (xs @ a # ys @ b # zs @ c # us @ d # vs) =
   del_list x (xs @ a # ys @ b # zs @ c # us) @ d # vs" 
by (induction xs) (auto simp: sorted_Cons_iff del_list_sorted4)

lemmas del_list_simps = sorted_lems
  del_list_sorted1
  del_list_sorted2
  del_list_sorted3
  del_list_sorted4
  del_list_sorted5

end
