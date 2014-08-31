
(* Author: Tobias Nipkow, TU Muenchen *)

header {* Summation over lists *}

theory Groups_List
imports List
begin

definition (in monoid_add) listsum :: "'a list \<Rightarrow> 'a" where
"listsum xs = foldr plus xs 0"

subsubsection {* List summation: @{const listsum} and @{text"\<Sum>"}*}

lemma (in monoid_add) listsum_simps [simp]:
  "listsum [] = 0"
  "listsum (x # xs) = x + listsum xs"
  by (simp_all add: listsum_def)

lemma (in monoid_add) listsum_append [simp]:
  "listsum (xs @ ys) = listsum xs + listsum ys"
  by (induct xs) (simp_all add: add.assoc)

lemma (in comm_monoid_add) listsum_rev [simp]:
  "listsum (rev xs) = listsum xs"
  by (simp add: listsum_def foldr_fold fold_rev fun_eq_iff add_ac)

lemma (in monoid_add) fold_plus_listsum_rev:
  "fold plus xs = plus (listsum (rev xs))"
proof
  fix x
  have "fold plus xs x = fold plus xs (x + 0)" by simp
  also have "\<dots> = fold plus (x # xs) 0" by simp
  also have "\<dots> = foldr plus (rev xs @ [x]) 0" by (simp add: foldr_conv_fold)
  also have "\<dots> = listsum (rev xs @ [x])" by (simp add: listsum_def)
  also have "\<dots> = listsum (rev xs) + listsum [x]" by simp
  finally show "fold plus xs x = listsum (rev xs) + x" by simp
qed

text{* Some syntactic sugar for summing a function over a list: *}

syntax
  "_listsum" :: "pttrn => 'a list => 'b => 'b"    ("(3SUM _<-_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_listsum" :: "pttrn => 'a list => 'b => 'b"    ("(3\<Sum>_\<leftarrow>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_listsum" :: "pttrn => 'a list => 'b => 'b"    ("(3\<Sum>_\<leftarrow>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "SUM x<-xs. b" == "CONST listsum (CONST map (%x. b) xs)"
  "\<Sum>x\<leftarrow>xs. b" == "CONST listsum (CONST map (%x. b) xs)"

lemma (in comm_monoid_add) listsum_map_remove1:
  "x \<in> set xs \<Longrightarrow> listsum (map f xs) = f x + listsum (map f (remove1 x xs))"
  by (induct xs) (auto simp add: ac_simps)

lemma (in monoid_add) size_list_conv_listsum:
  "size_list f xs = listsum (map f xs) + size xs"
  by (induct xs) auto

lemma (in monoid_add) length_concat:
  "length (concat xss) = listsum (map length xss)"
  by (induct xss) simp_all

lemma (in monoid_add) length_product_lists:
  "length (product_lists xss) = foldr op * (map length xss) 1"
proof (induct xss)
  case (Cons xs xss) then show ?case by (induct xs) (auto simp: length_concat o_def)
qed simp

lemma (in monoid_add) listsum_map_filter:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> f x = 0"
  shows "listsum (map f (filter P xs)) = listsum (map f xs)"
  using assms by (induct xs) auto

lemma (in comm_monoid_add) distinct_listsum_conv_Setsum:
  "distinct xs \<Longrightarrow> listsum xs = Setsum (set xs)"
  by (induct xs) simp_all

lemma listsum_eq_0_nat_iff_nat [simp]:
  "listsum ns = (0::nat) \<longleftrightarrow> (\<forall>n \<in> set ns. n = 0)"
  by (induct ns) simp_all

lemma member_le_listsum_nat:
  "(n :: nat) \<in> set ns \<Longrightarrow> n \<le> listsum ns"
  by (induct ns) auto

lemma elem_le_listsum_nat:
  "k < size ns \<Longrightarrow> ns ! k \<le> listsum (ns::nat list)"
  by (rule member_le_listsum_nat) simp

lemma listsum_update_nat:
  "k < size ns \<Longrightarrow> listsum (ns[k := (n::nat)]) = listsum ns + n - ns ! k"
apply(induct ns arbitrary:k)
 apply (auto split:nat.split)
apply(drule elem_le_listsum_nat)
apply arith
done

lemma (in monoid_add) listsum_triv:
  "(\<Sum>x\<leftarrow>xs. r) = of_nat (length xs) * r"
  by (induct xs) (simp_all add: distrib_right)

lemma (in monoid_add) listsum_0 [simp]:
  "(\<Sum>x\<leftarrow>xs. 0) = 0"
  by (induct xs) (simp_all add: distrib_right)

text{* For non-Abelian groups @{text xs} needs to be reversed on one side: *}
lemma (in ab_group_add) uminus_listsum_map:
  "- listsum (map f xs) = listsum (map (uminus \<circ> f) xs)"
  by (induct xs) simp_all

lemma (in comm_monoid_add) listsum_addf:
  "(\<Sum>x\<leftarrow>xs. f x + g x) = listsum (map f xs) + listsum (map g xs)"
  by (induct xs) (simp_all add: algebra_simps)

lemma (in ab_group_add) listsum_subtractf:
  "(\<Sum>x\<leftarrow>xs. f x - g x) = listsum (map f xs) - listsum (map g xs)"
  by (induct xs) (simp_all add: algebra_simps)

lemma (in semiring_0) listsum_const_mult:
  "(\<Sum>x\<leftarrow>xs. c * f x) = c * (\<Sum>x\<leftarrow>xs. f x)"
  by (induct xs) (simp_all add: algebra_simps)

lemma (in semiring_0) listsum_mult_const:
  "(\<Sum>x\<leftarrow>xs. f x * c) = (\<Sum>x\<leftarrow>xs. f x) * c"
  by (induct xs) (simp_all add: algebra_simps)

lemma (in ordered_ab_group_add_abs) listsum_abs:
  "\<bar>listsum xs\<bar> \<le> listsum (map abs xs)"
  by (induct xs) (simp_all add: order_trans [OF abs_triangle_ineq])

lemma listsum_mono:
  fixes f g :: "'a \<Rightarrow> 'b::{monoid_add, ordered_ab_semigroup_add}"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x) \<Longrightarrow> (\<Sum>x\<leftarrow>xs. f x) \<le> (\<Sum>x\<leftarrow>xs. g x)"
  by (induct xs) (simp, simp add: add_mono)

lemma (in monoid_add) listsum_distinct_conv_setsum_set:
  "distinct xs \<Longrightarrow> listsum (map f xs) = setsum f (set xs)"
  by (induct xs) simp_all

lemma (in monoid_add) interv_listsum_conv_setsum_set_nat:
  "listsum (map f [m..<n]) = setsum f (set [m..<n])"
  by (simp add: listsum_distinct_conv_setsum_set)

lemma (in monoid_add) interv_listsum_conv_setsum_set_int:
  "listsum (map f [k..l]) = setsum f (set [k..l])"
  by (simp add: listsum_distinct_conv_setsum_set)

text {* General equivalence between @{const listsum} and @{const setsum} *}
lemma (in monoid_add) listsum_setsum_nth:
  "listsum xs = (\<Sum> i = 0 ..< length xs. xs ! i)"
  using interv_listsum_conv_setsum_set_nat [of "op ! xs" 0 "length xs"] by (simp add: map_nth)


subsection {* Further facts about @{const List.n_lists} *}

lemma length_n_lists: "length (List.n_lists n xs) = length xs ^ n"
  by (induct n) (auto simp add: comp_def length_concat listsum_triv)

lemma distinct_n_lists:
  assumes "distinct xs"
  shows "distinct (List.n_lists n xs)"
proof (rule card_distinct)
  from assms have card_length: "card (set xs) = length xs" by (rule distinct_card)
  have "card (set (List.n_lists n xs)) = card (set xs) ^ n"
  proof (induct n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    moreover have "card (\<Union>ys\<in>set (List.n_lists n xs). (\<lambda>y. y # ys) ` set xs)
      = (\<Sum>ys\<in>set (List.n_lists n xs). card ((\<lambda>y. y # ys) ` set xs))"
      by (rule card_UN_disjoint) auto
    moreover have "\<And>ys. card ((\<lambda>y. y # ys) ` set xs) = card (set xs)"
      by (rule card_image) (simp add: inj_on_def)
    ultimately show ?case by auto
  qed
  also have "\<dots> = length xs ^ n" by (simp add: card_length)
  finally show "card (set (List.n_lists n xs)) = length (List.n_lists n xs)"
    by (simp add: length_n_lists)
qed


subsection {* Tools setup *}

lemma setsum_set_upto_conv_listsum_int [code_unfold]:
  "setsum f (set [i..j::int]) = listsum (map f [i..j])"
  by (simp add: interv_listsum_conv_setsum_set_int)

lemma setsum_set_upt_conv_listsum_nat [code_unfold]:
  "setsum f (set [m..<n]) = listsum (map f [m..<n])"
  by (simp add: interv_listsum_conv_setsum_set_nat)

lemma setsum_code [code]:
  "setsum f (set xs) = listsum (map f (remdups xs))"
  by (simp add: listsum_distinct_conv_setsum_set)

context
begin

interpretation lifting_syntax .

lemma listsum_transfer[transfer_rule]:
  assumes [transfer_rule]: "A 0 0"
  assumes [transfer_rule]: "(A ===> A ===> A) op + op +"
  shows "(list_all2 A ===> A) listsum listsum"
  unfolding listsum_def[abs_def]
  by transfer_prover

end

end