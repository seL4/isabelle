(* Author: Tobias Nipkow, TU Muenchen *)

section \<open>Sum and product over lists\<close>

theory Groups_List
imports List
begin

locale monoid_list = monoid
begin
 
definition F :: "'a list \<Rightarrow> 'a"
where
  eq_foldr [code]: "F xs = foldr f xs \<^bold>1"
 
lemma Nil [simp]:
  "F [] = \<^bold>1"
  by (simp add: eq_foldr)
 
lemma Cons [simp]:
  "F (x # xs) = x \<^bold>* F xs"
  by (simp add: eq_foldr)
 
lemma append [simp]:
  "F (xs @ ys) = F xs \<^bold>* F ys"
  by (induct xs) (simp_all add: assoc)
 
end

locale comm_monoid_list = comm_monoid + monoid_list
begin
 
lemma rev [simp]:
  "F (rev xs) = F xs"
  by (simp add: eq_foldr foldr_fold  fold_rev fun_eq_iff assoc left_commute)
 
end
 
locale comm_monoid_list_set = list: comm_monoid_list + set: comm_monoid_set
begin

lemma distinct_set_conv_list:
  "distinct xs \<Longrightarrow> set.F g (set xs) = list.F (map g xs)"
  by (induct xs) simp_all

lemma set_conv_list [code]:
  "set.F g (set xs) = list.F (map g (remdups xs))"
  by (simp add: distinct_set_conv_list [symmetric])

end


subsection \<open>List summation\<close>

context monoid_add
begin

sublocale sum_list: monoid_list plus 0
defines
  sum_list = sum_list.F ..
 
end

context comm_monoid_add
begin

sublocale sum_list: comm_monoid_list plus 0
rewrites
  "monoid_list.F plus 0 = sum_list"
proof -
  show "comm_monoid_list plus 0" ..
  then interpret sum_list: comm_monoid_list plus 0 .
  from sum_list_def show "monoid_list.F plus 0 = sum_list" by simp
qed

sublocale sum: comm_monoid_list_set plus 0
rewrites
  "monoid_list.F plus 0 = sum_list"
  and "comm_monoid_set.F plus 0 = sum"
proof -
  show "comm_monoid_list_set plus 0" ..
  then interpret sum: comm_monoid_list_set plus 0 .
  from sum_list_def show "monoid_list.F plus 0 = sum_list" by simp
  from sum_def show "comm_monoid_set.F plus 0 = sum" by (auto intro: sym)
qed

end

text \<open>Some syntactic sugar for summing a function over a list:\<close>
syntax (ASCII)
  "_sum_list" :: "pttrn => 'a list => 'b => 'b"    ("(3SUM _<-_. _)" [0, 51, 10] 10)
syntax
  "_sum_list" :: "pttrn => 'a list => 'b => 'b"    ("(3\<Sum>_\<leftarrow>_. _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>x\<leftarrow>xs. b" == "CONST sum_list (CONST map (\<lambda>x. b) xs)"

text \<open>TODO duplicates\<close>
lemmas sum_list_simps = sum_list.Nil sum_list.Cons
lemmas sum_list_append = sum_list.append
lemmas sum_list_rev = sum_list.rev

lemma (in monoid_add) fold_plus_sum_list_rev:
  "fold plus xs = plus (sum_list (rev xs))"
proof
  fix x
  have "fold plus xs x = sum_list (rev xs @ [x])"
    by (simp add: foldr_conv_fold sum_list.eq_foldr)
  also have "\<dots> = sum_list (rev xs) + x"
    by simp
  finally show "fold plus xs x = sum_list (rev xs) + x"
    .
qed

lemma (in comm_monoid_add) sum_list_map_remove1:
  "x \<in> set xs \<Longrightarrow> sum_list (map f xs) = f x + sum_list (map f (remove1 x xs))"
  by (induct xs) (auto simp add: ac_simps)

lemma (in monoid_add) size_list_conv_sum_list:
  "size_list f xs = sum_list (map f xs) + size xs"
  by (induct xs) auto

lemma (in monoid_add) length_concat:
  "length (concat xss) = sum_list (map length xss)"
  by (induct xss) simp_all

lemma (in monoid_add) length_product_lists:
  "length (product_lists xss) = foldr op * (map length xss) 1"
proof (induct xss)
  case (Cons xs xss) then show ?case by (induct xs) (auto simp: length_concat o_def)
qed simp

lemma (in monoid_add) sum_list_map_filter:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> f x = 0"
  shows "sum_list (map f (filter P xs)) = sum_list (map f xs)"
  using assms by (induct xs) auto

lemma (in comm_monoid_add) distinct_sum_list_conv_Sum:
  "distinct xs \<Longrightarrow> sum_list xs = Sum (set xs)"
  by (induct xs) simp_all

lemma sum_list_upt[simp]:
  "m \<le> n \<Longrightarrow> sum_list [m..<n] = \<Sum> {m..<n}"
by(simp add: distinct_sum_list_conv_Sum)

context ordered_comm_monoid_add
begin

lemma sum_list_nonneg: "(\<And>x. x \<in> set xs \<Longrightarrow> 0 \<le> x) \<Longrightarrow> 0 \<le> sum_list xs"
by (induction xs) auto

lemma sum_list_nonpos: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<le> 0) \<Longrightarrow> sum_list xs \<le> 0"
by (induction xs) (auto simp: add_nonpos_nonpos)

lemma sum_list_nonneg_eq_0_iff:
  "(\<And>x. x \<in> set xs \<Longrightarrow> 0 \<le> x) \<Longrightarrow> sum_list xs = 0 \<longleftrightarrow> (\<forall>x\<in> set xs. x = 0)"
by (induction xs) (simp_all add: add_nonneg_eq_0_iff sum_list_nonneg)

end

context canonically_ordered_monoid_add
begin

lemma sum_list_eq_0_iff [simp]:
  "sum_list ns = 0 \<longleftrightarrow> (\<forall>n \<in> set ns. n = 0)"
by (simp add: sum_list_nonneg_eq_0_iff)

lemma member_le_sum_list:
  "x \<in> set xs \<Longrightarrow> x \<le> sum_list xs"
by (induction xs) (auto simp: add_increasing add_increasing2)

lemma elem_le_sum_list:
  "k < size ns \<Longrightarrow> ns ! k \<le> sum_list (ns)"
by (rule member_le_sum_list) simp

end

lemma (in ordered_cancel_comm_monoid_diff) sum_list_update:
  "k < size xs \<Longrightarrow> sum_list (xs[k := x]) = sum_list xs + x - xs ! k"
apply(induction xs arbitrary:k)
 apply (auto simp: add_ac split: nat.split)
apply(drule elem_le_sum_list)
by (simp add: local.add_diff_assoc local.add_increasing)

lemma (in monoid_add) sum_list_triv:
  "(\<Sum>x\<leftarrow>xs. r) = of_nat (length xs) * r"
  by (induct xs) (simp_all add: distrib_right)

lemma (in monoid_add) sum_list_0 [simp]:
  "(\<Sum>x\<leftarrow>xs. 0) = 0"
  by (induct xs) (simp_all add: distrib_right)

text\<open>For non-Abelian groups \<open>xs\<close> needs to be reversed on one side:\<close>
lemma (in ab_group_add) uminus_sum_list_map:
  "- sum_list (map f xs) = sum_list (map (uminus \<circ> f) xs)"
  by (induct xs) simp_all

lemma (in comm_monoid_add) sum_list_addf:
  "(\<Sum>x\<leftarrow>xs. f x + g x) = sum_list (map f xs) + sum_list (map g xs)"
  by (induct xs) (simp_all add: algebra_simps)

lemma (in ab_group_add) sum_list_subtractf:
  "(\<Sum>x\<leftarrow>xs. f x - g x) = sum_list (map f xs) - sum_list (map g xs)"
  by (induct xs) (simp_all add: algebra_simps)

lemma (in semiring_0) sum_list_const_mult:
  "(\<Sum>x\<leftarrow>xs. c * f x) = c * (\<Sum>x\<leftarrow>xs. f x)"
  by (induct xs) (simp_all add: algebra_simps)

lemma (in semiring_0) sum_list_mult_const:
  "(\<Sum>x\<leftarrow>xs. f x * c) = (\<Sum>x\<leftarrow>xs. f x) * c"
  by (induct xs) (simp_all add: algebra_simps)

lemma (in ordered_ab_group_add_abs) sum_list_abs:
  "\<bar>sum_list xs\<bar> \<le> sum_list (map abs xs)"
  by (induct xs) (simp_all add: order_trans [OF abs_triangle_ineq])

lemma sum_list_mono:
  fixes f g :: "'a \<Rightarrow> 'b::{monoid_add, ordered_ab_semigroup_add}"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x) \<Longrightarrow> (\<Sum>x\<leftarrow>xs. f x) \<le> (\<Sum>x\<leftarrow>xs. g x)"
  by (induct xs) (simp, simp add: add_mono)

lemma (in monoid_add) sum_list_distinct_conv_sum_set:
  "distinct xs \<Longrightarrow> sum_list (map f xs) = sum f (set xs)"
  by (induct xs) simp_all

lemma (in monoid_add) interv_sum_list_conv_sum_set_nat:
  "sum_list (map f [m..<n]) = sum f (set [m..<n])"
  by (simp add: sum_list_distinct_conv_sum_set)

lemma (in monoid_add) interv_sum_list_conv_sum_set_int:
  "sum_list (map f [k..l]) = sum f (set [k..l])"
  by (simp add: sum_list_distinct_conv_sum_set)

text \<open>General equivalence between @{const sum_list} and @{const sum}\<close>
lemma (in monoid_add) sum_list_sum_nth:
  "sum_list xs = (\<Sum> i = 0 ..< length xs. xs ! i)"
  using interv_sum_list_conv_sum_set_nat [of "op ! xs" 0 "length xs"] by (simp add: map_nth)

lemma sum_list_map_eq_sum_count:
  "sum_list (map f xs) = sum (\<lambda>x. count_list xs x * f x) (set xs)"
proof(induction xs)
  case (Cons x xs)
  show ?case (is "?l = ?r")
  proof cases
    assume "x \<in> set xs"
    have "?l = f x + (\<Sum>x\<in>set xs. count_list xs x * f x)" by (simp add: Cons.IH)
    also have "set xs = insert x (set xs - {x})" using \<open>x \<in> set xs\<close>by blast
    also have "f x + (\<Sum>x\<in>insert x (set xs - {x}). count_list xs x * f x) = ?r"
      by (simp add: sum.insert_remove eq_commute)
    finally show ?thesis .
  next
    assume "x \<notin> set xs"
    hence "\<And>xa. xa \<in> set xs \<Longrightarrow> x \<noteq> xa" by blast
    thus ?thesis by (simp add: Cons.IH \<open>x \<notin> set xs\<close>)
  qed
qed simp

lemma sum_list_map_eq_sum_count2:
assumes "set xs \<subseteq> X" "finite X"
shows "sum_list (map f xs) = sum (\<lambda>x. count_list xs x * f x) X"
proof-
  let ?F = "\<lambda>x. count_list xs x * f x"
  have "sum ?F X = sum ?F (set xs \<union> (X - set xs))"
    using Un_absorb1[OF assms(1)] by(simp)
  also have "\<dots> = sum ?F (set xs)"
    using assms(2)
    by(simp add: sum.union_disjoint[OF _ _ Diff_disjoint] del: Un_Diff_cancel)
  finally show ?thesis by(simp add:sum_list_map_eq_sum_count)
qed

lemma sum_list_nonneg: 
    "(\<And>x. x \<in> set xs \<Longrightarrow> (x :: 'a :: ordered_comm_monoid_add) \<ge> 0) \<Longrightarrow> sum_list xs \<ge> 0"
  by (induction xs) simp_all

lemma (in monoid_add) sum_list_map_filter':
  "sum_list (map f (filter P xs)) = sum_list (map (\<lambda>x. if P x then f x else 0) xs)"
  by (induction xs) simp_all

lemma sum_list_cong [fundef_cong]:
  assumes "xs = ys"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows    "sum_list (map f xs) = sum_list (map g ys)"
proof -
  from assms(2) have "sum_list (map f xs) = sum_list (map g xs)"
    by (induction xs) simp_all
  with assms(1) show ?thesis by simp
qed


subsection \<open>Further facts about @{const List.n_lists}\<close>

lemma length_n_lists: "length (List.n_lists n xs) = length xs ^ n"
  by (induct n) (auto simp add: comp_def length_concat sum_list_triv)

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


subsection \<open>Tools setup\<close>

lemmas sum_code = sum.set_conv_list

lemma sum_set_upto_conv_sum_list_int [code_unfold]:
  "sum f (set [i..j::int]) = sum_list (map f [i..j])"
  by (simp add: interv_sum_list_conv_sum_set_int)

lemma sum_set_upt_conv_sum_list_nat [code_unfold]:
  "sum f (set [m..<n]) = sum_list (map f [m..<n])"
  by (simp add: interv_sum_list_conv_sum_set_nat)

lemma sum_list_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "A 0 0"
  assumes [transfer_rule]: "(A ===> A ===> A) op + op +"
  shows "(list_all2 A ===> A) sum_list sum_list"
  unfolding sum_list.eq_foldr [abs_def]
  by transfer_prover


subsection \<open>List product\<close>

context monoid_mult
begin

sublocale prod_list: monoid_list times 1
defines
  prod_list = prod_list.F ..

end

context comm_monoid_mult
begin

sublocale prod_list: comm_monoid_list times 1
rewrites
  "monoid_list.F times 1 = prod_list"
proof -
  show "comm_monoid_list times 1" ..
  then interpret prod_list: comm_monoid_list times 1 .
  from prod_list_def show "monoid_list.F times 1 = prod_list" by simp
qed

sublocale prod: comm_monoid_list_set times 1
rewrites
  "monoid_list.F times 1 = prod_list"
  and "comm_monoid_set.F times 1 = prod"
proof -
  show "comm_monoid_list_set times 1" ..
  then interpret prod: comm_monoid_list_set times 1 .
  from prod_list_def show "monoid_list.F times 1 = prod_list" by simp
  from prod_def show "comm_monoid_set.F times 1 = prod" by (auto intro: sym)
qed

end

lemma prod_list_cong [fundef_cong]:
  assumes "xs = ys"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows    "prod_list (map f xs) = prod_list (map g ys)"
proof -
  from assms(2) have "prod_list (map f xs) = prod_list (map g xs)"
    by (induction xs) simp_all
  with assms(1) show ?thesis by simp
qed

lemma prod_list_zero_iff: 
  "prod_list xs = 0 \<longleftrightarrow> (0 :: 'a :: {semiring_no_zero_divisors, semiring_1}) \<in> set xs"
  by (induction xs) simp_all

text \<open>Some syntactic sugar:\<close>

syntax (ASCII)
  "_prod_list" :: "pttrn => 'a list => 'b => 'b"    ("(3PROD _<-_. _)" [0, 51, 10] 10)
syntax
  "_prod_list" :: "pttrn => 'a list => 'b => 'b"    ("(3\<Prod>_\<leftarrow>_. _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Prod>x\<leftarrow>xs. b" \<rightleftharpoons> "CONST prod_list (CONST map (\<lambda>x. b) xs)"

end
