(*  Title:      HOL/Factorial.thy
    Author:     Jacques D. Fleuriot
    Author:     Lawrence C Paulson
    Author:     Jeremy Avigad
    Author:     Chaitanya Mangla
    Author:     Manuel Eberl
*)

section \<open>Factorial Function, Rising Factorials\<close>

theory Factorial
  imports Groups_List
begin

subsection \<open>Factorial Function\<close>

context semiring_char_0
begin

definition fact :: "nat \<Rightarrow> 'a"
  where fact_prod: "fact n = of_nat (\<Prod>{1..n})"

lemma fact_prod_Suc: "fact n = of_nat (prod Suc {0..<n})"
  unfolding fact_prod using atLeast0LessThan prod.atLeast1_atMost_eq by auto

lemma fact_prod_rev: "fact n = of_nat (\<Prod>i = 0..<n. n - i)"
proof -
  have "prod Suc {0..<n} = \<Prod>{1..n}"
    by (simp add: atLeast0LessThan prod.atLeast1_atMost_eq)
  then have "prod Suc {0..<n} = prod ((-) (n + 1)) {1..n}"
    using prod.atLeastAtMost_rev [of "\<lambda>i. i" 1 n] by presburger
  then show ?thesis
    unfolding fact_prod_Suc by (simp add: atLeast0LessThan prod.atLeast1_atMost_eq)
qed

lemma fact_0 [simp]: "fact 0 = 1"
  by (simp add: fact_prod)

lemma fact_1 [simp]: "fact 1 = 1"
  by (simp add: fact_prod)

lemma fact_Suc_0 [simp]: "fact (Suc 0) = 1"
  by (simp add: fact_prod)

lemma fact_Suc [simp]: "fact (Suc n) = of_nat (Suc n) * fact n"
  by (simp add: fact_prod atLeastAtMostSuc_conv algebra_simps)

lemma fact_2 [simp]: "fact 2 = 2"
  by (simp add: numeral_2_eq_2)

lemma fact_split: "k \<le> n \<Longrightarrow> fact n = of_nat (prod Suc {n - k..<n}) * fact (n - k)"
  by (simp add: fact_prod_Suc prod.union_disjoint [symmetric]
    ivl_disj_un ac_simps of_nat_mult [symmetric])

end

lemma of_nat_fact [simp]: "of_nat (fact n) = fact n"
  by (simp add: fact_prod)

lemma of_int_fact [simp]: "of_int (fact n) = fact n"
  by (simp only: fact_prod of_int_of_nat_eq)

lemma fact_reduce: "n > 0 \<Longrightarrow> fact n = of_nat n * fact (n - 1)"
  by (cases n) auto

lemma fact_nonzero [simp]: "fact n \<noteq> (0::'a::{semiring_char_0,semiring_no_zero_divisors})"
  apply (induct n)
  apply auto
  using of_nat_eq_0_iff
  apply fastforce
  done

lemma fact_mono_nat: "m \<le> n \<Longrightarrow> fact m \<le> (fact n :: nat)"
  by (induct n) (auto simp: le_Suc_eq)

lemma fact_in_Nats: "fact n \<in> \<nat>"
  by (induct n) auto

lemma fact_in_Ints: "fact n \<in> \<int>"
  by (induct n) auto

context
  assumes "SORT_CONSTRAINT('a::linordered_semidom)"
begin

lemma fact_mono: "m \<le> n \<Longrightarrow> fact m \<le> (fact n :: 'a)"
  by (metis of_nat_fact of_nat_le_iff fact_mono_nat)

lemma fact_ge_1 [simp]: "fact n \<ge> (1 :: 'a)"
  by (metis le0 fact_0 fact_mono)

lemma fact_gt_zero [simp]: "fact n > (0 :: 'a)"
  using fact_ge_1 less_le_trans zero_less_one by blast

lemma fact_ge_zero [simp]: "fact n \<ge> (0 :: 'a)"
  by (simp add: less_imp_le)

lemma fact_not_neg [simp]: "\<not> fact n < (0 :: 'a)"
  by (simp add: not_less_iff_gr_or_eq)

lemma fact_le_power: "fact n \<le> (of_nat (n^n) :: 'a)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have *: "fact n \<le> (of_nat (Suc n ^ n) ::'a)"
    by (rule order_trans) (simp add: power_mono del: of_nat_power)
  have "fact (Suc n) = (of_nat (Suc n) * fact n ::'a)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> of_nat (Suc n) * of_nat (Suc n ^ n)"
    by (simp add: * ordered_comm_semiring_class.comm_mult_left_mono del: of_nat_power)
  also have "\<dots> \<le> of_nat (Suc n ^ Suc n)"
    by (metis of_nat_mult order_refl power_Suc)
  finally show ?case .
qed

end

lemma fact_less_mono_nat: "0 < m \<Longrightarrow> m < n \<Longrightarrow> fact m < (fact n :: nat)"
  by (induct n) (auto simp: less_Suc_eq)

lemma fact_less_mono: "0 < m \<Longrightarrow> m < n \<Longrightarrow> fact m < (fact n :: 'a::linordered_semidom)"
  by (metis of_nat_fact of_nat_less_iff fact_less_mono_nat)

lemma fact_ge_Suc_0_nat [simp]: "fact n \<ge> Suc 0"
  by (metis One_nat_def fact_ge_1)

lemma dvd_fact: "1 \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> m dvd fact n"
  by (induct n) (auto simp: dvdI le_Suc_eq)

lemma fact_ge_self: "fact n \<ge> n"
  by (cases "n = 0") (simp_all add: dvd_imp_le dvd_fact)

lemma fact_dvd: "n \<le> m \<Longrightarrow> fact n dvd (fact m :: 'a::linordered_semidom)"
  by (induct m) (auto simp: le_Suc_eq)

lemma fact_mod: "m \<le> n \<Longrightarrow> fact n mod (fact m :: 'a::{semidom_modulo, linordered_semidom}) = 0"
  by (simp add: mod_eq_0_iff_dvd fact_dvd)

lemma fact_div_fact:
  assumes "m \<ge> n"
  shows "fact m div fact n = \<Prod>{n + 1..m}"
proof -
  obtain d where "d = m - n"
    by auto
  with assms have "m = n + d"
    by auto
  have "fact (n + d) div (fact n) = \<Prod>{n + 1..n + d}"
  proof (induct d)
    case 0
    show ?case by simp
  next
    case (Suc d')
    have "fact (n + Suc d') div fact n = Suc (n + d') * fact (n + d') div fact n"
      by simp
    also from Suc.hyps have "\<dots> = Suc (n + d') * \<Prod>{n + 1..n + d'}"
      unfolding div_mult1_eq[of _ "fact (n + d')"] by (simp add: fact_mod)
    also have "\<dots> = \<Prod>{n + 1..n + Suc d'}"
      by (simp add: atLeastAtMostSuc_conv)
    finally show ?case .
  qed
  with \<open>m = n + d\<close> show ?thesis by simp
qed

lemma fact_num_eq_if: "fact m = (if m = 0 then 1 else of_nat m * fact (m - 1))"
  by (cases m) auto

lemma fact_div_fact_le_pow:
  assumes "r \<le> n"
  shows "fact n div fact (n - r) \<le> n ^ r"
proof -
  have "r \<le> n \<Longrightarrow> \<Prod>{n - r..n} = (n - r) * \<Prod>{Suc (n - r)..n}" for r
    by (subst prod.insert[symmetric]) (auto simp: atLeastAtMost_insertL)
  with assms show ?thesis
    by (induct r rule: nat.induct) (auto simp add: fact_div_fact Suc_diff_Suc mult_le_mono)
qed

lemma prod_Suc_fact: "prod Suc {0..<n} = fact n"
  by (simp add: fact_prod_Suc)

lemma prod_Suc_Suc_fact: "prod Suc {Suc 0..<n} = fact n"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "prod Suc {Suc 0..<n} = Suc 0 * prod Suc {Suc 0..<n}"
    by simp
  also have "\<dots> = prod Suc (insert 0 {Suc 0..<n})"
    by simp
  also have "insert 0 {Suc 0..<n} = {0..<n}"
    using False by auto
  finally show ?thesis
    by (simp add: fact_prod_Suc)
qed

lemma fact_numeral: "fact (numeral k) = numeral k * fact (pred_numeral k)"
  \<comment> \<open>Evaluation for specific numerals\<close>
  by (metis fact_Suc numeral_eq_Suc of_nat_numeral)


subsection \<open>Pochhammer's symbol: generalized rising factorial\<close>

text \<open>See \<^url>\<open>https://en.wikipedia.org/wiki/Pochhammer_symbol\<close>.\<close>

context comm_semiring_1
begin

definition pochhammer :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
  where pochhammer_prod: "pochhammer a n = prod (\<lambda>i. a + of_nat i) {0..<n}"

lemma pochhammer_prod_rev: "pochhammer a n = prod (\<lambda>i. a + of_nat (n - i)) {1..n}"
  using prod.atLeastLessThan_rev_at_least_Suc_atMost [of "\<lambda>i. a + of_nat i" 0 n]
  by (simp add: pochhammer_prod)

lemma pochhammer_Suc_prod: "pochhammer a (Suc n) = prod (\<lambda>i. a + of_nat i) {0..n}"
  by (simp add: pochhammer_prod atLeastLessThanSuc_atLeastAtMost)

lemma pochhammer_Suc_prod_rev: "pochhammer a (Suc n) = prod (\<lambda>i. a + of_nat (n - i)) {0..n}"
  using prod.atLeast_Suc_atMost_Suc_shift
  by (simp add: pochhammer_prod_rev prod.atLeast_Suc_atMost_Suc_shift del: prod.cl_ivl_Suc)

lemma pochhammer_0 [simp]: "pochhammer a 0 = 1"
  by (simp add: pochhammer_prod)

lemma pochhammer_1 [simp]: "pochhammer a 1 = a"
  by (simp add: pochhammer_prod lessThan_Suc)

lemma pochhammer_Suc0 [simp]: "pochhammer a (Suc 0) = a"
  by (simp add: pochhammer_prod lessThan_Suc)

lemma pochhammer_Suc: "pochhammer a (Suc n) = pochhammer a n * (a + of_nat n)"
  by (simp add: pochhammer_prod atLeast0_lessThan_Suc ac_simps)

end

lemma pochhammer_nonneg:
  fixes x :: "'a :: linordered_semidom"
  shows "x > 0 \<Longrightarrow> pochhammer x n \<ge> 0"
  by (induction n) (auto simp: pochhammer_Suc intro!: mult_nonneg_nonneg add_nonneg_nonneg)

lemma pochhammer_pos:
  fixes x :: "'a :: linordered_semidom"
  shows "x > 0 \<Longrightarrow> pochhammer x n > 0"
  by (induction n) (auto simp: pochhammer_Suc intro!: mult_pos_pos add_pos_nonneg)

context comm_semiring_1
begin

lemma pochhammer_of_nat: "pochhammer (of_nat x) n = of_nat (pochhammer x n)"
  by (simp add: pochhammer_prod Factorial.pochhammer_prod)

end

context comm_ring_1
begin

lemma pochhammer_of_int: "pochhammer (of_int x) n = of_int (pochhammer x n)"
  by (simp add: pochhammer_prod Factorial.pochhammer_prod)

end

lemma pochhammer_rec: "pochhammer a (Suc n) = a * pochhammer (a + 1) n"
  by (simp add: pochhammer_prod prod.atLeast0_lessThan_Suc_shift ac_simps del: prod.op_ivl_Suc)

lemma pochhammer_rec': "pochhammer z (Suc n) = (z + of_nat n) * pochhammer z n"
  by (simp add: pochhammer_prod prod.atLeast0_lessThan_Suc ac_simps)

lemma pochhammer_fact: "fact n = pochhammer 1 n"
  by (simp add: pochhammer_prod fact_prod_Suc)

lemma pochhammer_of_nat_eq_0_lemma: "k > n \<Longrightarrow> pochhammer (- (of_nat n :: 'a:: idom)) k = 0"
  by (auto simp add: pochhammer_prod)

lemma pochhammer_of_nat_eq_0_lemma':
  assumes kn: "k \<le> n"
  shows "pochhammer (- (of_nat n :: 'a::{idom,ring_char_0})) k \<noteq> 0"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  then show ?thesis
    apply (simp add: pochhammer_Suc_prod)
    using Suc kn
    apply (auto simp add: algebra_simps)
    done
qed

lemma pochhammer_of_nat_eq_0_iff:
  "pochhammer (- (of_nat n :: 'a::{idom,ring_char_0})) k = 0 \<longleftrightarrow> k > n"
  (is "?l = ?r")
  using pochhammer_of_nat_eq_0_lemma[of n k, where ?'a='a]
    pochhammer_of_nat_eq_0_lemma'[of k n, where ?'a = 'a]
  by (auto simp add: not_le[symmetric])

lemma pochhammer_0_left:
  "pochhammer 0 n = (if n = 0 then 1 else 0)"
  by (induction n) (simp_all add: pochhammer_rec)

lemma pochhammer_eq_0_iff: "pochhammer a n = (0::'a::field_char_0) \<longleftrightarrow> (\<exists>k < n. a = - of_nat k)"
  by (auto simp add: pochhammer_prod eq_neg_iff_add_eq_0)

lemma pochhammer_eq_0_mono:
  "pochhammer a n = (0::'a::field_char_0) \<Longrightarrow> m \<ge> n \<Longrightarrow> pochhammer a m = 0"
  unfolding pochhammer_eq_0_iff by auto

lemma pochhammer_neq_0_mono:
  "pochhammer a m \<noteq> (0::'a::field_char_0) \<Longrightarrow> m \<ge> n \<Longrightarrow> pochhammer a n \<noteq> 0"
  unfolding pochhammer_eq_0_iff by auto

lemma pochhammer_minus:
  "pochhammer (- b) k = ((- 1) ^ k :: 'a::comm_ring_1) * pochhammer (b - of_nat k + 1) k"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have eq: "((- 1) ^ Suc h :: 'a) = (\<Prod>i = 0..h. - 1)"
    using prod_constant [where A="{0.. h}" and y="- 1 :: 'a"]
    by auto
  with Suc show ?thesis
    using pochhammer_Suc_prod_rev [of "b - of_nat k + 1"] 
    by (auto simp add: pochhammer_Suc_prod prod.distrib [symmetric] eq of_nat_diff simp del: prod_constant)
qed

lemma pochhammer_minus':
  "pochhammer (b - of_nat k + 1) k = ((- 1) ^ k :: 'a::comm_ring_1) * pochhammer (- b) k"
  by (simp add: pochhammer_minus)

lemma pochhammer_same: "pochhammer (- of_nat n) n =
    ((- 1) ^ n :: 'a::{semiring_char_0,comm_ring_1,semiring_no_zero_divisors}) * fact n"
  unfolding pochhammer_minus
  by (simp add: of_nat_diff pochhammer_fact)

lemma pochhammer_product': "pochhammer z (n + m) = pochhammer z n * pochhammer (z + of_nat n) m"
proof (induct n arbitrary: z)
  case 0
  then show ?case by simp
next
  case (Suc n z)
  have "pochhammer z (Suc n) * pochhammer (z + of_nat (Suc n)) m =
      z * (pochhammer (z + 1) n * pochhammer (z + 1 + of_nat n) m)"
    by (simp add: pochhammer_rec ac_simps)
  also note Suc[symmetric]
  also have "z * pochhammer (z + 1) (n + m) = pochhammer z (Suc (n + m))"
    by (subst pochhammer_rec) simp
  finally show ?case
    by simp
qed

lemma pochhammer_product:
  "m \<le> n \<Longrightarrow> pochhammer z n = pochhammer z m * pochhammer (z + of_nat m) (n - m)"
  using pochhammer_product'[of z m "n - m"] by simp

lemma pochhammer_times_pochhammer_half:
  fixes z :: "'a::field_char_0"
  shows "pochhammer z (Suc n) * pochhammer (z + 1/2) (Suc n) = (\<Prod>k=0..2*n+1. z + of_nat k / 2)"
proof (induct n)
  case 0
  then show ?case
    by (simp add: atLeast0_atMost_Suc)
next
  case (Suc n)
  define n' where "n' = Suc n"
  have "pochhammer z (Suc n') * pochhammer (z + 1 / 2) (Suc n') =
      (pochhammer z n' * pochhammer (z + 1 / 2) n') * ((z + of_nat n') * (z + 1/2 + of_nat n'))"
    (is "_ = _ * ?A")
    by (simp_all add: pochhammer_rec' mult_ac)
  also have "?A = (z + of_nat (Suc (2 * n + 1)) / 2) * (z + of_nat (Suc (Suc (2 * n + 1))) / 2)"
    (is "_ = ?B")
    by (simp add: field_simps n'_def)
  also note Suc[folded n'_def]
  also have "(\<Prod>k=0..2 * n + 1. z + of_nat k / 2) * ?B = (\<Prod>k=0..2 * Suc n + 1. z + of_nat k / 2)"
    by (simp add: atLeast0_atMost_Suc)
  finally show ?case
    by (simp add: n'_def)
qed

lemma pochhammer_double:
  fixes z :: "'a::field_char_0"
  shows "pochhammer (2 * z) (2 * n) = of_nat (2^(2*n)) * pochhammer z n * pochhammer (z+1/2) n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "pochhammer (2 * z) (2 * (Suc n)) = pochhammer (2 * z) (2 * n) *
      (2 * (z + of_nat n)) * (2 * (z + of_nat n) + 1)"
    by (simp add: pochhammer_rec' ac_simps)
  also note Suc
  also have "of_nat (2 ^ (2 * n)) * pochhammer z n * pochhammer (z + 1/2) n *
        (2 * (z + of_nat n)) * (2 * (z + of_nat n) + 1) =
      of_nat (2 ^ (2 * (Suc n))) * pochhammer z (Suc n) * pochhammer (z + 1/2) (Suc n)"
    by (simp add: field_simps pochhammer_rec')
  finally show ?case .
qed

lemma fact_double:
  "fact (2 * n) = (2 ^ (2 * n) * pochhammer (1 / 2) n * fact n :: 'a::field_char_0)"
  using pochhammer_double[of "1/2::'a" n] by (simp add: pochhammer_fact)

lemma pochhammer_absorb_comp: "(r - of_nat k) * pochhammer (- r) k = r * pochhammer (-r + 1) k"
  (is "?lhs = ?rhs")
  for r :: "'a::comm_ring_1"
proof -
  have "?lhs = - pochhammer (- r) (Suc k)"
    by (subst pochhammer_rec') (simp add: algebra_simps)
  also have "\<dots> = ?rhs"
    by (subst pochhammer_rec) simp
  finally show ?thesis .
qed


subsection \<open>Misc\<close>

lemma fact_code [code]:
  "fact n = (of_nat (fold_atLeastAtMost_nat ((*)) 2 n 1) :: 'a::semiring_char_0)"
proof -
  have "fact n = (of_nat (\<Prod>{1..n}) :: 'a)"
    by (simp add: fact_prod)
  also have "\<Prod>{1..n} = \<Prod>{2..n}"
    by (intro prod.mono_neutral_right) auto
  also have "\<dots> = fold_atLeastAtMost_nat ((*)) 2 n 1"
    by (simp add: prod_atLeastAtMost_code)
  finally show ?thesis .
qed

lemma pochhammer_code [code]:
  "pochhammer a n =
    (if n = 0 then 1
     else fold_atLeastAtMost_nat (\<lambda>n acc. (a + of_nat n) * acc) 0 (n - 1) 1)"
  by (cases n)
    (simp_all add: pochhammer_prod prod_atLeastAtMost_code [symmetric]
      atLeastLessThanSuc_atLeastAtMost)


lemma mult_less_iff1: "0 < z \<Longrightarrow> x * z < y * z \<longleftrightarrow> x < y"
  for x y z :: "'a::linordered_idom"
  by simp 

lemma mult_le_cancel_iff1: "0 < z \<Longrightarrow> x * z \<le> y * z \<longleftrightarrow> x \<le> y"
  for x y z :: "'a::linordered_idom"
  by simp

lemma mult_le_cancel_iff2: "0 < z \<Longrightarrow> z * x \<le> z * y \<longleftrightarrow> x \<le> y"
  for x y z :: "'a::linordered_idom"
  by simp 

end
