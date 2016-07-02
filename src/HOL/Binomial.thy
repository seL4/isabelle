(*  Title       : Binomial.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    Various additions by Jeremy Avigad.
    Additional binomial identities by Chaitanya Mangla and Manuel Eberl
*)

section\<open>Factorial Function, Binomial Coefficients and Binomial Theorem\<close>

theory Binomial
imports Main
begin

subsection \<open>Factorial\<close>

fun (in semiring_char_0) fact :: "nat \<Rightarrow> 'a"
  where "fact 0 = 1" | "fact (Suc n) = of_nat (Suc n) * fact n"

lemmas fact_Suc = fact.simps(2)

lemma fact_1 [simp]: "fact 1 = 1"
  by simp

lemma fact_Suc_0 [simp]: "fact (Suc 0) = Suc 0"
  by simp

lemma of_nat_fact [simp]:
  "of_nat (fact n) = fact n"
  by (induct n) (auto simp add: algebra_simps)

lemma of_int_fact [simp]:
  "of_int (fact n) = fact n"
proof -
  have "of_int (of_nat (fact n)) = fact n"
    unfolding of_int_of_nat_eq by simp
  then show ?thesis
    by simp
qed

lemma fact_reduce: "n > 0 \<Longrightarrow> fact n = of_nat n * fact (n - 1)"
  by (cases n) auto

lemma fact_nonzero [simp]: "fact n \<noteq> (0::'a::{semiring_char_0,semiring_no_zero_divisors})"
  apply (induct n)
  apply auto
  using of_nat_eq_0_iff by fastforce

lemma fact_mono_nat: "m \<le> n \<Longrightarrow> fact m \<le> (fact n :: nat)"
  by (induct n) (auto simp: le_Suc_eq)

lemma fact_in_Nats: "fact n \<in> \<nat>" by (induction n) auto

lemma fact_in_Ints: "fact n \<in> \<int>" by (induction n) auto

context
  assumes "SORT_CONSTRAINT('a::linordered_semidom)"
begin

  lemma fact_mono: "m \<le> n \<Longrightarrow> fact m \<le> (fact n :: 'a)"
    by (metis of_nat_fact of_nat_le_iff fact_mono_nat)

  lemma fact_ge_1 [simp]: "fact n \<ge> (1 :: 'a)"
    by (metis le0 fact.simps(1) fact_mono)

  lemma fact_gt_zero [simp]: "fact n > (0 :: 'a)"
    using fact_ge_1 less_le_trans zero_less_one by blast

  lemma fact_ge_zero [simp]: "fact n \<ge> (0 :: 'a)"
    by (simp add: less_imp_le)

  lemma fact_not_neg [simp]: "~ (fact n < (0 :: 'a))"
    by (simp add: not_less_iff_gr_or_eq)

  lemma fact_le_power:
      "fact n \<le> (of_nat (n^n) ::'a)"
  proof (induct n)
    case (Suc n)
    then have *: "fact n \<le> (of_nat (Suc n ^ n) ::'a)"
      by (rule order_trans) (simp add: power_mono del: of_nat_power)
    have "fact (Suc n) = (of_nat (Suc n) * fact n ::'a)"
      by (simp add: algebra_simps)
    also have "... \<le> (of_nat (Suc n) * of_nat (Suc n ^ n) ::'a)"
      by (simp add: "*" ordered_comm_semiring_class.comm_mult_left_mono del: of_nat_power)
    also have "... \<le> (of_nat (Suc n ^ Suc n) ::'a)"
      by (metis of_nat_mult order_refl power_Suc)
    finally show ?case .
  qed simp

end

text\<open>Note that @{term "fact 0 = fact 1"}\<close>
lemma fact_less_mono_nat: "\<lbrakk>0 < m; m < n\<rbrakk> \<Longrightarrow> fact m < (fact n :: nat)"
  by (induct n) (auto simp: less_Suc_eq)

lemma fact_less_mono:
  "\<lbrakk>0 < m; m < n\<rbrakk> \<Longrightarrow> fact m < (fact n :: 'a::linordered_semidom)"
  by (metis of_nat_fact of_nat_less_iff fact_less_mono_nat)

lemma fact_ge_Suc_0_nat [simp]: "fact n \<ge> Suc 0"
  by (metis One_nat_def fact_ge_1)

lemma dvd_fact:
  shows "1 \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> m dvd fact n"
  by (induct n) (auto simp: dvdI le_Suc_eq)

lemma fact_ge_self: "fact n \<ge> n"
  by (cases "n = 0") (simp_all add: dvd_imp_le dvd_fact)

lemma fact_altdef_nat: "fact n = \<Prod>{1..n}"
  by (induct n) (auto simp: atLeastAtMostSuc_conv)

lemma fact_altdef: "fact n = (\<Prod>i=1..n. of_nat i)"
  by (induct n) (auto simp: atLeastAtMostSuc_conv)

lemma fact_altdef': "fact n = of_nat (\<Prod>{1..n})"
  by (subst fact_altdef_nat [symmetric]) simp

lemma fact_dvd: "n \<le> m \<Longrightarrow> fact n dvd (fact m :: 'a :: {semiring_div,linordered_semidom})"
  by (induct m) (auto simp: le_Suc_eq)

lemma fact_mod: "m \<le> n \<Longrightarrow> fact n mod (fact m :: 'a :: {semiring_div,linordered_semidom}) = 0"
  by (auto simp add: fact_dvd)

lemma fact_div_fact:
  assumes "m \<ge> n"
  shows "(fact m) div (fact n) = \<Prod>{n + 1..m}"
proof -
  obtain d where "d = m - n" by auto
  from assms this have "m = n + d" by auto
  have "fact (n + d) div (fact n) = \<Prod>{n + 1..n + d}"
  proof (induct d)
    case 0
    show ?case by simp
  next
    case (Suc d')
    have "fact (n + Suc d') div fact n = Suc (n + d') * fact (n + d') div fact n"
      by simp
    also from Suc.hyps have "... = Suc (n + d') * \<Prod>{n + 1..n + d'}"
      unfolding div_mult1_eq[of _ "fact (n + d')"] by (simp add: fact_mod)
    also have "... = \<Prod>{n + 1..n + Suc d'}"
      by (simp add: atLeastAtMostSuc_conv)
    finally show ?case .
  qed
  from this \<open>m = n + d\<close> show ?thesis by simp
qed

lemma fact_num_eq_if:
    "fact m = (if m=0 then 1 else of_nat m * fact (m - 1))"
by (cases m) auto

lemma fact_eq_rev_setprod_nat: "fact k = (\<Prod>i<k. k - i)"
  unfolding fact_altdef_nat
  by (rule setprod.reindex_bij_witness[where i="\<lambda>i. k - i" and j="\<lambda>i. k - i"]) auto

lemma fact_div_fact_le_pow:
  assumes "r \<le> n" shows "fact n div fact (n - r) \<le> n ^ r"
proof -
  have "\<And>r. r \<le> n \<Longrightarrow> \<Prod>{n - r..n} = (n - r) * \<Prod>{Suc (n - r)..n}"
    by (subst setprod.insert[symmetric]) (auto simp: atLeastAtMost_insertL)
  with assms show ?thesis
    by (induct r rule: nat.induct) (auto simp add: fact_div_fact Suc_diff_Suc mult_le_mono)
qed

lemma fact_numeral:  \<comment>\<open>Evaluation for specific numerals\<close>
  "fact (numeral k) = (numeral k) * (fact (pred_numeral k))"
  by (metis fact.simps(2) numeral_eq_Suc of_nat_numeral)


text \<open>This development is based on the work of Andy Gordon and
  Florian Kammueller.\<close>

subsection \<open>Basic definitions and lemmas\<close>

text \<open>Combinatorial definition\<close>

definition binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infixl "choose" 65)
where
  "n choose k = card {K\<in>Pow {..<n}. card K = k}"

theorem n_subsets:
  assumes "finite A"
  shows "card {B. B \<subseteq> A \<and> card B = k} = card A choose k"
proof -
  from assms obtain f where bij: "bij_betw f {..<card A} A"
    by (blast elim: bij_betw_nat_finite)
  then have [simp]: "card (f ` C) = card C" if "C \<subseteq> {..<card A}" for C
    by (meson bij_betw_imp_inj_on bij_betw_subset card_image that)
  from bij have "bij_betw (image f) (Pow {..<card A}) (Pow A)"
    by (rule bij_betw_Pow)
  then have "inj_on (image f) (Pow {..<card A})"
    by (rule bij_betw_imp_inj_on)
  moreover have "{K. K \<subseteq> {..<card A} \<and> card K = k} \<subseteq> Pow {..<card A}"
    by auto
  ultimately have "inj_on (image f) {K. K \<subseteq> {..<card A} \<and> card K = k}"
    by (rule inj_on_subset)
  then have "card {K. K \<subseteq> {..<card A} \<and> card K = k} =
    card (image f ` {K. K \<subseteq> {..<card A} \<and> card K = k})" (is "_ = card ?C")
    by (simp add: card_image)
  also have "?C = {K. K \<subseteq> f ` {..<card A} \<and> card K = k}"
    by (auto elim!: subset_imageE)
  also have "f ` {..<card A} = A"
    by (meson bij bij_betw_def)
  finally show ?thesis
    by (simp add: binomial_def)
qed
    
text \<open>Recursive characterization\<close>

lemma binomial_n_0 [simp, code]:
  "n choose 0 = 1"
proof -
  have "{K \<in> Pow {..<n}. card K = 0} = {{}}"
    by (auto dest: subset_eq_range_finite) 
  then show ?thesis
    by (simp add: binomial_def)
qed

lemma binomial_0_Suc [simp, code]:
  "0 choose Suc k = 0"
  by (simp add: binomial_def)

lemma binomial_Suc_Suc [simp, code]:
  "Suc n choose Suc k = (n choose k) + (n choose Suc k)"
proof -
  let ?P = "\<lambda>n k. {K. K \<subseteq> {..<n} \<and> card K = k}"
  let ?Q = "?P (Suc n) (Suc k)"
  have inj: "inj_on (insert n) (?P n k)"
    by rule auto
  have disjoint: "insert n ` ?P n k \<inter> ?P n (Suc k) = {}"
    by auto
  have "?Q = {K\<in>?Q. n \<in> K} \<union> {K\<in>?Q. n \<notin> K}"
    by auto
  also have "{K\<in>?Q. n \<in> K} = insert n ` ?P n k" (is "?A = ?B")
  proof (rule set_eqI)
    fix K
    have K_finite: "finite K" if "K \<subseteq> insert n {..<n}"
      using that by (rule finite_subset) simp_all
    have Suc_card_K: "Suc (card K - Suc 0) = card K" if "n \<in> K"
      and "finite K"
    proof -
      from \<open>n \<in> K\<close> obtain L where "K = insert n L" and "n \<notin> L"
        by (blast elim: Set.set_insert)
      with that show ?thesis by (simp add: card_insert)
    qed
    show "K \<in> ?A \<longleftrightarrow> K \<in> ?B"
      by (subst in_image_insert_iff)
        (auto simp add: card_insert subset_eq_range_finite Diff_subset_conv K_finite Suc_card_K)
  qed    
  also have "{K\<in>?Q. n \<notin> K} = ?P n (Suc k)"
    by (auto simp add: lessThan_Suc)
  finally show ?thesis using inj disjoint
    by (simp add: binomial_def card_Un_disjoint card_image)
qed

lemma binomial_eq_0:
  "n < k \<Longrightarrow> n choose k = 0"
  by (auto simp add: binomial_def dest: subset_eq_range_card)

lemma zero_less_binomial: "k \<le> n \<Longrightarrow> n choose k > 0"
  by (induct n k rule: diff_induct) simp_all

lemma binomial_eq_0_iff [simp]:
  "n choose k = 0 \<longleftrightarrow> n < k"
  by (metis binomial_eq_0 less_numeral_extra(3) not_less zero_less_binomial)

lemma zero_less_binomial_iff [simp]:
  "n choose k > 0 \<longleftrightarrow> k \<le> n"
  by (metis binomial_eq_0_iff not_less0 not_less zero_less_binomial)

lemma binomial_n_n [simp]: "n choose n = 1"
  by (induct n) (simp_all add: binomial_eq_0)

lemma binomial_Suc_n [simp]: "Suc n choose n = Suc n"
  by (induct n) simp_all

lemma binomial_1 [simp]: "n choose Suc 0 = n"
  by (induct n) simp_all

lemma choose_reduce_nat:
  "0 < (n::nat) \<Longrightarrow> 0 < k \<Longrightarrow>
    (n choose k) = ((n - 1) choose (k - 1)) + ((n - 1) choose k)"
  using binomial_Suc_Suc [of "n - 1" "k - 1"] by simp

lemma Suc_times_binomial_eq:
  "Suc n * (n choose k) = (Suc n choose Suc k) * Suc k"
  apply (induct n arbitrary: k)
  apply simp apply arith
  apply (case_tac k)
   apply (auto simp add: add_mult_distrib add_mult_distrib2 le_Suc_eq binomial_eq_0)
  done

lemma binomial_le_pow2: "n choose k \<le> 2^n"
  apply (induct n arbitrary: k)
  apply (case_tac k) apply simp_all
  apply (case_tac k)
  apply auto
  apply (simp add: add_le_mono mult_2)
  done

text\<open>The absorption property\<close>
lemma Suc_times_binomial:
  "Suc k * (Suc n choose Suc k) = Suc n * (n choose k)"
  using Suc_times_binomial_eq by auto

text\<open>This is the well-known version of absorption, but it's harder to use because of the
  need to reason about division.\<close>
lemma binomial_Suc_Suc_eq_times:
    "(Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k"
  by (simp add: Suc_times_binomial_eq del: mult_Suc mult_Suc_right)

text\<open>Another version of absorption, with -1 instead of Suc.\<close>
lemma times_binomial_minus1_eq:
  "0 < k \<Longrightarrow> k * (n choose k) = n * ((n - 1) choose (k - 1))"
  using Suc_times_binomial_eq [where n = "n - 1" and k = "k - 1"]
  by (auto split add: nat_diff_split)


subsection \<open>The binomial theorem (courtesy of Tobias Nipkow):\<close>

text\<open>Avigad's version, generalized to any commutative ring\<close>
theorem binomial_ring: "(a+b::'a::{comm_ring_1,power})^n =
  (\<Sum>k=0..n. (of_nat (n choose k)) * a^k * b^(n-k))" (is "?P n")
proof (induct n)
  case 0 then show "?P 0" by simp
next
  case (Suc n)
  have decomp: "{0..n+1} = {0} Un {n+1} Un {1..n}"
    by auto
  have decomp2: "{0..n} = {0} Un {1..n}"
    by auto
  have "(a+b)^(n+1) =
      (a+b) * (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
    using Suc.hyps by simp
  also have "\<dots> = a*(\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k)) +
                   b*(\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
    by (rule distrib_right)
  also have "\<dots> = (\<Sum>k=0..n. of_nat (n choose k) * a^(k+1) * b^(n-k)) +
                  (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k+1))"
    by (auto simp add: setsum_right_distrib ac_simps)
  also have "\<dots> = (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n+1-k)) +
                  (\<Sum>k=1..n+1. of_nat (n choose (k - 1)) * a^k * b^(n+1-k))"
    by (simp add:setsum_shift_bounds_cl_Suc_ivl Suc_diff_le field_simps
        del:setsum_cl_ivl_Suc)
  also have "\<dots> = a^(n+1) + b^(n+1) +
                  (\<Sum>k=1..n. of_nat (n choose (k - 1)) * a^k * b^(n+1-k)) +
                  (\<Sum>k=1..n. of_nat (n choose k) * a^k * b^(n+1-k))"
    by (simp add: decomp2)
  also have
      "\<dots> = a^(n+1) + b^(n+1) +
            (\<Sum>k=1..n. of_nat(n+1 choose k) * a^k * b^(n+1-k))"
    by (auto simp add: field_simps setsum.distrib [symmetric] choose_reduce_nat)
  also have "\<dots> = (\<Sum>k=0..n+1. of_nat (n+1 choose k) * a^k * b^(n+1-k))"
    using decomp by (simp add: field_simps)
  finally show "?P (Suc n)" by simp
qed

text\<open>Original version for the naturals\<close>
corollary binomial: "(a+b::nat)^n = (\<Sum>k=0..n. (of_nat (n choose k)) * a^k * b^(n-k))"
    using binomial_ring [of "int a" "int b" n]
  by (simp only: of_nat_add [symmetric] of_nat_mult [symmetric] of_nat_power [symmetric]
           of_nat_setsum [symmetric]
           of_nat_eq_iff of_nat_id)

lemma binomial_fact_lemma: "k \<le> n \<Longrightarrow> fact k * fact (n - k) * (n choose k) = fact n"
proof (induct n arbitrary: k rule: nat_less_induct)
  fix n k assume H: "\<forall>m<n. \<forall>x\<le>m. fact x * fact (m - x) * (m choose x) =
                      fact m" and kn: "k \<le> n"
  let ?ths = "fact k * fact (n - k) * (n choose k) = fact n"
  { assume "n=0" then have ?ths using kn by simp }
  moreover
  { assume "k=0" then have ?ths using kn by simp }
  moreover
  { assume nk: "n=k" then have ?ths by simp }
  moreover
  { fix m h assume n: "n = Suc m" and h: "k = Suc h" and hm: "h < m"
    from n have mn: "m < n" by arith
    from hm have hm': "h \<le> m" by arith
    from hm h n kn have km: "k \<le> m" by arith
    have "m - h = Suc (m - Suc h)" using  h km hm by arith
    with km h have th0: "fact (m - h) = (m - h) * fact (m - k)"
      by simp
    from n h th0
    have "fact k * fact (n - k) * (n choose k) =
        k * (fact h * fact (m - h) * (m choose h)) +
        (m - h) * (fact k * fact (m - k) * (m choose k))"
      by (simp add: field_simps)
    also have "\<dots> = (k + (m - h)) * fact m"
      using H[rule_format, OF mn hm'] H[rule_format, OF mn km]
      by (simp add: field_simps)
    finally have ?ths using h n km by simp }
  moreover have "n=0 \<or> k = 0 \<or> k = n \<or> (\<exists>m h. n = Suc m \<and> k = Suc h \<and> h < m)"
    using kn by presburger
  ultimately show ?ths by blast
qed

lemma binomial_fact:
  assumes kn: "k \<le> n"
  shows "(of_nat (n choose k) :: 'a::field_char_0) =
         (fact n) / (fact k * fact(n - k))"
  using binomial_fact_lemma[OF kn]
  apply (simp add: field_simps)
  by (metis mult.commute of_nat_fact of_nat_mult)

lemma choose_row_sum: "(\<Sum>k=0..n. n choose k) = 2^n"
  using binomial [of 1 "1" n]
  by (simp add: numeral_2_eq_2)

lemma sum_choose_lower: "(\<Sum>k=0..n. (r+k) choose k) = Suc (r+n) choose n"
  by (induct n) auto

lemma sum_choose_upper: "(\<Sum>k=0..n. k choose m) = Suc n choose Suc m"
  by (induct n) auto

lemma choose_alternating_sum:
  "n > 0 \<Longrightarrow> (\<Sum>i\<le>n. (-1)^i * of_nat (n choose i)) = (0 :: 'a :: comm_ring_1)"
  using binomial_ring[of "-1 :: 'a" 1 n] by (simp add: atLeast0AtMost mult_of_nat_commute zero_power)

lemma choose_even_sum:
  assumes "n > 0"
  shows   "2 * (\<Sum>i\<le>n. if even i then of_nat (n choose i) else 0) = (2 ^ n :: 'a :: comm_ring_1)"
proof -
  have "2 ^ n = (\<Sum>i\<le>n. of_nat (n choose i)) + (\<Sum>i\<le>n. (-1) ^ i * of_nat (n choose i) :: 'a)"
    using choose_row_sum[of n]
    by (simp add: choose_alternating_sum assms atLeast0AtMost of_nat_setsum[symmetric])
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) + (-1) ^ i * of_nat (n choose i))"
    by (simp add: setsum.distrib)
  also have "\<dots> = 2 * (\<Sum>i\<le>n. if even i then of_nat (n choose i) else 0)"
    by (subst setsum_right_distrib, intro setsum.cong) simp_all
  finally show ?thesis ..
qed

lemma choose_odd_sum:
  assumes "n > 0"
  shows   "2 * (\<Sum>i\<le>n. if odd i then of_nat (n choose i) else 0) = (2 ^ n :: 'a :: comm_ring_1)"
proof -
  have "2 ^ n = (\<Sum>i\<le>n. of_nat (n choose i)) - (\<Sum>i\<le>n. (-1) ^ i * of_nat (n choose i) :: 'a)"
    using choose_row_sum[of n]
    by (simp add: choose_alternating_sum assms atLeast0AtMost of_nat_setsum[symmetric])
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) - (-1) ^ i * of_nat (n choose i))"
    by (simp add: setsum_subtractf)
  also have "\<dots> = 2 * (\<Sum>i\<le>n. if odd i then of_nat (n choose i) else 0)"
    by (subst setsum_right_distrib, intro setsum.cong) simp_all
  finally show ?thesis ..
qed

lemma choose_row_sum': "(\<Sum>k\<le>n. (n choose k)) = 2 ^ n"
  using choose_row_sum[of n] by (simp add: atLeast0AtMost)

lemma natsum_reverse_index:
  fixes m::nat
  shows "(\<And>k. m \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> g k = f (m + n - k)) \<Longrightarrow> (\<Sum>k=m..n. f k) = (\<Sum>k=m..n. g k)"
  by (rule setsum.reindex_bij_witness[where i="\<lambda>k. m+n-k" and j="\<lambda>k. m+n-k"]) auto

text\<open>NW diagonal sum property\<close>
lemma sum_choose_diagonal:
  assumes "m\<le>n" shows "(\<Sum>k=0..m. (n-k) choose (m-k)) = Suc n choose m"
proof -
  have "(\<Sum>k=0..m. (n-k) choose (m-k)) = (\<Sum>k=0..m. (n-m+k) choose k)"
    by (rule natsum_reverse_index) (simp add: assms)
  also have "... = Suc (n-m+m) choose m"
    by (rule sum_choose_lower)
  also have "... = Suc n choose m" using assms
    by simp
  finally show ?thesis .
qed

subsection\<open>Pochhammer's symbol : generalized rising factorial\<close>

text \<open>See @{url "http://en.wikipedia.org/wiki/Pochhammer_symbol"}\<close>

definition (in comm_semiring_1) "pochhammer (a :: 'a) n =
  (if n = 0 then 1 else setprod (\<lambda>n. a + of_nat n) {0 .. n - 1})"

lemma pochhammer_0 [simp]: "pochhammer a 0 = 1"
  by (simp add: pochhammer_def)

lemma pochhammer_1 [simp]: "pochhammer a 1 = a"
  by (simp add: pochhammer_def)

lemma pochhammer_Suc0 [simp]: "pochhammer a (Suc 0) = a"
  by (simp add: pochhammer_def)

lemma pochhammer_Suc_setprod: "pochhammer a (Suc n) = setprod (\<lambda>n. a + of_nat n) {0 .. n}"
  by (simp add: pochhammer_def)

lemma pochhammer_of_nat: "pochhammer (of_nat x) n = of_nat (pochhammer x n)"
  by (simp add: pochhammer_def)

lemma pochhammer_of_int: "pochhammer (of_int x) n = of_int (pochhammer x n)"
  by (simp add: pochhammer_def)

lemma setprod_nat_ivl_Suc: "setprod f {0 .. Suc n} = setprod f {0..n} * f (Suc n)"
proof -
  have "{0..Suc n} = {0..n} \<union> {Suc n}" by auto
  then show ?thesis by (simp add: field_simps)
qed

lemma setprod_nat_ivl_1_Suc: "setprod f {0 .. Suc n} = f 0 * setprod f {1.. Suc n}"
proof -
  have "{0..Suc n} = {0} \<union> {1 .. Suc n}" by auto
  then show ?thesis by simp
qed


lemma pochhammer_Suc: "pochhammer a (Suc n) = pochhammer a n * (a + of_nat n)"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc n)
  show ?thesis unfolding Suc pochhammer_Suc_setprod setprod_nat_ivl_Suc ..
qed

lemma pochhammer_rec: "pochhammer a (Suc n) = a * pochhammer (a + 1) n"
proof (cases "n = 0")
  case True
  then show ?thesis by (simp add: pochhammer_Suc_setprod)
next
  case False
  have *: "finite {1 .. n}" "0 \<notin> {1 .. n}" by auto
  have eq: "insert 0 {1 .. n} = {0..n}" by auto
  have **: "(\<Prod>n\<in>{1::nat..n}. a + of_nat n) = (\<Prod>n\<in>{0::nat..n - 1}. a + 1 + of_nat n)"
    apply (rule setprod.reindex_cong [where l = Suc])
    using False
    apply (auto simp add: fun_eq_iff field_simps)
    done
  show ?thesis
    apply (simp add: pochhammer_def)
    unfolding setprod.insert [OF *, unfolded eq]
    using ** apply (simp add: field_simps)
    done
qed

lemma pochhammer_rec': "pochhammer z (Suc n) = (z + of_nat n) * pochhammer z n"
proof (induction n arbitrary: z)
  case (Suc n z)
  have "pochhammer z (Suc (Suc n)) = z * pochhammer (z + 1) (Suc n)"
    by (simp add: pochhammer_rec)
  also note Suc
  also have "z * ((z + 1 + of_nat n) * pochhammer (z + 1) n) =
               (z + of_nat (Suc n)) * pochhammer z (Suc n)"
    by (simp_all add: pochhammer_rec algebra_simps)
  finally show ?case .
qed simp_all

lemma pochhammer_fact: "fact n = pochhammer 1 n"
  unfolding fact_altdef
  apply (cases n)
   apply (simp_all add: pochhammer_Suc_setprod)
  apply (rule setprod.reindex_cong [where l = Suc])
    apply (auto simp add: fun_eq_iff)
  done

lemma pochhammer_of_nat_eq_0_lemma:
  assumes "k > n"
  shows "pochhammer (- (of_nat n :: 'a:: idom)) k = 0"
proof (cases "n = 0")
  case True
  then show ?thesis
    using assms by (cases k) (simp_all add: pochhammer_rec)
next
  case False
  from assms obtain h where "k = Suc h" by (cases k) auto
  then show ?thesis
    by (simp add: pochhammer_Suc_setprod)
       (metis Suc_leI Suc_le_mono assms atLeastAtMost_iff less_eq_nat.simps(1))
qed

lemma pochhammer_of_nat_eq_0_lemma':
  assumes kn: "k \<le> n"
  shows "pochhammer (- (of_nat n :: 'a:: {idom,ring_char_0})) k \<noteq> 0"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  then show ?thesis
    apply (simp add: pochhammer_Suc_setprod)
    using Suc kn apply (auto simp add: algebra_simps)
    done
qed

lemma pochhammer_of_nat_eq_0_iff:
  shows "pochhammer (- (of_nat n :: 'a:: {idom,ring_char_0})) k = 0 \<longleftrightarrow> k > n"
  (is "?l = ?r")
  using pochhammer_of_nat_eq_0_lemma[of n k, where ?'a='a]
    pochhammer_of_nat_eq_0_lemma'[of k n, where ?'a = 'a]
  by (auto simp add: not_le[symmetric])

lemma pochhammer_eq_0_iff: "pochhammer a n = (0::'a::field_char_0) \<longleftrightarrow> (\<exists>k < n. a = - of_nat k)"
  apply (auto simp add: pochhammer_of_nat_eq_0_iff)
  apply (cases n)
   apply (auto simp add: pochhammer_def algebra_simps group_add_class.eq_neg_iff_add_eq_0)
  apply (metis leD not_less_eq)
  done

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
  have eq: "((- 1) ^ Suc h :: 'a) = (\<Prod>i=0..h. - 1)"
    using setprod_constant[where A="{0 .. h}" and y="- 1 :: 'a"]
    by auto
  show ?thesis
    unfolding Suc pochhammer_Suc_setprod eq setprod.distrib[symmetric]
    by (rule setprod.reindex_bij_witness[where i="op - h" and j="op - h"])
       (auto simp: of_nat_diff)
qed

lemma pochhammer_minus':
    "pochhammer (b - of_nat k + 1) k = ((- 1) ^ k :: 'a::comm_ring_1) * pochhammer (- b) k"
  unfolding pochhammer_minus[where b=b]
  unfolding mult.assoc[symmetric]
  unfolding power_add[symmetric]
  by simp

lemma pochhammer_same: "pochhammer (- of_nat n) n =
    ((- 1) ^ n :: 'a::{semiring_char_0,comm_ring_1,semiring_no_zero_divisors}) * (fact n)"
  unfolding pochhammer_minus
  by (simp add: of_nat_diff pochhammer_fact)

lemma pochhammer_product':
  "pochhammer z (n + m) = pochhammer z n * pochhammer (z + of_nat n) m"
proof (induction n arbitrary: z)
  case (Suc n z)
  have "pochhammer z (Suc n) * pochhammer (z + of_nat (Suc n)) m =
            z * (pochhammer (z + 1) n * pochhammer (z + 1 + of_nat n) m)"
    by (simp add: pochhammer_rec ac_simps)
  also note Suc[symmetric]
  also have "z * pochhammer (z + 1) (n + m) = pochhammer z (Suc (n + m))"
    by (subst pochhammer_rec) simp
  finally show ?case by simp
qed simp

lemma pochhammer_product:
  "m \<le> n \<Longrightarrow> pochhammer z n = pochhammer z m * pochhammer (z + of_nat m) (n - m)"
  using pochhammer_product'[of z m "n - m"] by simp

lemma pochhammer_times_pochhammer_half:
  fixes z :: "'a :: field_char_0"
  shows "pochhammer z (Suc n) * pochhammer (z + 1/2) (Suc n) = (\<Prod>k=0..2*n+1. z + of_nat k / 2)"
proof (induction n)
  case (Suc n)
  define n' where "n' = Suc n"
  have "pochhammer z (Suc n') * pochhammer (z + 1 / 2) (Suc n') =
          (pochhammer z n' * pochhammer (z + 1 / 2) n') *
          ((z + of_nat n') * (z + 1/2 + of_nat n'))" (is "_ = _ * ?A")
     by (simp_all add: pochhammer_rec' mult_ac)
  also have "?A = (z + of_nat (Suc (2 * n + 1)) / 2) * (z + of_nat (Suc (Suc (2 * n + 1))) / 2)"
    (is "_ = ?A") by (simp add: field_simps n'_def)
  also note Suc[folded n'_def]
  also have "(\<Prod>k = 0..2 * n + 1. z + of_nat k / 2) * ?A = (\<Prod>k = 0..2 * Suc n + 1. z + of_nat k / 2)"
    by (simp add: setprod_nat_ivl_Suc)
  finally show ?case by (simp add: n'_def)
qed (simp add: setprod_nat_ivl_Suc)

lemma pochhammer_double:
  fixes z :: "'a :: field_char_0"
  shows "pochhammer (2 * z) (2 * n) = of_nat (2^(2*n)) * pochhammer z n * pochhammer (z+1/2) n"
proof (induction n)
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
qed simp

lemma fact_double:
  "fact (2 * n) = (2 ^ (2 * n) * pochhammer (1 / 2) n * fact n :: 'a :: field_char_0)"
  using pochhammer_double[of "1/2::'a" n] by (simp add: pochhammer_fact)

lemma pochhammer_absorb_comp:
  "((r :: 'a :: comm_ring_1) - of_nat k) * pochhammer (- r) k = r * pochhammer (-r + 1) k"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = -pochhammer (-r) (Suc k)" by (subst pochhammer_rec') (simp add: algebra_simps)
  also have "\<dots> = ?rhs" by (subst pochhammer_rec) simp
  finally show ?thesis .
qed


subsection\<open>Generalized binomial coefficients\<close>

definition (in field_char_0) gbinomial :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixl "gchoose" 65)
  where "a gchoose n =
    (if n = 0 then 1 else (setprod (\<lambda>i. a - of_nat i) {0 .. n - 1}) / (fact n))"

lemma gbinomial_0 [simp]: "a gchoose 0 = 1" "0 gchoose (Suc n) = 0"
  by (simp_all add: gbinomial_def)

lemma gbinomial_pochhammer: "a gchoose n = (- 1) ^ n * pochhammer (- a) n / (fact n)"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have eq: "(- 1) ^ n = (\<Prod>i = 0..n - 1. - 1)"
    by (auto simp add: setprod_constant)
  from False show ?thesis
    by (simp add: pochhammer_def gbinomial_def field_simps
      eq setprod.distrib[symmetric])
qed

lemma gbinomial_pochhammer':
  "(s :: 'a :: field_char_0) gchoose n = pochhammer (s - of_nat n + 1) n / fact n"
proof -
  have "s gchoose n = ((-1)^n * (-1)^n) * pochhammer (s - of_nat n + 1) n / fact n"
    by (simp add: gbinomial_pochhammer pochhammer_minus mult_ac)
  also have "(-1 :: 'a)^n * (-1)^n = 1" by (subst power_add [symmetric]) simp
  finally show ?thesis by simp
qed

lemma binomial_gbinomial:
    "of_nat (n choose k) = (of_nat n gchoose k :: 'a::field_char_0)"
proof -
  { assume kn: "k > n"
    then have ?thesis
      by (subst binomial_eq_0[OF kn])
         (simp add: gbinomial_pochhammer field_simps  pochhammer_of_nat_eq_0_iff) }
  moreover
  { assume "k=0" then have ?thesis by simp }
  moreover
  { assume kn: "k \<le> n" and k0: "k\<noteq> 0"
    from k0 obtain h where h: "k = Suc h" by (cases k) auto
    from h
    have eq:"(- 1 :: 'a) ^ k = setprod (\<lambda>i. - 1) {0..h}"
      by (subst setprod_constant) auto
    have eq': "(\<Prod>i\<in>{0..h}. of_nat n + - (of_nat i :: 'a)) = (\<Prod>i\<in>{n - h..n}. of_nat i)"
        using h kn
      by (intro setprod.reindex_bij_witness[where i="op - n" and j="op - n"])
         (auto simp: of_nat_diff)
    have th0: "finite {1..n - Suc h}" "finite {n - h .. n}"
        "{1..n - Suc h} \<inter> {n - h .. n} = {}" and
        eq3: "{1..n - Suc h} \<union> {n - h .. n} = {1..n}"
      using h kn by auto
    from eq[symmetric]
    have ?thesis using kn
      apply (simp add: binomial_fact[OF kn, where ?'a = 'a]
        gbinomial_pochhammer field_simps pochhammer_Suc_setprod)
      apply (simp add: pochhammer_Suc_setprod fact_altdef h
        setprod.distrib[symmetric] eq' del: One_nat_def power_Suc)
      unfolding setprod.union_disjoint[OF th0, unfolded eq3, of "of_nat:: nat \<Rightarrow> 'a"] eq[unfolded h]
      unfolding mult.assoc
      unfolding setprod.distrib[symmetric]
      apply simp
      apply (intro setprod.reindex_bij_witness[where i="op - n" and j="op - n"])
      apply (auto simp: of_nat_diff)
      done
  }
  moreover
  have "k > n \<or> k = 0 \<or> (k \<le> n \<and> k \<noteq> 0)" by arith
  ultimately show ?thesis by blast
qed

lemma gbinomial_1[simp]: "a gchoose 1 = a"
  by (simp add: gbinomial_def)

lemma gbinomial_Suc0[simp]: "a gchoose (Suc 0) = a"
  by (simp add: gbinomial_def)

lemma gbinomial_mult_1:
  fixes a :: "'a :: field_char_0"
  shows "a * (a gchoose n) =
    of_nat n * (a gchoose n) + of_nat (Suc n) * (a gchoose (Suc n))"  (is "?l = ?r")
proof -
  have "?r = ((- 1) ^n * pochhammer (- a) n / (fact n)) * (of_nat n - (- a + of_nat n))"
    unfolding gbinomial_pochhammer
      pochhammer_Suc right_diff_distrib power_Suc
    apply (simp del: of_nat_Suc fact.simps)
    apply (auto simp add: field_simps simp del: of_nat_Suc)
    done
  also have "\<dots> = ?l" unfolding gbinomial_pochhammer
    by (simp add: field_simps)
  finally show ?thesis ..
qed

lemma gbinomial_mult_1':
  fixes a :: "'a :: field_char_0"
  shows "(a gchoose n) * a = of_nat n * (a gchoose n) + of_nat (Suc n) * (a gchoose (Suc n))"
  by (simp add: mult.commute gbinomial_mult_1)

lemma gbinomial_Suc:
    "a gchoose (Suc k) = (setprod (\<lambda>i. a - of_nat i) {0 .. k}) / (fact (Suc k))"
  by (simp add: gbinomial_def)

lemma gbinomial_mult_fact:
  fixes a :: "'a::field_char_0"
  shows
   "fact (Suc k) * (a gchoose (Suc k)) =
    (setprod (\<lambda>i. a - of_nat i) {0 .. k})"
  by (simp_all add: gbinomial_Suc field_simps del: fact.simps)

lemma gbinomial_mult_fact':
  fixes a :: "'a::field_char_0"
  shows "(a gchoose (Suc k)) * fact (Suc k) = (setprod (\<lambda>i. a - of_nat i) {0 .. k})"
  using gbinomial_mult_fact[of k a]
  by (subst mult.commute)

lemma gbinomial_Suc_Suc:
  fixes a :: "'a :: field_char_0"
  shows "(a + 1) gchoose (Suc k) = a gchoose k + (a gchoose (Suc k))"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have eq0: "(\<Prod>i\<in>{1..k}. (a + 1) - of_nat i) = (\<Prod>i\<in>{0..h}. a - of_nat i)"
    apply (rule setprod.reindex_cong [where l = Suc])
      using Suc
      apply auto
    done
  have "fact (Suc k) * (a gchoose k + (a gchoose (Suc k))) =
        (a gchoose Suc h) * (fact (Suc (Suc h))) +
        (a gchoose Suc (Suc h)) * (fact (Suc (Suc h)))"
    by (simp add: Suc field_simps del: fact.simps)
  also have "... = (a gchoose Suc h) * of_nat (Suc (Suc h) * fact (Suc h)) +
                   (\<Prod>i = 0..Suc h. a - of_nat i)"
    by (metis fact.simps(2) gbinomial_mult_fact' of_nat_fact of_nat_id)
  also have "... = (fact (Suc h) * (a gchoose Suc h)) * of_nat (Suc (Suc h)) +
                   (\<Prod>i = 0..Suc h. a - of_nat i)"
    by (simp only: fact.simps(2) mult.commute mult.left_commute of_nat_fact of_nat_id of_nat_mult)
  also have "... =  of_nat (Suc (Suc h)) * (\<Prod>i = 0..h. a - of_nat i) +
                    (\<Prod>i = 0..Suc h. a - of_nat i)"
    by (metis gbinomial_mult_fact mult.commute)
  also have "... = (\<Prod>i = 0..Suc h. a - of_nat i) +
                   (of_nat h * (\<Prod>i = 0..h. a - of_nat i) + 2 * (\<Prod>i = 0..h. a - of_nat i))"
    by (simp add: field_simps)
  also have "... =
    ((a gchoose Suc h) * (fact (Suc h)) * of_nat (Suc k)) + (\<Prod>i\<in>{0::nat..Suc h}. a - of_nat i)"
    unfolding gbinomial_mult_fact'
    by (simp add: comm_semiring_class.distrib field_simps Suc)
  also have "\<dots> = (\<Prod>i\<in>{0..h}. a - of_nat i) * (a + 1)"
    unfolding gbinomial_mult_fact' setprod_nat_ivl_Suc
    by (simp add: field_simps Suc)
  also have "\<dots> = (\<Prod>i\<in>{0..k}. (a + 1) - of_nat i)"
    using eq0
    by (simp add: Suc setprod_nat_ivl_1_Suc)
  also have "\<dots> = (fact (Suc k)) * ((a + 1) gchoose (Suc k))"
    unfolding gbinomial_mult_fact ..
  finally show ?thesis
    by (metis fact_nonzero mult_cancel_left)
qed

lemma gbinomial_reduce_nat:
  fixes a :: "'a :: field_char_0"
  shows "0 < k \<Longrightarrow> a gchoose k = (a - 1) gchoose (k - 1) + ((a - 1) gchoose k)"
  by (metis Suc_pred' diff_add_cancel gbinomial_Suc_Suc)

lemma gchoose_row_sum_weighted:
  fixes r :: "'a::field_char_0"
  shows "(\<Sum>k = 0..m. (r gchoose k) * (r/2 - of_nat k)) = of_nat(Suc m) / 2 * (r gchoose (Suc m))"
proof (induct m)
  case 0 show ?case by simp
next
  case (Suc m)
  from Suc show ?case
    by (simp add: field_simps distrib gbinomial_mult_1)
qed

lemma binomial_symmetric:
  assumes kn: "k \<le> n"
  shows "n choose k = n choose (n - k)"
proof-
  from kn have kn': "n - k \<le> n" by arith
  from binomial_fact_lemma[OF kn] binomial_fact_lemma[OF kn']
  have "fact k * fact (n - k) * (n choose k) =
    fact (n - k) * fact (n - (n - k)) * (n choose (n - k))" by simp
  then show ?thesis using kn by simp
qed

lemma choose_rising_sum:
  "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose (n + 1))"
  "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose m)"
proof -
  show "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose (n + 1))" by (induction m) simp_all
  also have "... = ((n + m + 1) choose m)" by (subst binomial_symmetric) simp_all
  finally show "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose m)" .
qed

lemma choose_linear_sum:
  "(\<Sum>i\<le>n. i * (n choose i)) = n * 2 ^ (n - 1)"
proof (cases n)
  case (Suc m)
  have "(\<Sum>i\<le>n. i * (n choose i)) = (\<Sum>i\<le>Suc m. i * (Suc m choose i))" by (simp add: Suc)
  also have "... = Suc m * 2 ^ m"
    by (simp only: setsum_atMost_Suc_shift Suc_times_binomial setsum_right_distrib[symmetric])
       (simp add: choose_row_sum')
  finally show ?thesis using Suc by simp
qed simp_all

lemma choose_alternating_linear_sum:
  assumes "n \<noteq> 1"
  shows   "(\<Sum>i\<le>n. (-1)^i * of_nat i * of_nat (n choose i) :: 'a :: comm_ring_1) = 0"
proof (cases n)
  case (Suc m)
  with assms have "m > 0" by simp
  have "(\<Sum>i\<le>n. (-1) ^ i * of_nat i * of_nat (n choose i) :: 'a) =
            (\<Sum>i\<le>Suc m. (-1) ^ i * of_nat i * of_nat (Suc m choose i))" by (simp add: Suc)
  also have "... = (\<Sum>i\<le>m. (-1) ^ (Suc i) * of_nat (Suc i * (Suc m choose Suc i)))"
    by (simp only: setsum_atMost_Suc_shift setsum_right_distrib[symmetric] mult_ac of_nat_mult) simp
  also have "... = -of_nat (Suc m) * (\<Sum>i\<le>m. (-1) ^ i * of_nat ((m choose i)))"
    by (subst setsum_right_distrib, rule setsum.cong[OF refl], subst Suc_times_binomial)
       (simp add: algebra_simps)
  also have "(\<Sum>i\<le>m. (-1 :: 'a) ^ i * of_nat ((m choose i))) = 0"
    using choose_alternating_sum[OF \<open>m > 0\<close>] by simp
  finally show ?thesis by simp
qed simp

lemma vandermonde:
  "(\<Sum>k\<le>r. (m choose k) * (n choose (r - k))) = (m + n) choose r"
proof (induction n arbitrary: r)
  case 0
  have "(\<Sum>k\<le>r. (m choose k) * (0 choose (r - k))) = (\<Sum>k\<le>r. if k = r then (m choose k) else 0)"
    by (intro setsum.cong) simp_all
  also have "... = m choose r" by (simp add: setsum.delta)
  finally show ?case by simp
next
  case (Suc n r)
  show ?case by (cases r) (simp_all add: Suc [symmetric] algebra_simps setsum.distrib Suc_diff_le)
qed

lemma choose_square_sum:
  "(\<Sum>k\<le>n. (n choose k)^2) = ((2*n) choose n)"
  using vandermonde[of n n n] by (simp add: power2_eq_square mult_2 binomial_symmetric [symmetric])

lemma pochhammer_binomial_sum:
  fixes a b :: "'a :: comm_ring_1"
  shows "pochhammer (a + b) n = (\<Sum>k\<le>n. of_nat (n choose k) * pochhammer a k * pochhammer b (n - k))"
proof (induction n arbitrary: a b)
  case (Suc n a b)
  have "(\<Sum>k\<le>Suc n. of_nat (Suc n choose k) * pochhammer a k * pochhammer b (Suc n - k)) =
            (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a (Suc i) * pochhammer b (n - i)) +
            ((\<Sum>i\<le>n. of_nat (n choose Suc i) * pochhammer a (Suc i) * pochhammer b (n - i)) +
            pochhammer b (Suc n))"
    by (subst setsum_atMost_Suc_shift) (simp add: ring_distribs setsum.distrib)
  also have "(\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a (Suc i) * pochhammer b (n - i)) =
               a * pochhammer ((a + 1) + b) n"
    by (subst Suc) (simp add: setsum_right_distrib pochhammer_rec mult_ac)
  also have "(\<Sum>i\<le>n. of_nat (n choose Suc i) * pochhammer a (Suc i) * pochhammer b (n - i)) + pochhammer b (Suc n) =
               (\<Sum>i=0..Suc n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc n - i))"
    by (subst setsum_head_Suc, simp, subst setsum_shift_bounds_cl_Suc_ivl) (simp add: atLeast0AtMost)
  also have "... = (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc n - i))"
    using Suc by (intro setsum.mono_neutral_right) (auto simp: not_le binomial_eq_0)
  also have "... = (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc (n - i)))"
    by (intro setsum.cong) (simp_all add: Suc_diff_le)
  also have "... = b * pochhammer (a + (b + 1)) n"
    by (subst Suc) (simp add: setsum_right_distrib mult_ac pochhammer_rec)
  also have "a * pochhammer ((a + 1) + b) n + b * pochhammer (a + (b + 1)) n =
               pochhammer (a + b) (Suc n)" by (simp add: pochhammer_rec algebra_simps)
  finally show ?case ..
qed simp_all


text\<open>Contributed by Manuel Eberl, generalised by LCP.
  Alternative definition of the binomial coefficient as @{term "\<Prod>i<k. (n - i) / (k - i)"}\<close>
lemma gbinomial_altdef_of_nat:
  fixes k :: nat
    and x :: "'a :: {field_char_0,field}"
  shows "x gchoose k = (\<Prod>i<k. (x - of_nat i) / of_nat (k - i) :: 'a)"
proof -
  have "(x gchoose k) = (\<Prod>i<k. x - of_nat i) / of_nat (fact k)"
    unfolding gbinomial_def
    by (auto simp: gr0_conv_Suc lessThan_Suc_atMost atLeast0AtMost)
  also have "\<dots> = (\<Prod>i<k. (x - of_nat i) / of_nat (k - i) :: 'a)"
    unfolding fact_eq_rev_setprod_nat of_nat_setprod
    by (auto simp add: setprod_dividef intro!: setprod.cong of_nat_diff[symmetric])
  finally show ?thesis .
qed

lemma gbinomial_ge_n_over_k_pow_k:
  fixes k :: nat
    and x :: "'a :: linordered_field"
  assumes "of_nat k \<le> x"
  shows "(x / of_nat k :: 'a) ^ k \<le> x gchoose k"
proof -
  have x: "0 \<le> x"
    using assms of_nat_0_le_iff order_trans by blast
  have "(x / of_nat k :: 'a) ^ k = (\<Prod>i<k. x / of_nat k :: 'a)"
    by (simp add: setprod_constant)
  also have "\<dots> \<le> x gchoose k"
    unfolding gbinomial_altdef_of_nat
  proof (safe intro!: setprod_mono)
    fix i :: nat
    assume ik: "i < k"
    from assms have "x * of_nat i \<ge> of_nat (i * k)"
      by (metis mult.commute mult_le_cancel_right of_nat_less_0_iff of_nat_mult)
    then have "x * of_nat k - x * of_nat i \<le> x * of_nat k - of_nat (i * k)" by arith
    then have "x * of_nat (k - i) \<le> (x - of_nat i) * of_nat k"
      using ik
      by (simp add: algebra_simps zero_less_mult_iff of_nat_diff)
    then have "x * of_nat (k - i) \<le> (x - of_nat i) * (of_nat k :: 'a)"
      unfolding of_nat_mult[symmetric] of_nat_le_iff .
    with assms show "x / of_nat k \<le> (x - of_nat i) / (of_nat (k - i) :: 'a)"
      using \<open>i < k\<close> by (simp add: field_simps)
  qed (simp add: x zero_le_divide_iff)
  finally show ?thesis .
qed

lemma gbinomial_negated_upper: "(a gchoose b) = (-1) ^ b * ((of_nat b - a - 1) gchoose b)"
  by (simp add: gbinomial_pochhammer pochhammer_minus algebra_simps)

lemma gbinomial_minus: "((-a) gchoose b) = (-1) ^ b * ((a + of_nat b - 1) gchoose b)"
  by (subst gbinomial_negated_upper) (simp add: add_ac)

lemma Suc_times_gbinomial:
  "of_nat (Suc b) * ((a + 1) gchoose (Suc b)) = (a + 1) * (a gchoose b)"
proof (cases b)
  case (Suc b)
  hence "((a + 1) gchoose (Suc (Suc b))) =
             (\<Prod>i = 0..Suc b. a + (1 - of_nat i)) / fact (b + 2)"
    by (simp add: field_simps gbinomial_def)
  also have "(\<Prod>i = 0..Suc b. a + (1 - of_nat i)) = (a + 1) * (\<Prod>i = 0..b. a - of_nat i)"
    by (simp add: setprod_nat_ivl_1_Suc setprod_shift_bounds_cl_Suc_ivl)
  also have "... / fact (b + 2) = (a + 1) / of_nat (Suc (Suc b)) * (a gchoose Suc b)"
    by (simp_all add: gbinomial_def setprod_nat_ivl_1_Suc setprod_shift_bounds_cl_Suc_ivl)
  finally show ?thesis by (simp add: Suc field_simps del: of_nat_Suc)
qed simp

lemma gbinomial_factors:
  "((a + 1) gchoose (Suc b)) = (a + 1) / of_nat (Suc b) * (a gchoose b)"
proof (cases b)
  case (Suc b)
  hence "((a + 1) gchoose (Suc (Suc b))) =
             (\<Prod>i = 0..Suc b. a + (1 - of_nat i)) / fact (b + 2)"
    by (simp add: field_simps gbinomial_def)
  also have "(\<Prod>i = 0..Suc b. a + (1 - of_nat i)) = (a + 1) * (\<Prod>i = 0..b. a - of_nat i)"
    by (simp add: setprod_nat_ivl_1_Suc setprod_shift_bounds_cl_Suc_ivl)
  also have "... / fact (b + 2) = (a + 1) / of_nat (Suc (Suc b)) * (a gchoose Suc b)"
    by (simp_all add: gbinomial_def setprod_nat_ivl_1_Suc setprod_shift_bounds_cl_Suc_ivl)
  finally show ?thesis by (simp add: Suc)
qed simp

lemma gbinomial_rec: "((r + 1) gchoose (Suc k)) = (r gchoose k) * ((r + 1) / of_nat (Suc k))"
  using gbinomial_mult_1[of r k]
  by (subst gbinomial_Suc_Suc) (simp add: field_simps del: of_nat_Suc, simp add: algebra_simps)

lemma gbinomial_of_nat_symmetric: "k \<le> n \<Longrightarrow> (of_nat n) gchoose k = (of_nat n) gchoose (n - k)"
  using binomial_symmetric[of k n] by (simp add: binomial_gbinomial [symmetric])


text \<open>The absorption identity (equation 5.5 \cite[p.~157]{GKP}):\[
{r \choose k} = \frac{r}{k}{r - 1 \choose k - 1},\quad \textnormal{integer } k \neq 0.
\]\<close>
lemma gbinomial_absorption':
  "k > 0 \<Longrightarrow> (r gchoose k) = (r / of_nat(k)) * (r - 1 gchoose (k - 1))"
  using gbinomial_rec[of "r - 1" "k - 1"]
  by (simp_all add: gbinomial_rec field_simps del: of_nat_Suc)

text \<open>The absorption identity is written in the following form to avoid
division by $k$ (the lower index) and therefore remove the $k \neq 0$
restriction\cite[p.~157]{GKP}:\[
k{r \choose k} = r{r - 1 \choose k - 1}, \quad \textnormal{integer } k.
\]\<close>
lemma gbinomial_absorption:
  "of_nat (Suc k) * (r gchoose Suc k) = r * ((r - 1) gchoose k)"
  using gbinomial_absorption'[of "Suc k" r] by (simp add: field_simps del: of_nat_Suc)

text \<open>The absorption identity for natural number binomial coefficients:\<close>
lemma binomial_absorption:
  "Suc k * (n choose Suc k) = n * ((n - 1) choose k)"
  by (cases n) (simp_all add: binomial_eq_0 Suc_times_binomial del: binomial_Suc_Suc mult_Suc)

text \<open>The absorption companion identity for natural number coefficients,
following the proof by GKP \cite[p.~157]{GKP}:\<close>
lemma binomial_absorb_comp:
  "(n - k) * (n choose k) = n * ((n - 1) choose k)" (is "?lhs = ?rhs")
proof (cases "n \<le> k")
  case False
  then have "?rhs = Suc ((n - 1) - k) * (n choose Suc ((n - 1) - k))"
    using binomial_symmetric[of k "n - 1"] binomial_absorption[of "(n - 1) - k" n]
    by simp
  also from False have "Suc ((n - 1) - k) = n - k" by simp
  also from False have "n choose \<dots> = n choose k" by (intro binomial_symmetric [symmetric]) simp_all
  finally show ?thesis ..
qed auto

text \<open>The generalised absorption companion identity:\<close>
lemma gbinomial_absorb_comp: "(r - of_nat k) * (r gchoose k) = r * ((r - 1) gchoose k)"
  using pochhammer_absorb_comp[of r k] by (simp add: gbinomial_pochhammer)

lemma gbinomial_addition_formula:
  "r gchoose (Suc k) = ((r - 1) gchoose (Suc k)) + ((r - 1) gchoose k)"
  using gbinomial_Suc_Suc[of "r - 1" k] by (simp add: algebra_simps)

lemma binomial_addition_formula:
  "0 < n \<Longrightarrow> n choose (Suc k) = ((n - 1) choose (Suc k)) + ((n - 1) choose k)"
  by (subst choose_reduce_nat) simp_all


text \<open>
  Equation 5.9 of the reference material \cite[p.~159]{GKP} is a useful
  summation formula, operating on both indices:\[
  \sum\limits_{k \leq n}{r + k \choose k} = {r + n + 1 \choose n},
   \quad \textnormal{integer } n.
  \]
\<close>
lemma gbinomial_parallel_sum:
"(\<Sum>k\<le>n. (r + of_nat k) gchoose k) = (r + of_nat n + 1) gchoose n"
proof (induction n)
  case (Suc m)
  thus ?case using gbinomial_Suc_Suc[of "(r + of_nat m + 1)" m] by (simp add: add_ac)
qed auto

subsection \<open>Summation on the upper index\<close>
text \<open>
  Another summation formula is equation 5.10 of the reference material \cite[p.~160]{GKP},
  aptly named \emph{summation on the upper index}:\[\sum_{0 \leq k \leq n} {k \choose m} =
  {n + 1 \choose m + 1}, \quad \textnormal{integers } m, n \geq 0.\]
\<close>
lemma gbinomial_sum_up_index:
  "(\<Sum>k = 0..n. (of_nat k gchoose m) :: 'a :: field_char_0) = (of_nat n + 1) gchoose (m + 1)"
proof (induction n)
  case 0
  show ?case using gbinomial_Suc_Suc[of 0 m] by (cases m) auto
next
  case (Suc n)
  thus ?case using gbinomial_Suc_Suc[of "of_nat (Suc n) :: 'a" m] by (simp add: add_ac)
qed

lemma gbinomial_index_swap:
  "((-1) ^ m) * ((- (of_nat n) - 1) gchoose m) = ((-1) ^ n) * ((- (of_nat m) - 1) gchoose n)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (of_nat (m + n) gchoose m)"
    by (subst gbinomial_negated_upper) (simp add: power_mult_distrib [symmetric])
  also have "\<dots> = (of_nat (m + n) gchoose n)" by (subst gbinomial_of_nat_symmetric) simp_all
  also have "\<dots> = ?rhs" by (subst gbinomial_negated_upper) simp
  finally show ?thesis .
qed

lemma gbinomial_sum_lower_neg:
  "(\<Sum>k\<le>m. (r gchoose k) * (- 1) ^ k) = (- 1) ^ m * (r - 1 gchoose m)" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>k\<le>m. -(r + 1) + of_nat k gchoose k)"
    by (intro setsum.cong[OF refl]) (subst gbinomial_negated_upper, simp add: power_mult_distrib)
  also have "\<dots>  = -r + of_nat m gchoose m" by (subst gbinomial_parallel_sum) simp
  also have "\<dots> = ?rhs" by (subst gbinomial_negated_upper) (simp add: power_mult_distrib)
  finally show ?thesis .
qed

lemma gbinomial_partial_row_sum:
"(\<Sum>k\<le>m. (r gchoose k) * ((r / 2) - of_nat k)) = ((of_nat m + 1)/2) * (r gchoose (m + 1))"
proof (induction m)
  case (Suc mm)
  hence "(\<Sum>k\<le>Suc mm. (r gchoose k) * (r / 2 - of_nat k)) =
             (r - of_nat (Suc mm)) * (r gchoose Suc mm) / 2" by (simp add: field_simps)
  also have "\<dots> = r * (r - 1 gchoose Suc mm) / 2" by (subst gbinomial_absorb_comp) (rule refl)
  also have "\<dots> = (of_nat (Suc mm) + 1) / 2 * (r gchoose (Suc mm + 1))"
    by (subst gbinomial_absorption [symmetric]) simp
  finally show ?case .
qed simp_all

lemma setsum_bounds_lt_plus1: "(\<Sum>k<mm. f (Suc k)) = (\<Sum>k=1..mm. f k)"
  by (induction mm) simp_all

lemma gbinomial_partial_sum_poly:
  "(\<Sum>k\<le>m. (of_nat m + r gchoose k) * x^k * y^(m-k)) =
       (\<Sum>k\<le>m. (-r gchoose k) * (-x)^k * (x + y)^(m-k))" (is "?lhs m = ?rhs m")
proof (induction m)
  case (Suc mm)
  define G where "G i k = (of_nat i + r gchoose k) * x^k * y^(i-k)" for i k
  define S where "S = ?lhs"
  have SG_def: "S = (\<lambda>i. (\<Sum>k\<le>i. (G i k)))" unfolding S_def G_def ..

  have "S (Suc mm) = G (Suc mm) 0 + (\<Sum>k=Suc 0..Suc mm. G (Suc mm) k)"
    using SG_def by (simp add: setsum_head_Suc atLeast0AtMost [symmetric])
  also have "(\<Sum>k=Suc 0..Suc mm. G (Suc mm) k) = (\<Sum>k=0..mm. G (Suc mm) (Suc k))"
    by (subst setsum_shift_bounds_cl_Suc_ivl) simp
  also have "\<dots> = (\<Sum>k=0..mm. ((of_nat mm + r gchoose (Suc k))
                    + (of_nat mm + r gchoose k)) * x^(Suc k) * y^(mm - k))"
    unfolding G_def by (subst gbinomial_addition_formula) simp
  also have "\<dots> = (\<Sum>k=0..mm. (of_nat mm + r gchoose (Suc k)) * x^(Suc k) * y^(mm - k))
                  + (\<Sum>k=0..mm. (of_nat mm + r gchoose k) * x^(Suc k) * y^(mm - k))"
    by (subst setsum.distrib [symmetric]) (simp add: algebra_simps)
  also have "(\<Sum>k=0..mm. (of_nat mm + r gchoose (Suc k)) * x^(Suc k) * y^(mm - k)) =
               (\<Sum>k<Suc mm. (of_nat mm + r gchoose (Suc k)) * x^(Suc k) * y^(mm - k))"
    by (simp only: atLeast0AtMost lessThan_Suc_atMost)
  also have "\<dots> = (\<Sum>k<mm. (of_nat mm + r gchoose Suc k) * x^(Suc k) * y^(mm-k))
                      + (of_nat mm + r gchoose (Suc mm)) * x^(Suc mm)" (is "_ = ?A + ?B")
    by (subst setsum_lessThan_Suc) simp
  also have "?A = (\<Sum>k=1..mm. (of_nat mm + r gchoose k) * x^k * y^(mm - k + 1))"
  proof (subst setsum_bounds_lt_plus1 [symmetric], intro setsum.cong[OF refl], clarify)
    fix k assume "k < mm"
    hence "mm - k = mm - Suc k + 1" by linarith
    thus "(of_nat mm + r gchoose Suc k) * x ^ Suc k * y ^ (mm - k) =
            (of_nat mm + r gchoose Suc k) * x ^ Suc k * y ^ (mm - Suc k + 1)" by (simp only:)
  qed
  also have "\<dots> + ?B = y * (\<Sum>k=1..mm. (G mm k)) + (of_nat mm + r gchoose (Suc mm)) * x^(Suc mm)"
    unfolding G_def by (subst setsum_right_distrib) (simp add: algebra_simps)
  also have "(\<Sum>k=0..mm. (of_nat mm + r gchoose k) * x^(Suc k) * y^(mm - k)) = x * (S mm)"
      unfolding S_def by (subst setsum_right_distrib) (simp add: atLeast0AtMost algebra_simps)
  also have "(G (Suc mm) 0) = y * (G mm 0)" by (simp add: G_def)
  finally have "S (Suc mm) = y * ((G mm 0) + (\<Sum>k=1..mm. (G mm k)))
                + (of_nat mm + r gchoose (Suc mm)) * x^(Suc mm) + x * (S mm)"
    by (simp add: ring_distribs)
  also have "(G mm 0) + (\<Sum>k=1..mm. (G mm k)) = S mm"
    by (simp add: setsum_head_Suc[symmetric] SG_def atLeast0AtMost)
  finally have "S (Suc mm) = (x + y) * (S mm) + (of_nat mm + r gchoose (Suc mm)) * x^(Suc mm)"
    by (simp add: algebra_simps)
  also have "(of_nat mm + r gchoose (Suc mm)) = (-1) ^ (Suc mm) * (-r gchoose (Suc mm))"
    by (subst gbinomial_negated_upper) simp
  also have "(-1) ^ Suc mm * (- r gchoose Suc mm) * x ^ Suc mm =
                 (-r gchoose (Suc mm)) * (-x) ^ Suc mm" by (simp add: power_minus[of x])
  also have "(x + y) * S mm + \<dots> = (x + y) * ?rhs mm + (-r gchoose (Suc mm)) * (-x)^Suc mm"
    unfolding S_def by (subst Suc.IH) simp
  also have "(x + y) * ?rhs mm = (\<Sum>n\<le>mm. ((- r gchoose n) * (- x) ^ n * (x + y) ^ (Suc mm - n)))"
    by (subst setsum_right_distrib, rule setsum.cong) (simp_all add: Suc_diff_le)
  also have "\<dots> + (-r gchoose (Suc mm)) * (-x)^Suc mm =
                 (\<Sum>n\<le>Suc mm. (- r gchoose n) * (- x) ^ n * (x + y) ^ (Suc mm - n))" by simp
  finally show ?case unfolding S_def .
qed simp_all

lemma gbinomial_partial_sum_poly_xpos:
  "(\<Sum>k\<le>m. (of_nat m + r gchoose k) * x^k * y^(m-k)) =
     (\<Sum>k\<le>m. (of_nat k + r - 1 gchoose k) * x^k * (x + y)^(m-k))"
  apply (subst gbinomial_partial_sum_poly)
  apply (subst gbinomial_negated_upper)
  apply (intro setsum.cong, rule refl)
  apply (simp add: power_mult_distrib [symmetric])
  done

lemma setsum_nat_symmetry:
  "(\<Sum>k = 0..(m::nat). f k) = (\<Sum>k = 0..m. f (m - k))"
  by (rule setsum.reindex_bij_witness[where i="\<lambda>i. m - i" and j="\<lambda>i. m - i"]) auto

lemma binomial_r_part_sum: "(\<Sum>k\<le>m. (2 * m + 1 choose k)) = 2 ^ (2 * m)"
proof -
  have "2 * 2^(2*m) = (\<Sum>k = 0..(2 * m + 1). (2 * m + 1 choose k))"
    using choose_row_sum[where n="2 * m + 1"] by simp
  also have "(\<Sum>k = 0..(2 * m + 1). (2 * m + 1 choose k)) = (\<Sum>k = 0..m. (2 * m + 1 choose k))
                + (\<Sum>k = m+1..2*m+1. (2 * m + 1 choose k))"
    using setsum_ub_add_nat[of 0 m "\<lambda>k. 2 * m + 1 choose k" "m+1"] by (simp add: mult_2)
  also have "(\<Sum>k = m+1..2*m+1. (2 * m + 1 choose k)) =
                 (\<Sum>k = 0..m. (2 * m + 1 choose (k + (m + 1))))"
    by (subst setsum_shift_bounds_cl_nat_ivl [symmetric]) (simp add: mult_2)
  also have "\<dots> = (\<Sum>k = 0..m. (2 * m + 1 choose (m - k)))"
    by (intro setsum.cong[OF refl], subst binomial_symmetric) simp_all
  also have "\<dots> = (\<Sum>k = 0..m. (2 * m + 1 choose k))"
    by (subst (2) setsum_nat_symmetry) (rule refl)
  also have "\<dots> + \<dots> = 2 * \<dots>" by simp
  finally show ?thesis by (subst (asm) mult_cancel1) (simp add: atLeast0AtMost)
qed

lemma gbinomial_r_part_sum:
  "(\<Sum>k\<le>m. (2 * (of_nat m) + 1 gchoose k)) = 2 ^ (2 * m)" (is "?lhs = ?rhs")
proof -
  have "?lhs = of_nat (\<Sum>k\<le>m. (2 * m + 1) choose k)"
    by (simp add: binomial_gbinomial add_ac)
  also have "\<dots> = of_nat (2 ^ (2 * m))" by (subst binomial_r_part_sum) (rule refl)
  finally show ?thesis by simp
qed

lemma gbinomial_sum_nat_pow2:
   "(\<Sum>k\<le>m. (of_nat (m + k) gchoose k :: 'a :: field_char_0) / 2 ^ k) = 2 ^ m" (is "?lhs = ?rhs")
proof -
  have "2 ^ m * 2 ^ m = (2 ^ (2*m) :: 'a)" by (induction m) simp_all
  also have "\<dots> = (\<Sum>k\<le>m. (2 * (of_nat m) + 1 gchoose k))" using gbinomial_r_part_sum ..
  also have "\<dots> = (\<Sum>k\<le>m. (of_nat (m + k) gchoose k) * 2 ^ (m - k))"
    using gbinomial_partial_sum_poly_xpos[where x="1" and y="1" and r="of_nat m + 1" and m="m"]
    by (simp add: add_ac)
  also have "\<dots> = 2 ^ m * (\<Sum>k\<le>m. (of_nat (m + k) gchoose k) / 2 ^ k)"
    by (subst setsum_right_distrib) (simp add: algebra_simps power_diff)
  finally show ?thesis by (subst (asm) mult_left_cancel) simp_all
qed

lemma gbinomial_trinomial_revision:
  assumes "k \<le> m"
  shows   "(r gchoose m) * (of_nat m gchoose k) = (r gchoose k) * (r - of_nat k gchoose (m - k))"
proof -
  have "(r gchoose m) * (of_nat m gchoose k) =
            (r gchoose m) * fact m / (fact k * fact (m - k))"
    using assms by (simp add: binomial_gbinomial [symmetric] binomial_fact)
  also have "\<dots> = (r gchoose k) * (r - of_nat k gchoose (m - k))" using assms
    by (simp add: gbinomial_pochhammer power_diff pochhammer_product)
  finally show ?thesis .
qed


text\<open>Versions of the theorems above for the natural-number version of "choose"\<close>
lemma binomial_altdef_of_nat:
  fixes n k :: nat
    and x :: "'a :: {field_char_0,field}"  \<comment>\<open>the point is to constrain @{typ 'a}\<close>
  assumes "k \<le> n"
  shows "of_nat (n choose k) = (\<Prod>i<k. of_nat (n - i) / of_nat (k - i) :: 'a)"
using assms
by (simp add: gbinomial_altdef_of_nat binomial_gbinomial of_nat_diff)

lemma binomial_ge_n_over_k_pow_k:
  fixes k n :: nat
    and x :: "'a :: linordered_field"
  assumes "k \<le> n"
  shows "(of_nat n / of_nat k :: 'a) ^ k \<le> of_nat (n choose k)"
by (simp add: assms gbinomial_ge_n_over_k_pow_k binomial_gbinomial of_nat_diff)

lemma binomial_le_pow:
  assumes "r \<le> n"
  shows "n choose r \<le> n ^ r"
proof -
  have "n choose r \<le> fact n div fact (n - r)"
    using \<open>r \<le> n\<close> by (subst binomial_fact_lemma[symmetric]) auto
  with fact_div_fact_le_pow [OF assms] show ?thesis by auto
qed

lemma binomial_altdef_nat: "(k::nat) \<le> n \<Longrightarrow>
    n choose k = fact n div (fact k * fact (n - k))"
 by (subst binomial_fact_lemma [symmetric]) auto

lemma choose_dvd: "k \<le> n \<Longrightarrow> fact k * fact (n - k) dvd (fact n :: 'a :: {semiring_div,linordered_semidom})"
  unfolding dvd_def
  apply (rule exI [where x="of_nat (n choose k)"])
  using binomial_fact_lemma [of k n, THEN arg_cong [where f = of_nat and 'b='a]]
  apply auto
  done

lemma fact_fact_dvd_fact:
    "fact k * fact n dvd (fact (k+n) :: 'a :: {semiring_div,linordered_semidom})"
by (metis add.commute add_diff_cancel_left' choose_dvd le_add2)

lemma choose_mult_lemma:
     "((m+r+k) choose (m+k)) * ((m+k) choose k) = ((m+r+k) choose k) * ((m+r) choose m)"
proof -
  have "((m+r+k) choose (m+k)) * ((m+k) choose k) =
        fact (m+r + k) div (fact (m + k) * fact (m+r - m)) * (fact (m + k) div (fact k * fact m))"
    by (simp add: binomial_altdef_nat)
  also have "... = fact (m+r+k) div (fact r * (fact k * fact m))"
    apply (subst div_mult_div_if_dvd)
    apply (auto simp: algebra_simps fact_fact_dvd_fact)
    apply (metis add.assoc add.commute fact_fact_dvd_fact)
    done
  also have "... = (fact (m+r+k) * fact (m+r)) div (fact r * (fact k * fact m) * fact (m+r))"
    apply (subst div_mult_div_if_dvd [symmetric])
    apply (auto simp add: algebra_simps)
    apply (metis fact_fact_dvd_fact dvd_trans nat_mult_dvd_cancel_disj)
    done
  also have "... = (fact (m+r+k) div (fact k * fact (m+r)) * (fact (m+r) div (fact r * fact m)))"
    apply (subst div_mult_div_if_dvd)
    apply (auto simp: fact_fact_dvd_fact algebra_simps)
    done
  finally show ?thesis
    by (simp add: binomial_altdef_nat mult.commute)
qed

text\<open>The "Subset of a Subset" identity\<close>
lemma choose_mult:
  assumes "k\<le>m" "m\<le>n"
    shows "(n choose m) * (m choose k) = (n choose k) * ((n-k) choose (m-k))"
using assms choose_mult_lemma [of "m-k" "n-m" k]
by simp


subsection \<open>Binomial coefficients\<close>

lemma choose_one: "(n::nat) choose 1 = n"
  by simp

(*FIXME: messy and apparently unused*)
lemma binomial_induct [rule_format]: "(ALL (n::nat). P n n) \<longrightarrow>
    (ALL n. P (Suc n) 0) \<longrightarrow> (ALL n. (ALL k < n. P n k \<longrightarrow> P n (Suc k) \<longrightarrow>
    P (Suc n) (Suc k))) \<longrightarrow> (ALL k <= n. P n k)"
  apply (induct n)
  apply auto
  apply (case_tac "k = 0")
  apply auto
  apply (case_tac "k = Suc n")
  apply auto
  apply (metis Suc_le_eq fact.cases le_Suc_eq le_eq_less_or_eq)
  done

lemma card_UNION:
  assumes "finite A" and "\<forall>k \<in> A. finite k"
  shows "card (\<Union>A) = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * (\<Sum>_\<in>\<Inter>I. 1))" by simp
  also have "\<dots> = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (\<Sum>_\<in>\<Inter>I. (- 1) ^ (card I + 1)))" (is "_ = nat ?rhs")
    by(subst setsum_right_distrib) simp
  also have "?rhs = (\<Sum>(I, _)\<in>Sigma {I. I \<subseteq> A \<and> I \<noteq> {}} Inter. (- 1) ^ (card I + 1))"
    using assms by(subst setsum.Sigma)(auto)
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:UNIV. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). (- 1) ^ (card I + 1))"
    by (rule setsum.reindex_cong [where l = "\<lambda>(x, y). (y, x)"]) (auto intro: inj_onI simp add: split_beta)
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:\<Union>A. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). (- 1) ^ (card I + 1))"
    using assms by(auto intro!: setsum.mono_neutral_cong_right finite_SigmaI2 intro: finite_subset[where B="\<Union>A"])
  also have "\<dots> = (\<Sum>x\<in>\<Union>A. (\<Sum>I|I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I. (- 1) ^ (card I + 1)))"
    using assms by(subst setsum.Sigma) auto
  also have "\<dots> = (\<Sum>_\<in>\<Union>A. 1)" (is "setsum ?lhs _ = _")
  proof(rule setsum.cong[OF refl])
    fix x
    assume x: "x \<in> \<Union>A"
    define K where "K = {X \<in> A. x \<in> X}"
    with \<open>finite A\<close> have K: "finite K" by auto
    let ?I = "\<lambda>i. {I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I}"
    have "inj_on snd (SIGMA i:{1..card A}. ?I i)"
      using assms by(auto intro!: inj_onI)
    moreover have [symmetric]: "snd ` (SIGMA i:{1..card A}. ?I i) = {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}"
      using assms by(auto intro!: rev_image_eqI[where x="(card a, a)" for a]
        simp add: card_gt_0_iff[folded Suc_le_eq]
        dest: finite_subset intro: card_mono)
    ultimately have "?lhs x = (\<Sum>(i, I)\<in>(SIGMA i:{1..card A}. ?I i). (- 1) ^ (i + 1))"
      by (rule setsum.reindex_cong [where l = snd]) fastforce
    also have "\<dots> = (\<Sum>i=1..card A. (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. (- 1) ^ (i + 1)))"
      using assms by(subst setsum.Sigma) auto
    also have "\<dots> = (\<Sum>i=1..card A. (- 1) ^ (i + 1) * (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1))"
      by(subst setsum_right_distrib) simp
    also have "\<dots> = (\<Sum>i=1..card K. (- 1) ^ (i + 1) * (\<Sum>I|I \<subseteq> K \<and> card I = i. 1))" (is "_ = ?rhs")
    proof(rule setsum.mono_neutral_cong_right[rule_format])
      show "{1..card K} \<subseteq> {1..card A}" using \<open>finite A\<close>
        by(auto simp add: K_def intro: card_mono)
    next
      fix i
      assume "i \<in> {1..card A} - {1..card K}"
      hence i: "i \<le> card A" "card K < i" by auto
      have "{I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I} = {I. I \<subseteq> K \<and> card I = i}"
        by(auto simp add: K_def)
      also have "\<dots> = {}" using \<open>finite A\<close> i
        by(auto simp add: K_def dest: card_mono[rotated 1])
      finally show "(- 1) ^ (i + 1) * (\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1 :: int) = 0"
        by(simp only:) simp
    next
      fix i
      have "(\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1) = (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)"
        (is "?lhs = ?rhs")
        by(rule setsum.cong)(auto simp add: K_def)
      thus "(- 1) ^ (i + 1) * ?lhs = (- 1) ^ (i + 1) * ?rhs" by simp
    qed simp
    also have "{I. I \<subseteq> K \<and> card I = 0} = {{}}" using assms
      by(auto simp add: card_eq_0_iff K_def dest: finite_subset)
    hence "?rhs = (\<Sum>i = 0..card K. (- 1) ^ (i + 1) * (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)) + 1"
      by(subst (2) setsum_head_Suc)(simp_all )
    also have "\<dots> = (\<Sum>i = 0..card K. (- 1) * ((- 1) ^ i * int (card K choose i))) + 1"
      using K by(subst n_subsets[symmetric]) simp_all
    also have "\<dots> = - (\<Sum>i = 0..card K. (- 1) ^ i * int (card K choose i)) + 1"
      by(subst setsum_right_distrib[symmetric]) simp
    also have "\<dots> =  - ((-1 + 1) ^ card K) + 1"
      by(subst binomial_ring)(simp add: ac_simps)
    also have "\<dots> = 1" using x K by(auto simp add: K_def card_gt_0_iff)
    finally show "?lhs x = 1" .
  qed
  also have "nat \<dots> = card (\<Union>A)" by simp
  finally show ?thesis ..
qed

text\<open>The number of nat lists of length \<open>m\<close> summing to \<open>N\<close> is
@{term "(N + m - 1) choose N"}:\<close>

lemma card_length_listsum_rec:
  assumes "m\<ge>1"
  shows "card {l::nat list. length l = m \<and> listsum l = N} =
    (card {l. length l = (m - 1) \<and> listsum l = N} +
    card {l. length l = m \<and> listsum l + 1 =  N})"
    (is "card ?C = (card ?A + card ?B)")
proof -
  let ?A'="{l. length l = m \<and> listsum l = N \<and> hd l = 0}"
  let ?B'="{l. length l = m \<and> listsum l = N \<and> hd l \<noteq> 0}"
  let ?f ="\<lambda> l. 0#l"
  let ?g ="\<lambda> l. (hd l + 1) # tl l"
  have 1: "\<And>xs x. xs \<noteq> [] \<Longrightarrow> x = hd xs \<Longrightarrow> x # tl xs = xs" by simp
  have 2: "\<And>xs. (xs::nat list) \<noteq> [] \<Longrightarrow> listsum(tl xs) = listsum xs - hd xs"
    by(auto simp add: neq_Nil_conv)
  have f: "bij_betw ?f ?A ?A'"
    apply(rule bij_betw_byWitness[where f' = tl])
    using assms
    by (auto simp: 2 length_0_conv[symmetric] 1 simp del: length_0_conv)
  have 3: "\<And>xs:: nat list. xs \<noteq> [] \<Longrightarrow> hd xs + (listsum xs - hd xs) = listsum xs"
    by (metis 1 listsum_simps(2) 2)
  have g: "bij_betw ?g ?B ?B'"
    apply(rule bij_betw_byWitness[where f' = "\<lambda> l. (hd l - 1) # tl l"])
    using assms
    by (auto simp: 2 length_0_conv[symmetric] intro!: 3
      simp del: length_greater_0_conv length_0_conv)
  { fix M N :: nat have "finite {xs. size xs = M \<and> set xs \<subseteq> {0..<N}}"
    using finite_lists_length_eq[OF finite_atLeastLessThan] conj_commute by auto }
    note fin = this
  have fin_A: "finite ?A" using fin[of _ "N+1"]
    by (intro finite_subset[where ?A = "?A" and ?B = "{xs. size xs = m - 1 \<and> set xs \<subseteq> {0..<N+1}}"],
      auto simp: member_le_listsum_nat less_Suc_eq_le)
  have fin_B: "finite ?B"
    by (intro finite_subset[where ?A = "?B" and ?B = "{xs. size xs = m \<and> set xs \<subseteq> {0..<N}}"],
      auto simp: member_le_listsum_nat less_Suc_eq_le fin)
  have uni: "?C = ?A' \<union> ?B'" by auto
  have disj: "?A' \<inter> ?B' = {}" by auto
  have "card ?C = card(?A' \<union> ?B')" using uni by simp
  also have "\<dots> = card ?A + card ?B"
    using card_Un_disjoint[OF _ _ disj] bij_betw_finite[OF f] bij_betw_finite[OF g]
      bij_betw_same_card[OF f] bij_betw_same_card[OF g] fin_A fin_B
    by presburger
  finally show ?thesis .
qed

lemma card_length_listsum: \<comment>"By Holden Lee, tidied by Tobias Nipkow"
  "card {l::nat list. size l = m \<and> listsum l = N} = (N + m - 1) choose N"
proof (cases m)
  case 0 then show ?thesis
    by (cases N) (auto simp: cong: conj_cong)
next
  case (Suc m')
    have m: "m\<ge>1" by (simp add: Suc)
    then show ?thesis
    proof (induct "N + m - 1" arbitrary: N m)
      case 0   \<comment> "In the base case, the only solution is [0]."
      have [simp]: "{l::nat list. length l = Suc 0 \<and> (\<forall>n\<in>set l. n = 0)} = {[0]}"
        by (auto simp: length_Suc_conv)
      have "m=1 \<and> N=0" using 0 by linarith
      then show ?case by simp
    next
      case (Suc k)

      have c1: "card {l::nat list. size l = (m - 1) \<and> listsum l =  N} =
        (N + (m - 1) - 1) choose N"
      proof cases
        assume "m = 1"
        with Suc.hyps have "N\<ge>1" by auto
        with \<open>m = 1\<close> show ?thesis by (simp add: binomial_eq_0)
      next
        assume "m \<noteq> 1" thus ?thesis using Suc by fastforce
      qed

      from Suc have c2: "card {l::nat list. size l = m \<and> listsum l + 1 = N} =
        (if N>0 then ((N - 1) + m - 1) choose (N - 1) else 0)"
      proof -
        have aux: "\<And>m n. n > 0 \<Longrightarrow> Suc m = n \<longleftrightarrow> m = n - 1" by arith
        from Suc have "N>0 \<Longrightarrow>
          card {l::nat list. size l = m \<and> listsum l + 1 = N} =
          ((N - 1) + m - 1) choose (N - 1)" by (simp add: aux)
        thus ?thesis by auto
      qed

      from Suc.prems have "(card {l::nat list. size l = (m - 1) \<and> listsum l = N} +
          card {l::nat list. size l = m \<and> listsum l + 1 = N}) = (N + m - 1) choose N"
        by (auto simp: c1 c2 choose_reduce_nat[of "N + m - 1" N] simp del: One_nat_def)
      thus ?case using card_length_listsum_rec[OF Suc.prems] by auto
    qed
qed


lemma Suc_times_binomial_add: \<comment> \<open>by Lukas Bulwahn\<close>
  "Suc a * (Suc (a + b) choose Suc a) = Suc b * (Suc (a + b) choose a)"
proof -
  have dvd: "Suc a * (fact a * fact b) dvd fact (Suc (a + b))" for a b
    using fact_fact_dvd_fact[of "Suc a" "b", where 'a=nat]
    by (simp only: fact_Suc add_Suc[symmetric] of_nat_id mult.assoc)

  have "Suc a * (fact (Suc (a + b)) div (Suc a * fact a * fact b)) =
      Suc a * fact (Suc (a + b)) div (Suc a * (fact a * fact b))"
    by (subst div_mult_swap[symmetric]; simp only: mult.assoc dvd)
  also have "\<dots> = Suc b * fact (Suc (a + b)) div (Suc b * (fact a * fact b))"
    by (simp only: div_mult_mult1)
  also have "\<dots> = Suc b * (fact (Suc (a + b)) div (Suc b * (fact a * fact b)))"
    using dvd[of b a] by (subst div_mult_swap[symmetric]; simp only: ac_simps dvd)
  finally show ?thesis
    by (subst (1 2) binomial_altdef_nat)
       (simp_all only: ac_simps diff_Suc_Suc Suc_diff_le diff_add_inverse fact_Suc of_nat_id)
qed

lemma fact_code [code]:
  "fact n = (of_nat (fold_atLeastAtMost_nat (op *) 2 n 1) :: 'a :: semiring_char_0)"
proof -
  have "fact n = (of_nat (\<Prod>{1..n}) :: 'a)" by (simp add: fact_altdef')
  also have "\<Prod>{1..n} = \<Prod>{2..n}"
    by (intro setprod.mono_neutral_right) auto
  also have "\<dots> = fold_atLeastAtMost_nat (op *) 2 n 1"
    by (simp add: setprod_atLeastAtMost_code)
  finally show ?thesis .
qed

lemma pochhammer_code [code]:
  "pochhammer a n = (if n = 0 then 1 else
       fold_atLeastAtMost_nat (\<lambda>n acc. (a + of_nat n) * acc) 0 (n - 1) 1)"
  by (simp add: setprod_atLeastAtMost_code pochhammer_def)

lemma gbinomial_code [code]:
  "a gchoose n = (if n = 0 then 1 else
     fold_atLeastAtMost_nat (\<lambda>n acc. (a - of_nat n) * acc) 0 (n - 1) 1 / fact n)"
  by (simp add: setprod_atLeastAtMost_code gbinomial_def)

(*TODO: This code equation breaks Scala code generation in HOL-Codegenerator_Test. We have to figure out why and how to prevent that. *)

(*
lemma binomial_code [code]:
  "(n choose k) =
      (if k > n then 0
       else if 2 * k > n then (n choose (n - k))
       else (fold_atLeastAtMost_nat (op * ) (n-k+1) n 1 div fact k))"
proof -
  {
    assume "k \<le> n"
    hence "{1..n} = {1..n-k} \<union> {n-k+1..n}" by auto
    hence "(fact n :: nat) = fact (n-k) * \<Prod>{n-k+1..n}"
      by (simp add: setprod.union_disjoint fact_altdef_nat)
  }
  thus ?thesis by (auto simp: binomial_altdef_nat mult_ac setprod_atLeastAtMost_code)
qed
*)

end
