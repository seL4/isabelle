section \<open>More facts about binomial coefficients\<close>

text \<open>
  These facts could have been proven before, but having real numbers
  makes the proofs a lot easier. Thanks to Alexander Maletzky among others.
\<close>

theory Binomial_Plus
imports Real
begin

subsection \<open>More facts about binomial coefficients\<close>

text \<open>
  These facts could have been proven before, but having real numbers
  makes the proofs a lot easier.
\<close>

lemma central_binomial_odd:
  "odd n \<Longrightarrow> n choose (Suc (n div 2)) = n choose (n div 2)"
proof -
  assume "odd n"
  hence "Suc (n div 2) \<le> n" by presburger
  hence "n choose (Suc (n div 2)) = n choose (n - Suc (n div 2))"
    by (rule binomial_symmetric)
  also from \<open>odd n\<close> have "n - Suc (n div 2) = n div 2" by presburger
  finally show ?thesis .
qed

lemma binomial_less_binomial_Suc:
  assumes k: "k < n div 2"
  shows   "n choose k < n choose (Suc k)"
proof -
  from k have k': "k \<le> n" "Suc k \<le> n" by simp_all
  from k' have "real (n choose k) = fact n / (fact k * fact (n - k))"
    by (simp add: binomial_fact)
  also from k' have "n - k = Suc (n - Suc k)" by simp
  also from k' have "fact \<dots> = (real n - real k) * fact (n - Suc k)"
    by (subst fact_Suc) (simp_all add: of_nat_diff)
  also from k have "fact k = fact (Suc k) / (real k + 1)" by (simp add: field_simps)
  also have "fact n / (fact (Suc k) / (real k + 1) * ((real n - real k) * fact (n - Suc k))) =
               (n choose (Suc k)) * ((real k + 1) / (real n - real k))"
    using k by (simp add: field_split_simps binomial_fact)
  also from assms have "(real k + 1) / (real n - real k) < 1" by simp
  finally show ?thesis using k by (simp add: mult_less_cancel_left)
qed

lemma binomial_strict_mono:
  assumes "k < k'" "2*k' \<le> n"
  shows   "n choose k < n choose k'"
proof -
  from assms have "k \<le> k' - 1" by simp
  thus ?thesis
  proof (induction rule: inc_induct)
    case base
    with assms binomial_less_binomial_Suc[of "k' - 1" n]
      show ?case by simp
  next
    case (step k)
    from step.prems step.hyps assms have "n choose k < n choose (Suc k)"
      by (intro binomial_less_binomial_Suc) simp_all
    also have "\<dots> < n choose k'" by (rule step.IH)
    finally show ?case .
  qed
qed

lemma binomial_mono:
  assumes "k \<le> k'" "2*k' \<le> n"
  shows   "n choose k \<le> n choose k'"
  using assms binomial_strict_mono[of k k' n] by (cases "k = k'") simp_all

lemma binomial_strict_antimono:
  assumes "k < k'" "2 * k \<ge> n" "k' \<le> n"
  shows   "n choose k > n choose k'"
proof -
  from assms have "n choose (n - k) > n choose (n - k')"
    by (intro binomial_strict_mono) (simp_all add: algebra_simps)
  with assms show ?thesis by (simp add: binomial_symmetric [symmetric])
qed

lemma binomial_antimono:
  assumes "k \<le> k'" "k \<ge> n div 2" "k' \<le> n"
  shows   "n choose k \<ge> n choose k'"
proof (cases "k = k'")
  case False
  note not_eq = False
  show ?thesis
  proof (cases "k = n div 2 \<and> odd n")
    case False
    with assms(2) have "2*k \<ge> n" by presburger
    with not_eq assms binomial_strict_antimono[of k k' n]
      show ?thesis by simp
  next
    case True
    have "n choose k' \<le> n choose (Suc (n div 2))"
    proof (cases "k' = Suc (n div 2)")
      case False
      with assms True not_eq have "Suc (n div 2) < k'" by simp
      with assms binomial_strict_antimono[of "Suc (n div 2)" k' n] True
        show ?thesis by auto
    qed simp_all
    also from True have "\<dots> = n choose k" by (simp add: central_binomial_odd)
    finally show ?thesis .
  qed
qed simp_all

lemma binomial_maximum: "n choose k \<le> n choose (n div 2)"
proof -
  have "k \<le> n div 2 \<longleftrightarrow> 2*k \<le> n" by linarith
  consider "2*k \<le> n" | "2*k \<ge> n" "k \<le> n" | "k > n" by linarith
  thus ?thesis
  proof cases
    case 1
    thus ?thesis by (intro binomial_mono) linarith+
  next
    case 2
    thus ?thesis by (intro binomial_antimono) simp_all
  qed (simp_all add: binomial_eq_0)
qed

lemma binomial_maximum': "(2*n) choose k \<le> (2*n) choose n"
  using binomial_maximum[of "2*n"] by simp

lemma central_binomial_lower_bound:
  assumes "n > 0"
  shows   "4^n / (2*real n) \<le> real ((2*n) choose n)"
proof -
  from binomial[of 1 1 "2*n"]
    have "4 ^ n = (\<Sum>k\<le>2*n. (2*n) choose k)"
    by (simp add: power_mult power2_eq_square One_nat_def [symmetric] del: One_nat_def)
  also have "{..2*n} = {0<..<2*n} \<union> {0,2*n}" by auto
  also have "(\<Sum>k\<in>\<dots>. (2*n) choose k) =
             (\<Sum>k\<in>{0<..<2*n}. (2*n) choose k) + (\<Sum>k\<in>{0,2*n}. (2*n) choose k)"
    by (subst sum.union_disjoint) auto
  also have "(\<Sum>k\<in>{0,2*n}. (2*n) choose k) \<le> (\<Sum>k\<le>1. (n choose k)\<^sup>2)"
    by (cases n) simp_all
  also from assms have "\<dots> \<le> (\<Sum>k\<le>n. (n choose k)\<^sup>2)"
    by (intro sum_mono2) auto
  also have "\<dots> = (2*n) choose n" by (rule choose_square_sum)
  also have "(\<Sum>k\<in>{0<..<2*n}. (2*n) choose k) \<le> (\<Sum>k\<in>{0<..<2*n}. (2*n) choose n)"
    by (intro sum_mono binomial_maximum')
  also have "\<dots> = card {0<..<2*n} * ((2*n) choose n)" by simp
  also have "card {0<..<2*n} \<le> 2*n - 1" by (cases n) simp_all
  also have "(2 * n - 1) * (2 * n choose n) + (2 * n choose n) = ((2*n) choose n) * (2*n)"
    using assms by (simp add: algebra_simps)
  finally have "4 ^ n \<le> (2 * n choose n) * (2 * n)" by simp_all
  hence "real (4 ^ n) \<le> real ((2 * n choose n) * (2 * n))"
    by (subst of_nat_le_iff)
  with assms show ?thesis by (simp add: field_simps)
qed

lemma upper_le_binomial:
  assumes "0 < k" and "k < n"
  shows "n \<le> n choose k"
proof -
  from assms have "1 \<le> n" by simp
  define k' where "k' = (if n div 2 \<le> k then k else n - k)"
  from assms have 1: "k' \<le> n - 1" and 2: "n div 2 \<le> k'" by (auto simp: k'_def)
  from assms(2) have "k \<le> n" by simp
  have "n choose k = n choose k'" by (simp add: k'_def binomial_symmetric[OF \<open>k \<le> n\<close>])
  have "n = n choose 1" by (simp only: choose_one)
  also from \<open>1 \<le> n\<close> have "\<dots> = n choose (n - 1)" by (rule binomial_symmetric)
  also from 1 2 have "\<dots> \<le> n choose k'" by (rule binomial_antimono) simp
  also have "\<dots> = n choose k" by (simp add: k'_def binomial_symmetric[OF \<open>k \<le> n\<close>])
  finally show ?thesis .
qed

subsection \<open>Results about binomials and integers, thanks to Alexander Maletzky\<close>

text \<open>Restore original sort constraints: semidom rather than field of char 0\<close>
setup \<open>Sign.add_const_constraint (@{const_name gbinomial}, SOME @{typ "'a::{semidom_divide,semiring_char_0} \<Rightarrow> nat \<Rightarrow> 'a"})\<close>

lemma gbinomial_eq_0_int:
  assumes "n < k"
  shows "(int n) gchoose k = 0"
  by (simp add: assms gbinomial_prod_rev prod_zero)

corollary gbinomial_eq_0: "0 \<le> a \<Longrightarrow> a < int k \<Longrightarrow> a gchoose k = 0"
  by (metis nat_eq_iff2 nat_less_iff gbinomial_eq_0_int)

lemma int_binomial: "int (n choose k) = (int n) gchoose k"
proof (cases "k \<le> n")
  case True
  from refl have eq: "(\<Prod>i = 0..<k. int (n - i)) = (\<Prod>i = 0..<k. int n - int i)"
  proof (rule prod.cong)
    fix i
    assume "i \<in> {0..<k}"
    with True show "int (n - i) = int n - int i" by simp
  qed
  show ?thesis
    by (simp add: gbinomial_binomial[symmetric] gbinomial_prod_rev zdiv_int eq)
next
  case False
  thus ?thesis by (simp add: gbinomial_eq_0_int)
qed

lemma falling_fact_pochhammer: "prod (\<lambda>i. a - int i) {0..<k} = (- 1) ^ k * pochhammer (- a) k"
proof -
  have eq: "z ^ Suc n * prod f {0..n} = prod (\<lambda>x. z * f x) {0..n}" for z::int and n f
    by (induct n) (simp_all add: ac_simps)
  show ?thesis
  proof (cases k)
    case 0
    thus ?thesis by (simp add: pochhammer_minus)
  next
    case (Suc n)
    thus ?thesis
      by (simp only: pochhammer_prod atLeastLessThanSuc_atLeastAtMost
          prod.atLeast_Suc_atMost_Suc_shift eq flip: power_mult_distrib) (simp add: of_nat_diff)
  qed
qed

lemma falling_fact_pochhammer': "prod (\<lambda>i. a - int i) {0..<k} = pochhammer (a - int k + 1) k"
  by (simp add: falling_fact_pochhammer pochhammer_minus')

lemma gbinomial_int_pochhammer: "(a::int) gchoose k = (- 1) ^ k * pochhammer (- a) k div fact k"
  by (simp only: gbinomial_prod_rev falling_fact_pochhammer)

lemma gbinomial_int_pochhammer': "a gchoose k = pochhammer (a - int k + 1) k div fact k"
  by (simp only: gbinomial_prod_rev falling_fact_pochhammer')

lemma fact_dvd_pochhammer: "fact k dvd pochhammer (a::int) k"
proof -
  have dvd: "y \<noteq> 0 \<Longrightarrow> ((of_int (x div y))::'a::field_char_0) = of_int x / of_int y \<Longrightarrow> y dvd x"
    for x y :: int
    by (smt dvd_triv_left mult.commute nonzero_eq_divide_eq of_int_eq_0_iff of_int_eq_iff of_int_mult)
  show ?thesis
  proof (cases "0 < a")
    case True
    moreover define n where "n = nat (a - 1) + k"
    ultimately have a: "a = int n - int k + 1" by simp
    from fact_nonzero show ?thesis unfolding a
    proof (rule dvd)
      have "of_int (pochhammer (int n - int k + 1) k div fact k) = (of_int (int n gchoose k)::rat)"
        by (simp only: gbinomial_int_pochhammer')
      also have "\<dots> = of_nat (n choose k)"
        by (metis int_binomial of_int_of_nat_eq)
      also have "\<dots> = (of_nat n) gchoose k" by (fact binomial_gbinomial)
      also have "\<dots> = pochhammer (of_nat n - of_nat k + 1) k / fact k"
        by (fact gbinomial_pochhammer')
      also have "\<dots> = pochhammer (of_int (int n - int k + 1)) k / fact k" by simp
      also have "\<dots> = (of_int (pochhammer (int n - int k + 1) k)) / (of_int (fact k))"
        by (simp only: of_int_fact pochhammer_of_int)
      finally show "of_int (pochhammer (int n - int k + 1) k div fact k) =
                      of_int (pochhammer (int n - int k + 1) k) / rat_of_int (fact k)" .
    qed
  next
    case False
    moreover define n where "n = nat (- a)"
    ultimately have a: "a = - int n" by simp
    from fact_nonzero have "fact k dvd (-1)^k * pochhammer (- int n) k"
    proof (rule dvd)
      have "of_int ((-1)^k * pochhammer (- int n) k div fact k) = (of_int (int n gchoose k)::rat)"
        by (metis falling_fact_pochhammer gbinomial_prod_rev)
      also have "\<dots> = of_int (int (n choose k))" by (simp only: int_binomial)
      also have "\<dots> = of_nat (n choose k)" by simp
      also have "\<dots> = (of_nat n) gchoose k" by (fact binomial_gbinomial)
      also have "\<dots> = (-1)^k * pochhammer (- of_nat n) k / fact k"
        by (fact gbinomial_pochhammer)
      also have "\<dots> = (-1)^k * pochhammer (of_int (- int n)) k / fact k" by simp
      also have "\<dots> = (-1)^k * (of_int (pochhammer (- int n) k)) / (of_int (fact k))"
        by (simp only: of_int_fact pochhammer_of_int)
      also have "\<dots> = (of_int ((-1)^k * pochhammer (- int n) k)) / (of_int (fact k))" by simp
      finally show "of_int ((- 1) ^ k * pochhammer (- int n) k div fact k) =
                    of_int ((- 1) ^ k * pochhammer (- int n) k) / rat_of_int (fact k)" .
    qed
    thus ?thesis unfolding a by (metis dvdI dvd_mult_unit_iff' minus_one_mult_self)
  qed
qed

lemma gbinomial_int_negated_upper: "(a gchoose k) = (-1) ^ k * ((int k - a - 1) gchoose k)"
  by (simp add: gbinomial_int_pochhammer pochhammer_minus algebra_simps fact_dvd_pochhammer div_mult_swap)

lemma gbinomial_int_mult_fact: "fact k * (a gchoose k) = (\<Prod>i = 0..<k. a - int i)"
  by (simp only: gbinomial_int_pochhammer' fact_dvd_pochhammer dvd_mult_div_cancel falling_fact_pochhammer')

corollary gbinomial_int_mult_fact': "(a gchoose k) * fact k = (\<Prod>i = 0..<k. a - int i)"
  using gbinomial_int_mult_fact[of k a] by (simp add: ac_simps)

lemma gbinomial_int_binomial:
  "a gchoose k = (if 0 \<le> a then int ((nat a) choose k) else (-1::int)^k * int ((k + (nat (- a)) - 1) choose k))"
  by (auto simp: int_binomial gbinomial_int_negated_upper[of a] int_ops(6))

corollary gbinomial_nneg: "0 \<le> a \<Longrightarrow> a gchoose k = int ((nat a) choose k)"
  by (simp add: gbinomial_int_binomial)

corollary gbinomial_neg: "a < 0 \<Longrightarrow> a gchoose k = (-1::int)^k * int ((k + (nat (- a)) - 1) choose k)"
  by (simp add: gbinomial_int_binomial)

lemma of_int_gbinomial: "of_int (a gchoose k) = (of_int a :: 'a::field_char_0) gchoose k"
proof -
  have of_int_div: "y dvd x \<Longrightarrow> of_int (x div y) = of_int x / (of_int y :: 'a)" for x y :: int by auto
  show ?thesis
    by (simp add: gbinomial_int_pochhammer' gbinomial_pochhammer' of_int_div fact_dvd_pochhammer
        pochhammer_of_int[symmetric])
qed

lemma uminus_one_gbinomial [simp]: "(- 1::int) gchoose k = (- 1) ^ k"
  by (simp add: gbinomial_int_binomial)

lemma gbinomial_int_Suc_Suc: "(x + 1::int) gchoose (Suc k) = (x gchoose k) + (x gchoose (Suc k))"
proof (rule linorder_cases)
  assume 1: "x + 1 < 0"
  hence 2: "x < 0" by simp
  then obtain n where 3: "nat (- x) = Suc n" using not0_implies_Suc by fastforce
  hence 4: "nat (- x - 1) = n" by simp
  show ?thesis
  proof (cases k)
    case 0
    show ?thesis by (simp add: \<open>k = 0\<close>)
  next
    case (Suc k')
    from 1 2 3 4 show ?thesis by (simp add: \<open>k = Suc k'\<close> gbinomial_int_binomial int_distrib(2))
  qed
next
  assume "x + 1 = 0"
  hence "x = - 1" by simp
  thus ?thesis by simp
next
  assume "0 < x + 1"
  hence "0 \<le> x + 1" and "0 \<le> x" and "nat (x + 1) = Suc (nat x)" by simp_all
  thus ?thesis by (simp add: gbinomial_int_binomial)
qed

corollary plus_Suc_gbinomial:
  "(x + (1 + int k)) gchoose (Suc k) = ((x + int k) gchoose k) + ((x + int k) gchoose (Suc k))"
    (is "?l = ?r")
proof -
  have "?l = (x + int k + 1) gchoose (Suc k)" by (simp only: ac_simps)
  also have "\<dots> = ?r" by (fact gbinomial_int_Suc_Suc)
  finally show ?thesis .
qed

lemma gbinomial_int_n_n [simp]: "(int n) gchoose n = 1"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "int (Suc n) gchoose Suc n = (int n + 1) gchoose Suc n" by (simp add: add.commute)
  also have "\<dots> = (int n gchoose n) + (int n gchoose (Suc n))" by (fact gbinomial_int_Suc_Suc)
  finally show ?case by (simp add: Suc gbinomial_eq_0)
qed

lemma gbinomial_int_Suc_n [simp]: "(1 + int n) gchoose n = 1 + int n"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "1 + int (Suc n) gchoose Suc n = (1 + int n) + 1 gchoose Suc n" by simp
  also have "\<dots> = (1 + int n gchoose n) + (1 + int n gchoose (Suc n))" by (fact gbinomial_int_Suc_Suc)
  also have "\<dots> = 1 + int n + (int (Suc n) gchoose (Suc n))" by (simp add: Suc)
  also have "\<dots> = 1 + int (Suc n)" by (simp only: gbinomial_int_n_n)
  finally show ?case .
qed

lemma zbinomial_eq_0_iff [simp]: "a gchoose k = 0 \<longleftrightarrow> (0 \<le> a \<and> a < int k)"
proof
  assume a: "a gchoose k = 0"
  have 1: "b < int k" if "b gchoose k = 0" for b
  proof (rule ccontr)
    assume "\<not> b < int k"
    hence "0 \<le> b" and "k \<le> nat b" by simp_all
    from this(1) have "int ((nat b) choose k) = b gchoose k" by (simp add: gbinomial_int_binomial)
    also have "\<dots> = 0" by (fact that)
    finally show False using \<open>k \<le> nat b\<close> by simp
  qed
  show "0 \<le> a \<and> a < int k"
  proof
    show "0 \<le> a"
    proof (rule ccontr)
      assume "\<not> 0 \<le> a"
      hence "(-1) ^ k * ((int k - a - 1) gchoose k) = a gchoose k"
        by (simp add: gbinomial_int_negated_upper[of a])
      also have "\<dots> = 0" by (fact a)
      finally have "(int k - a - 1) gchoose k = 0" by simp
      hence "int k - a - 1 < int k" by (rule 1)
      with \<open>\<not> 0 \<le> a\<close> show False by simp
    qed
  next
    from a show "a < int k" by (rule 1)
  qed
qed (auto intro: gbinomial_eq_0)

subsection \<open>Sums\<close>

lemma gchoose_rising_sum_nat: "(\<Sum>j\<le>n. int j + int k gchoose k) = (int n + int k + 1) gchoose (Suc k)"
proof -
  have "(\<Sum>j\<le>n. int j + int k gchoose k) = int (\<Sum>j\<le>n. k + j choose k)"
    by (simp add: int_binomial add.commute)
  also have "(\<Sum>j\<le>n. k + j choose k) = (k + n + 1) choose (k + 1)" by (fact choose_rising_sum(1))
  also have "int \<dots> = (int n + int k + 1) gchoose (Suc k)"
    by (simp add: int_binomial ac_simps del: binomial_Suc_Suc)
  finally show ?thesis .
qed

lemma gchoose_rising_sum:
  assumes "0 \<le> n"   \<comment>\<open>Necessary condition.\<close>
  shows "(\<Sum>j=0..n. j + int k gchoose k) = (n + int k + 1) gchoose (Suc k)"
proof -
  from _ refl have "(\<Sum>j=0..n. j + int k gchoose k) = (\<Sum>j\<in>int ` {0..nat n}. j + int k gchoose k)"
  proof (rule sum.cong)
    from assms show "{0..n} = int ` {0..nat n}" by (simp add: image_int_atLeastAtMost)
  qed
  also have "\<dots> = (\<Sum>j\<le>nat n. int j + int k gchoose k)" by (simp add: sum.reindex atMost_atLeast0)
  also have "\<dots> = (int (nat n) + int k + 1) gchoose (Suc k)" by (fact gchoose_rising_sum_nat)
  also from assms have "\<dots> = (n + int k + 1) gchoose (Suc k)" by (simp add: add.assoc add.commute)
  finally show ?thesis .
qed

end
