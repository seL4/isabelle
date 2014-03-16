(*  Title:      HOL/Transcendental.thy
    Author:     Jacques D. Fleuriot, University of Cambridge, University of Edinburgh
    Author:     Lawrence C Paulson
    Author:     Jeremy Avigad
*)

header{*Power Series, Transcendental Functions etc.*}

theory Transcendental
imports Fact Series Deriv NthRoot
begin

subsection {* Properties of Power Series *}

lemma lemma_realpow_diff:
  fixes y :: "'a::monoid_mult"
  shows "p \<le> n \<Longrightarrow> y ^ (Suc n - p) = (y ^ (n - p)) * y"
proof -
  assume "p \<le> n"
  hence "Suc n - p = Suc (n - p)" by (rule Suc_diff_le)
  thus ?thesis by (simp add: power_commutes)
qed

lemma lemma_realpow_diff_sumr:
  fixes y :: "'a::{comm_semiring_0,monoid_mult}"
  shows
    "(\<Sum>p=0..<Suc n. (x ^ p) * y ^ (Suc n - p)) =
      y * (\<Sum>p=0..<Suc n. (x ^ p) * y ^ (n - p))"
  by (simp add: setsum_right_distrib lemma_realpow_diff mult_ac del: setsum_op_ivl_Suc)

lemma lemma_realpow_diff_sumr2:
  fixes y :: "'a::{comm_ring,monoid_mult}"
  shows
    "x ^ (Suc n) - y ^ (Suc n) =
      (x - y) * (\<Sum>p=0..<Suc n. (x ^ p) * y ^ (n - p))"
proof (induct n)
  case 0 show ?case
    by simp
next
  case (Suc n)
  have "x ^ Suc (Suc n) - y ^ Suc (Suc n) = x * (x * x ^ n) - y * (y * y ^ n)"
    by simp
  also have "... = y * (x ^ (Suc n) - y ^ (Suc n)) + (x - y) * (x * x ^ n)"
    by (simp add: algebra_simps)
  also have "... = y * ((x - y) * (\<Sum>p=0..<Suc n. (x ^ p) * y ^ (n - p))) + (x - y) * (x * x ^ n)"
    by (simp only: Suc)
  also have "... = (x - y) * (y * (\<Sum>p=0..<Suc n. (x ^ p) * y ^ (n - p))) + (x - y) * (x * x ^ n)"
    by (simp only: mult_left_commute)
  also have "... = (x - y) * (\<Sum>p = 0..<Suc (Suc n). x ^ p * y ^ (Suc n - p))"
    by (simp add: setsum_op_ivl_Suc [where n = "Suc n"] distrib_left lemma_realpow_diff_sumr
             del: setsum_op_ivl_Suc)
  finally show ?case .
qed

corollary power_diff_sumr2: --{* @{text COMPLEX_POLYFUN} in HOL Light *}
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows   "x^n - y^n = (x - y) * (\<Sum>i=0..<n. y^(n - Suc i) * x^i)"
using lemma_realpow_diff_sumr2[of x "n - 1" y]
by (cases "n = 0") (simp_all add: field_simps)

lemma lemma_realpow_rev_sumr:
   "(\<Sum>p=0..<Suc n. (x ^ p) * (y ^ (n - p))) =
    (\<Sum>p=0..<Suc n. (x ^ (n - p)) * (y ^ p))"
  apply (rule setsum_reindex_cong [where f="\<lambda>i. n - i"])
  apply (rule inj_onI, auto)
  apply (metis atLeastLessThan_iff diff_diff_cancel diff_less_Suc imageI le0 less_Suc_eq_le)
  done

lemma power_diff_1_eq:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "n \<noteq> 0 \<Longrightarrow> x^n - 1 = (x - 1) * (\<Sum>i=0..<n. (x^i))"
using lemma_realpow_diff_sumr2 [of x _ 1] 
  by (cases n) auto

lemma one_diff_power_eq':
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "n \<noteq> 0 \<Longrightarrow> 1 - x^n = (1 - x) * (\<Sum>i=0..<n. x^(n - Suc i))"
using lemma_realpow_diff_sumr2 [of 1 _ x] 
  by (cases n) auto

lemma one_diff_power_eq:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "n \<noteq> 0 \<Longrightarrow> 1 - x^n = (1 - x) * (\<Sum>i=0..<n. x^i)"
by (metis one_diff_power_eq' [of n x] nat_diff_setsum_reindex)

text{*Power series has a `circle` of convergence, i.e. if it sums for @{term
  x}, then it sums absolutely for @{term z} with @{term "\<bar>z\<bar> < \<bar>x\<bar>"}.*}

lemma powser_insidea:
  fixes x z :: "'a::real_normed_div_algebra"
  assumes 1: "summable (\<lambda>n. f n * x ^ n)"
    and 2: "norm z < norm x"
  shows "summable (\<lambda>n. norm (f n * z ^ n))"
proof -
  from 2 have x_neq_0: "x \<noteq> 0" by clarsimp
  from 1 have "(\<lambda>n. f n * x ^ n) ----> 0"
    by (rule summable_LIMSEQ_zero)
  hence "convergent (\<lambda>n. f n * x ^ n)"
    by (rule convergentI)
  hence "Cauchy (\<lambda>n. f n * x ^ n)"
    by (rule convergent_Cauchy)
  hence "Bseq (\<lambda>n. f n * x ^ n)"
    by (rule Cauchy_Bseq)
  then obtain K where 3: "0 < K" and 4: "\<forall>n. norm (f n * x ^ n) \<le> K"
    by (simp add: Bseq_def, safe)
  have "\<exists>N. \<forall>n\<ge>N. norm (norm (f n * z ^ n)) \<le>
                   K * norm (z ^ n) * inverse (norm (x ^ n))"
  proof (intro exI allI impI)
    fix n::nat
    assume "0 \<le> n"
    have "norm (norm (f n * z ^ n)) * norm (x ^ n) =
          norm (f n * x ^ n) * norm (z ^ n)"
      by (simp add: norm_mult abs_mult)
    also have "\<dots> \<le> K * norm (z ^ n)"
      by (simp only: mult_right_mono 4 norm_ge_zero)
    also have "\<dots> = K * norm (z ^ n) * (inverse (norm (x ^ n)) * norm (x ^ n))"
      by (simp add: x_neq_0)
    also have "\<dots> = K * norm (z ^ n) * inverse (norm (x ^ n)) * norm (x ^ n)"
      by (simp only: mult_assoc)
    finally show "norm (norm (f n * z ^ n)) \<le>
                  K * norm (z ^ n) * inverse (norm (x ^ n))"
      by (simp add: mult_le_cancel_right x_neq_0)
  qed
  moreover have "summable (\<lambda>n. K * norm (z ^ n) * inverse (norm (x ^ n)))"
  proof -
    from 2 have "norm (norm (z * inverse x)) < 1"
      using x_neq_0
      by (simp add: norm_mult nonzero_norm_inverse divide_inverse [where 'a=real, symmetric])
    hence "summable (\<lambda>n. norm (z * inverse x) ^ n)"
      by (rule summable_geometric)
    hence "summable (\<lambda>n. K * norm (z * inverse x) ^ n)"
      by (rule summable_mult)
    thus "summable (\<lambda>n. K * norm (z ^ n) * inverse (norm (x ^ n)))"
      using x_neq_0
      by (simp add: norm_mult nonzero_norm_inverse power_mult_distrib
                    power_inverse norm_power mult_assoc)
  qed
  ultimately show "summable (\<lambda>n. norm (f n * z ^ n))"
    by (rule summable_comparison_test)
qed

lemma powser_inside:
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}"
  shows
    "summable (\<lambda>n. f n * (x ^ n)) \<Longrightarrow> norm z < norm x \<Longrightarrow>
      summable (\<lambda>n. f n * (z ^ n))"
  by (rule powser_insidea [THEN summable_norm_cancel])

lemma sum_split_even_odd:
  fixes f :: "nat \<Rightarrow> real"
  shows
    "(\<Sum> i = 0 ..< 2 * n. if even i then f i else g i) =
     (\<Sum> i = 0 ..< n. f (2 * i)) + (\<Sum> i = 0 ..< n. g (2 * i + 1))"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(\<Sum> i = 0 ..< 2 * Suc n. if even i then f i else g i) =
    (\<Sum> i = 0 ..< n. f (2 * i)) + (\<Sum> i = 0 ..< n. g (2 * i + 1)) + (f (2 * n) + g (2 * n + 1))"
    using Suc.hyps unfolding One_nat_def by auto
  also have "\<dots> = (\<Sum> i = 0 ..< Suc n. f (2 * i)) + (\<Sum> i = 0 ..< Suc n. g (2 * i + 1))"
    by auto
  finally show ?case .
qed

lemma sums_if':
  fixes g :: "nat \<Rightarrow> real"
  assumes "g sums x"
  shows "(\<lambda> n. if even n then 0 else g ((n - 1) div 2)) sums x"
  unfolding sums_def
proof (rule LIMSEQ_I)
  fix r :: real
  assume "0 < r"
  from `g sums x`[unfolded sums_def, THEN LIMSEQ_D, OF this]
  obtain no where no_eq: "\<And> n. n \<ge> no \<Longrightarrow> (norm (setsum g { 0..<n } - x) < r)" by blast

  let ?SUM = "\<lambda> m. \<Sum> i = 0 ..< m. if even i then 0 else g ((i - 1) div 2)"
  {
    fix m
    assume "m \<ge> 2 * no"
    hence "m div 2 \<ge> no" by auto
    have sum_eq: "?SUM (2 * (m div 2)) = setsum g { 0 ..< m div 2 }"
      using sum_split_even_odd by auto
    hence "(norm (?SUM (2 * (m div 2)) - x) < r)"
      using no_eq unfolding sum_eq using `m div 2 \<ge> no` by auto
    moreover
    have "?SUM (2 * (m div 2)) = ?SUM m"
    proof (cases "even m")
      case True
      show ?thesis
        unfolding even_nat_div_two_times_two[OF True, unfolded numeral_2_eq_2[symmetric]] ..
    next
      case False
      hence "even (Suc m)" by auto
      from even_nat_div_two_times_two[OF this, unfolded numeral_2_eq_2[symmetric]]
        odd_nat_plus_one_div_two[OF False, unfolded numeral_2_eq_2[symmetric]]
      have eq: "Suc (2 * (m div 2)) = m" by auto
      hence "even (2 * (m div 2))" using `odd m` by auto
      have "?SUM m = ?SUM (Suc (2 * (m div 2)))" unfolding eq ..
      also have "\<dots> = ?SUM (2 * (m div 2))" using `even (2 * (m div 2))` by auto
      finally show ?thesis by auto
    qed
    ultimately have "(norm (?SUM m - x) < r)" by auto
  }
  thus "\<exists> no. \<forall> m \<ge> no. norm (?SUM m - x) < r" by blast
qed

lemma sums_if:
  fixes g :: "nat \<Rightarrow> real"
  assumes "g sums x" and "f sums y"
  shows "(\<lambda> n. if even n then f (n div 2) else g ((n - 1) div 2)) sums (x + y)"
proof -
  let ?s = "\<lambda> n. if even n then 0 else f ((n - 1) div 2)"
  {
    fix B T E
    have "(if B then (0 :: real) else E) + (if B then T else 0) = (if B then T else E)"
      by (cases B) auto
  } note if_sum = this
  have g_sums: "(\<lambda> n. if even n then 0 else g ((n - 1) div 2)) sums x"
    using sums_if'[OF `g sums x`] .
  {
    have "?s 0 = 0" by auto
    have Suc_m1: "\<And> n. Suc n - 1 = n" by auto
    have if_eq: "\<And>B T E. (if \<not> B then T else E) = (if B then E else T)" by auto

    have "?s sums y" using sums_if'[OF `f sums y`] .
    from this[unfolded sums_def, THEN LIMSEQ_Suc]
    have "(\<lambda> n. if even n then f (n div 2) else 0) sums y"
      unfolding sums_def setsum_shift_lb_Suc0_0_upt[where f="?s", OF `?s 0 = 0`, symmetric]
                image_Suc_atLeastLessThan[symmetric] setsum_reindex[OF inj_Suc, unfolded comp_def]
                even_Suc Suc_m1 if_eq .
  }
  from sums_add[OF g_sums this] show ?thesis unfolding if_sum .
qed

subsection {* Alternating series test / Leibniz formula *}

lemma sums_alternating_upper_lower:
  fixes a :: "nat \<Rightarrow> real"
  assumes mono: "\<And>n. a (Suc n) \<le> a n" and a_pos: "\<And>n. 0 \<le> a n" and "a ----> 0"
  shows "\<exists>l. ((\<forall>n. (\<Sum>i=0..<2*n. -1^i*a i) \<le> l) \<and> (\<lambda> n. \<Sum>i=0..<2*n. -1^i*a i) ----> l) \<and>
             ((\<forall>n. l \<le> (\<Sum>i=0..<2*n + 1. -1^i*a i)) \<and> (\<lambda> n. \<Sum>i=0..<2*n + 1. -1^i*a i) ----> l)"
  (is "\<exists>l. ((\<forall>n. ?f n \<le> l) \<and> _) \<and> ((\<forall>n. l \<le> ?g n) \<and> _)")
proof (rule nested_sequence_unique)
  have fg_diff: "\<And>n. ?f n - ?g n = - a (2 * n)" unfolding One_nat_def by auto

  show "\<forall>n. ?f n \<le> ?f (Suc n)"
  proof
    fix n
    show "?f n \<le> ?f (Suc n)" using mono[of "2*n"] by auto
  qed
  show "\<forall>n. ?g (Suc n) \<le> ?g n"
  proof
    fix n
    show "?g (Suc n) \<le> ?g n" using mono[of "Suc (2*n)"]
      unfolding One_nat_def by auto
  qed
  show "\<forall>n. ?f n \<le> ?g n"
  proof
    fix n
    show "?f n \<le> ?g n" using fg_diff a_pos
      unfolding One_nat_def by auto
  qed
  show "(\<lambda>n. ?f n - ?g n) ----> 0" unfolding fg_diff
  proof (rule LIMSEQ_I)
    fix r :: real
    assume "0 < r"
    with `a ----> 0`[THEN LIMSEQ_D] obtain N where "\<And> n. n \<ge> N \<Longrightarrow> norm (a n - 0) < r"
      by auto
    hence "\<forall>n \<ge> N. norm (- a (2 * n) - 0) < r" by auto
    thus "\<exists>N. \<forall>n \<ge> N. norm (- a (2 * n) - 0) < r" by auto
  qed
qed

lemma summable_Leibniz':
  fixes a :: "nat \<Rightarrow> real"
  assumes a_zero: "a ----> 0"
    and a_pos: "\<And> n. 0 \<le> a n"
    and a_monotone: "\<And> n. a (Suc n) \<le> a n"
  shows summable: "summable (\<lambda> n. (-1)^n * a n)"
    and "\<And>n. (\<Sum>i=0..<2*n. (-1)^i*a i) \<le> (\<Sum>i. (-1)^i*a i)"
    and "(\<lambda>n. \<Sum>i=0..<2*n. (-1)^i*a i) ----> (\<Sum>i. (-1)^i*a i)"
    and "\<And>n. (\<Sum>i. (-1)^i*a i) \<le> (\<Sum>i=0..<2*n+1. (-1)^i*a i)"
    and "(\<lambda>n. \<Sum>i=0..<2*n+1. (-1)^i*a i) ----> (\<Sum>i. (-1)^i*a i)"
proof -
  let ?S = "\<lambda>n. (-1)^n * a n"
  let ?P = "\<lambda>n. \<Sum>i=0..<n. ?S i"
  let ?f = "\<lambda>n. ?P (2 * n)"
  let ?g = "\<lambda>n. ?P (2 * n + 1)"
  obtain l :: real
    where below_l: "\<forall> n. ?f n \<le> l"
      and "?f ----> l"
      and above_l: "\<forall> n. l \<le> ?g n"
      and "?g ----> l"
    using sums_alternating_upper_lower[OF a_monotone a_pos a_zero] by blast

  let ?Sa = "\<lambda>m. \<Sum> n = 0..<m. ?S n"
  have "?Sa ----> l"
  proof (rule LIMSEQ_I)
    fix r :: real
    assume "0 < r"
    with `?f ----> l`[THEN LIMSEQ_D]
    obtain f_no where f: "\<And> n. n \<ge> f_no \<Longrightarrow> norm (?f n - l) < r" by auto

    from `0 < r` `?g ----> l`[THEN LIMSEQ_D]
    obtain g_no where g: "\<And> n. n \<ge> g_no \<Longrightarrow> norm (?g n - l) < r" by auto

    {
      fix n :: nat
      assume "n \<ge> (max (2 * f_no) (2 * g_no))"
      hence "n \<ge> 2 * f_no" and "n \<ge> 2 * g_no" by auto
      have "norm (?Sa n - l) < r"
      proof (cases "even n")
        case True
        from even_nat_div_two_times_two[OF this]
        have n_eq: "2 * (n div 2) = n"
          unfolding numeral_2_eq_2[symmetric] by auto
        with `n \<ge> 2 * f_no` have "n div 2 \<ge> f_no"
          by auto
        from f[OF this] show ?thesis
          unfolding n_eq atLeastLessThanSuc_atLeastAtMost .
      next
        case False
        hence "even (n - 1)" by simp
        from even_nat_div_two_times_two[OF this]
        have n_eq: "2 * ((n - 1) div 2) = n - 1"
          unfolding numeral_2_eq_2[symmetric] by auto
        hence range_eq: "n - 1 + 1 = n"
          using odd_pos[OF False] by auto

        from n_eq `n \<ge> 2 * g_no` have "(n - 1) div 2 \<ge> g_no"
          by auto
        from g[OF this] show ?thesis
          unfolding n_eq atLeastLessThanSuc_atLeastAtMost range_eq .
      qed
    }
    thus "\<exists>no. \<forall>n \<ge> no. norm (?Sa n - l) < r" by blast
  qed
  hence sums_l: "(\<lambda>i. (-1)^i * a i) sums l"
    unfolding sums_def atLeastLessThanSuc_atLeastAtMost[symmetric] .
  thus "summable ?S" using summable_def by auto

  have "l = suminf ?S" using sums_unique[OF sums_l] .

  fix n
  show "suminf ?S \<le> ?g n"
    unfolding sums_unique[OF sums_l, symmetric] using above_l by auto
  show "?f n \<le> suminf ?S"
    unfolding sums_unique[OF sums_l, symmetric] using below_l by auto
  show "?g ----> suminf ?S"
    using `?g ----> l` `l = suminf ?S` by auto
  show "?f ----> suminf ?S"
    using `?f ----> l` `l = suminf ?S` by auto
qed

theorem summable_Leibniz:
  fixes a :: "nat \<Rightarrow> real"
  assumes a_zero: "a ----> 0" and "monoseq a"
  shows "summable (\<lambda> n. (-1)^n * a n)" (is "?summable")
    and "0 < a 0 \<longrightarrow>
      (\<forall>n. (\<Sum>i. -1^i*a i) \<in> { \<Sum>i=0..<2*n. -1^i * a i .. \<Sum>i=0..<2*n+1. -1^i * a i})" (is "?pos")
    and "a 0 < 0 \<longrightarrow>
      (\<forall>n. (\<Sum>i. -1^i*a i) \<in> { \<Sum>i=0..<2*n+1. -1^i * a i .. \<Sum>i=0..<2*n. -1^i * a i})" (is "?neg")
    and "(\<lambda>n. \<Sum>i=0..<2*n. -1^i*a i) ----> (\<Sum>i. -1^i*a i)" (is "?f")
    and "(\<lambda>n. \<Sum>i=0..<2*n+1. -1^i*a i) ----> (\<Sum>i. -1^i*a i)" (is "?g")
proof -
  have "?summable \<and> ?pos \<and> ?neg \<and> ?f \<and> ?g"
  proof (cases "(\<forall> n. 0 \<le> a n) \<and> (\<forall>m. \<forall>n\<ge>m. a n \<le> a m)")
    case True
    hence ord: "\<And>n m. m \<le> n \<Longrightarrow> a n \<le> a m" and ge0: "\<And> n. 0 \<le> a n"
      by auto
    {
      fix n
      have "a (Suc n) \<le> a n"
        using ord[where n="Suc n" and m=n] by auto
    } note mono = this
    note leibniz = summable_Leibniz'[OF `a ----> 0` ge0]
    from leibniz[OF mono]
    show ?thesis using `0 \<le> a 0` by auto
  next
    let ?a = "\<lambda> n. - a n"
    case False
    with monoseq_le[OF `monoseq a` `a ----> 0`]
    have "(\<forall> n. a n \<le> 0) \<and> (\<forall>m. \<forall>n\<ge>m. a m \<le> a n)" by auto
    hence ord: "\<And>n m. m \<le> n \<Longrightarrow> ?a n \<le> ?a m" and ge0: "\<And> n. 0 \<le> ?a n"
      by auto
    {
      fix n
      have "?a (Suc n) \<le> ?a n" using ord[where n="Suc n" and m=n]
        by auto
    } note monotone = this
    note leibniz =
      summable_Leibniz'[OF _ ge0, of "\<lambda>x. x",
        OF tendsto_minus[OF `a ----> 0`, unfolded minus_zero] monotone]
    have "summable (\<lambda> n. (-1)^n * ?a n)"
      using leibniz(1) by auto
    then obtain l where "(\<lambda> n. (-1)^n * ?a n) sums l"
      unfolding summable_def by auto
    from this[THEN sums_minus] have "(\<lambda> n. (-1)^n * a n) sums -l"
      by auto
    hence ?summable unfolding summable_def by auto
    moreover
    have "\<And>a b :: real. \<bar>- a - - b\<bar> = \<bar>a - b\<bar>"
      unfolding minus_diff_minus by auto

    from suminf_minus[OF leibniz(1), unfolded mult_minus_right minus_minus]
    have move_minus: "(\<Sum>n. - (-1 ^ n * a n)) = - (\<Sum>n. -1 ^ n * a n)"
      by auto

    have ?pos using `0 \<le> ?a 0` by auto
    moreover have ?neg
      using leibniz(2,4)
      unfolding mult_minus_right setsum_negf move_minus neg_le_iff_le
      by auto
    moreover have ?f and ?g
      using leibniz(3,5)[unfolded mult_minus_right setsum_negf move_minus, THEN tendsto_minus_cancel]
      by auto
    ultimately show ?thesis by auto
  qed
  then show ?summable and ?pos and ?neg and ?f and ?g 
    by safe
qed

subsection {* Term-by-Term Differentiability of Power Series *}

definition diffs :: "(nat => 'a::ring_1) => nat => 'a"
  where "diffs c = (\<lambda>n. of_nat (Suc n) * c(Suc n))"

text{*Lemma about distributing negation over it*}
lemma diffs_minus: "diffs (\<lambda>n. - c n) = (\<lambda>n. - diffs c n)"
  by (simp add: diffs_def)

lemma sums_Suc_imp:
  assumes f: "f 0 = 0"
  shows "(\<lambda>n. f (Suc n)) sums s \<Longrightarrow> (\<lambda>n. f n) sums s"
  unfolding sums_def
  apply (rule LIMSEQ_imp_Suc)
  apply (subst setsum_shift_lb_Suc0_0_upt [where f=f, OF f, symmetric])
  apply (simp only: setsum_shift_bounds_Suc_ivl)
  done

lemma diffs_equiv:
  fixes x :: "'a::{real_normed_vector, ring_1}"
  shows "summable (\<lambda>n. (diffs c)(n) * (x ^ n)) \<Longrightarrow>
      (\<lambda>n. of_nat n * c(n) * (x ^ (n - Suc 0))) sums
         (\<Sum>n. (diffs c)(n) * (x ^ n))"
  unfolding diffs_def
  by (simp add: summable_sums sums_Suc_imp)

lemma lemma_termdiff1:
  fixes z :: "'a :: {monoid_mult,comm_ring}" shows
  "(\<Sum>p=0..<m. (((z + h) ^ (m - p)) * (z ^ p)) - (z ^ m)) =
   (\<Sum>p=0..<m. (z ^ p) * (((z + h) ^ (m - p)) - (z ^ (m - p))))"
  by (auto simp add: algebra_simps power_add [symmetric])

lemma sumr_diff_mult_const2:
  "setsum f {0..<n} - of_nat n * (r::'a::ring_1) = (\<Sum>i = 0..<n. f i - r)"
  by (simp add: setsum_subtractf)

lemma lemma_termdiff2:
  fixes h :: "'a :: {field}"
  assumes h: "h \<noteq> 0"
  shows
    "((z + h) ^ n - z ^ n) / h - of_nat n * z ^ (n - Suc 0) =
     h * (\<Sum>p=0..< n - Suc 0. \<Sum>q=0..< n - Suc 0 - p.
          (z + h) ^ q * z ^ (n - 2 - q))" (is "?lhs = ?rhs")
  apply (subgoal_tac "h * ?lhs = h * ?rhs", simp add: h)
  apply (simp add: right_diff_distrib diff_divide_distrib h)
  apply (simp add: mult_assoc [symmetric])
  apply (cases "n", simp)
  apply (simp add: lemma_realpow_diff_sumr2 h
                   right_diff_distrib [symmetric] mult_assoc
              del: power_Suc setsum_op_ivl_Suc of_nat_Suc)
  apply (subst lemma_realpow_rev_sumr)
  apply (subst sumr_diff_mult_const2)
  apply simp
  apply (simp only: lemma_termdiff1 setsum_right_distrib)
  apply (rule setsum_cong [OF refl])
  apply (simp add: less_iff_Suc_add)
  apply (clarify)
  apply (simp add: setsum_right_distrib lemma_realpow_diff_sumr2 mult_ac
              del: setsum_op_ivl_Suc power_Suc)
  apply (subst mult_assoc [symmetric], subst power_add [symmetric])
  apply (simp add: mult_ac)
  done

lemma real_setsum_nat_ivl_bounded2:
  fixes K :: "'a::linordered_semidom"
  assumes f: "\<And>p::nat. p < n \<Longrightarrow> f p \<le> K"
    and K: "0 \<le> K"
  shows "setsum f {0..<n-k} \<le> of_nat n * K"
  apply (rule order_trans [OF setsum_mono])
  apply (rule f, simp)
  apply (simp add: mult_right_mono K)
  done

lemma lemma_termdiff3:
  fixes h z :: "'a::{real_normed_field}"
  assumes 1: "h \<noteq> 0"
    and 2: "norm z \<le> K"
    and 3: "norm (z + h) \<le> K"
  shows "norm (((z + h) ^ n - z ^ n) / h - of_nat n * z ^ (n - Suc 0))
          \<le> of_nat n * of_nat (n - Suc 0) * K ^ (n - 2) * norm h"
proof -
  have "norm (((z + h) ^ n - z ^ n) / h - of_nat n * z ^ (n - Suc 0)) =
        norm (\<Sum>p = 0..<n - Suc 0. \<Sum>q = 0..<n - Suc 0 - p.
          (z + h) ^ q * z ^ (n - 2 - q)) * norm h"
    by (metis (lifting, no_types) lemma_termdiff2 [OF 1] mult_commute norm_mult)
  also have "\<dots> \<le> of_nat n * (of_nat (n - Suc 0) * K ^ (n - 2)) * norm h"
  proof (rule mult_right_mono [OF _ norm_ge_zero])
    from norm_ge_zero 2 have K: "0 \<le> K"
      by (rule order_trans)
    have le_Kn: "\<And>i j n. i + j = n \<Longrightarrow> norm ((z + h) ^ i * z ^ j) \<le> K ^ n"
      apply (erule subst)
      apply (simp only: norm_mult norm_power power_add)
      apply (intro mult_mono power_mono 2 3 norm_ge_zero zero_le_power K)
      done
    show "norm (\<Sum>p = 0..<n - Suc 0. \<Sum>q = 0..<n - Suc 0 - p. (z + h) ^ q * z ^ (n - 2 - q))
          \<le> of_nat n * (of_nat (n - Suc 0) * K ^ (n - 2))"
      apply (intro
         order_trans [OF norm_setsum]
         real_setsum_nat_ivl_bounded2
         mult_nonneg_nonneg
         of_nat_0_le_iff
         zero_le_power K)
      apply (rule le_Kn, simp)
      done
  qed
  also have "\<dots> = of_nat n * of_nat (n - Suc 0) * K ^ (n - 2) * norm h"
    by (simp only: mult_assoc)
  finally show ?thesis .
qed

lemma lemma_termdiff4:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes k: "0 < (k::real)"
    and le: "\<And>h. \<lbrakk>h \<noteq> 0; norm h < k\<rbrakk> \<Longrightarrow> norm (f h) \<le> K * norm h"
  shows "f -- 0 --> 0"
proof (rule tendsto_norm_zero_cancel)
  show "(\<lambda>h. norm (f h)) -- 0 --> 0"
  proof (rule real_tendsto_sandwich)
    show "eventually (\<lambda>h. 0 \<le> norm (f h)) (at 0)"
      by simp
    show "eventually (\<lambda>h. norm (f h) \<le> K * norm h) (at 0)"
      using k by (auto simp add: eventually_at dist_norm le)
    show "(\<lambda>h. 0) -- (0::'a) --> (0::real)"
      by (rule tendsto_const)
    have "(\<lambda>h. K * norm h) -- (0::'a) --> K * norm (0::'a)"
      by (intro tendsto_intros)
    then show "(\<lambda>h. K * norm h) -- (0::'a) --> 0"
      by simp
  qed
qed

lemma lemma_termdiff5:
  fixes g :: "'a::real_normed_vector \<Rightarrow> nat \<Rightarrow> 'b::banach"
  assumes k: "0 < (k::real)"
  assumes f: "summable f"
  assumes le: "\<And>h n. \<lbrakk>h \<noteq> 0; norm h < k\<rbrakk> \<Longrightarrow> norm (g h n) \<le> f n * norm h"
  shows "(\<lambda>h. suminf (g h)) -- 0 --> 0"
proof (rule lemma_termdiff4 [OF k])
  fix h::'a
  assume "h \<noteq> 0" and "norm h < k"
  hence A: "\<forall>n. norm (g h n) \<le> f n * norm h"
    by (simp add: le)
  hence "\<exists>N. \<forall>n\<ge>N. norm (norm (g h n)) \<le> f n * norm h"
    by simp
  moreover from f have B: "summable (\<lambda>n. f n * norm h)"
    by (rule summable_mult2)
  ultimately have C: "summable (\<lambda>n. norm (g h n))"
    by (rule summable_comparison_test)
  hence "norm (suminf (g h)) \<le> (\<Sum>n. norm (g h n))"
    by (rule summable_norm)
  also from A C B have "(\<Sum>n. norm (g h n)) \<le> (\<Sum>n. f n * norm h)"
    by (rule summable_le)
  also from f have "(\<Sum>n. f n * norm h) = suminf f * norm h"
    by (rule suminf_mult2 [symmetric])
  finally show "norm (suminf (g h)) \<le> suminf f * norm h" .
qed


text{* FIXME: Long proofs*}

lemma termdiffs_aux:
  fixes x :: "'a::{real_normed_field,banach}"
  assumes 1: "summable (\<lambda>n. diffs (diffs c) n * K ^ n)"
    and 2: "norm x < norm K"
  shows "(\<lambda>h. \<Sum>n. c n * (((x + h) ^ n - x ^ n) / h
             - of_nat n * x ^ (n - Suc 0))) -- 0 --> 0"
proof -
  from dense [OF 2]
  obtain r where r1: "norm x < r" and r2: "r < norm K" by fast
  from norm_ge_zero r1 have r: "0 < r"
    by (rule order_le_less_trans)
  hence r_neq_0: "r \<noteq> 0" by simp
  show ?thesis
  proof (rule lemma_termdiff5)
    show "0 < r - norm x" using r1 by simp
    from r r2 have "norm (of_real r::'a) < norm K"
      by simp
    with 1 have "summable (\<lambda>n. norm (diffs (diffs c) n * (of_real r ^ n)))"
      by (rule powser_insidea)
    hence "summable (\<lambda>n. diffs (diffs (\<lambda>n. norm (c n))) n * r ^ n)"
      using r
      by (simp add: diffs_def norm_mult norm_power del: of_nat_Suc)
    hence "summable (\<lambda>n. of_nat n * diffs (\<lambda>n. norm (c n)) n * r ^ (n - Suc 0))"
      by (rule diffs_equiv [THEN sums_summable])
    also have "(\<lambda>n. of_nat n * diffs (\<lambda>n. norm (c n)) n * r ^ (n - Suc 0)) =
      (\<lambda>n. diffs (\<lambda>m. of_nat (m - Suc 0) * norm (c m) * inverse r) n * (r ^ n))"
      apply (rule ext)
      apply (simp add: diffs_def)
      apply (case_tac n, simp_all add: r_neq_0)
      done
    finally have "summable
      (\<lambda>n. of_nat n * (of_nat (n - Suc 0) * norm (c n) * inverse r) * r ^ (n - Suc 0))"
      by (rule diffs_equiv [THEN sums_summable])
    also have
      "(\<lambda>n. of_nat n * (of_nat (n - Suc 0) * norm (c n) * inverse r) *
           r ^ (n - Suc 0)) =
       (\<lambda>n. norm (c n) * of_nat n * of_nat (n - Suc 0) * r ^ (n - 2))"
      apply (rule ext)
      apply (case_tac "n", simp)
      apply (rename_tac nat)
      apply (case_tac "nat", simp)
      apply (simp add: r_neq_0)
      done
    finally
    show "summable (\<lambda>n. norm (c n) * of_nat n * of_nat (n - Suc 0) * r ^ (n - 2))" .
  next
    fix h::'a and n::nat
    assume h: "h \<noteq> 0"
    assume "norm h < r - norm x"
    hence "norm x + norm h < r" by simp
    with norm_triangle_ineq have xh: "norm (x + h) < r"
      by (rule order_le_less_trans)
    show "norm (c n * (((x + h) ^ n - x ^ n) / h - of_nat n * x ^ (n - Suc 0)))
          \<le> norm (c n) * of_nat n * of_nat (n - Suc 0) * r ^ (n - 2) * norm h"
      apply (simp only: norm_mult mult_assoc)
      apply (rule mult_left_mono [OF _ norm_ge_zero])
      apply (simp add: mult_assoc [symmetric])
      apply (metis h lemma_termdiff3 less_eq_real_def r1 xh)
      done
  qed
qed

lemma termdiffs:
  fixes K x :: "'a::{real_normed_field,banach}"
  assumes 1: "summable (\<lambda>n. c n * K ^ n)"
      and 2: "summable (\<lambda>n. (diffs c) n * K ^ n)"
      and 3: "summable (\<lambda>n. (diffs (diffs c)) n * K ^ n)"
      and 4: "norm x < norm K"
  shows "DERIV (\<lambda>x. \<Sum>n. c n * x ^ n) x :> (\<Sum>n. (diffs c) n * x ^ n)"
  unfolding deriv_def
proof (rule LIM_zero_cancel)
  show "(\<lambda>h. (suminf (\<lambda>n. c n * (x + h) ^ n) - suminf (\<lambda>n. c n * x ^ n)) / h
            - suminf (\<lambda>n. diffs c n * x ^ n)) -- 0 --> 0"
  proof (rule LIM_equal2)
    show "0 < norm K - norm x" using 4 by (simp add: less_diff_eq)
  next
    fix h :: 'a
    assume "norm (h - 0) < norm K - norm x"
    hence "norm x + norm h < norm K" by simp
    hence 5: "norm (x + h) < norm K"
      by (rule norm_triangle_ineq [THEN order_le_less_trans])
    have "summable (\<lambda>n. c n * x ^ n)"
      and "summable (\<lambda>n. c n * (x + h) ^ n)"
      and "summable (\<lambda>n. diffs c n * x ^ n)"
      using 1 2 4 5 by (auto elim: powser_inside)
    then have "((\<Sum>n. c n * (x + h) ^ n) - (\<Sum>n. c n * x ^ n)) / h - (\<Sum>n. diffs c n * x ^ n) =
          (\<Sum>n. (c n * (x + h) ^ n - c n * x ^ n) / h - of_nat n * c n * x ^ (n - Suc 0))"
      by (intro sums_unique sums_diff sums_divide diffs_equiv summable_sums)
    then show "((\<Sum>n. c n * (x + h) ^ n) - (\<Sum>n. c n * x ^ n)) / h - (\<Sum>n. diffs c n * x ^ n) =
          (\<Sum>n. c n * (((x + h) ^ n - x ^ n) / h - of_nat n * x ^ (n - Suc 0)))"
      by (simp add: algebra_simps)
  next
    show "(\<lambda>h. \<Sum>n. c n * (((x + h) ^ n - x ^ n) / h - of_nat n * x ^ (n - Suc 0))) -- 0 --> 0"
      by (rule termdiffs_aux [OF 3 4])
  qed
qed


subsection {* Derivability of power series *}

lemma DERIV_series':
  fixes f :: "real \<Rightarrow> nat \<Rightarrow> real"
  assumes DERIV_f: "\<And> n. DERIV (\<lambda> x. f x n) x0 :> (f' x0 n)"
    and allf_summable: "\<And> x. x \<in> {a <..< b} \<Longrightarrow> summable (f x)" and x0_in_I: "x0 \<in> {a <..< b}"
    and "summable (f' x0)"
    and "summable L"
    and L_def: "\<And>n x y. \<lbrakk> x \<in> { a <..< b} ; y \<in> { a <..< b} \<rbrakk> \<Longrightarrow> \<bar>f x n - f y n\<bar> \<le> L n * \<bar>x - y\<bar>"
  shows "DERIV (\<lambda> x. suminf (f x)) x0 :> (suminf (f' x0))"
  unfolding deriv_def
proof (rule LIM_I)
  fix r :: real
  assume "0 < r" hence "0 < r/3" by auto

  obtain N_L where N_L: "\<And> n. N_L \<le> n \<Longrightarrow> \<bar> \<Sum> i. L (i + n) \<bar> < r/3"
    using suminf_exist_split[OF `0 < r/3` `summable L`] by auto

  obtain N_f' where N_f': "\<And> n. N_f' \<le> n \<Longrightarrow> \<bar> \<Sum> i. f' x0 (i + n) \<bar> < r/3"
    using suminf_exist_split[OF `0 < r/3` `summable (f' x0)`] by auto

  let ?N = "Suc (max N_L N_f')"
  have "\<bar> \<Sum> i. f' x0 (i + ?N) \<bar> < r/3" (is "?f'_part < r/3") and
    L_estimate: "\<bar> \<Sum> i. L (i + ?N) \<bar> < r/3" using N_L[of "?N"] and N_f' [of "?N"] by auto

  let ?diff = "\<lambda>i x. (f (x0 + x) i - f x0 i) / x"

  let ?r = "r / (3 * real ?N)"
  have "0 < 3 * real ?N" by auto
  from divide_pos_pos[OF `0 < r` this]
  have "0 < ?r" .

  let "?s n" = "SOME s. 0 < s \<and> (\<forall> x. x \<noteq> 0 \<and> \<bar> x \<bar> < s \<longrightarrow> \<bar> ?diff n x - f' x0 n \<bar> < ?r)"
  def S' \<equiv> "Min (?s ` { 0 ..< ?N })"

  have "0 < S'" unfolding S'_def
  proof (rule iffD2[OF Min_gr_iff])
    show "\<forall>x \<in> (?s ` { 0 ..< ?N }). 0 < x"
    proof
      fix x
      assume "x \<in> ?s ` {0..<?N}"
      then obtain n where "x = ?s n" and "n \<in> {0..<?N}"
        using image_iff[THEN iffD1] by blast
      from DERIV_D[OF DERIV_f[where n=n], THEN LIM_D, OF `0 < ?r`, unfolded real_norm_def]
      obtain s where s_bound: "0 < s \<and> (\<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < s \<longrightarrow> \<bar>?diff n x - f' x0 n\<bar> < ?r)"
        by auto
      have "0 < ?s n" by (rule someI2[where a=s]) (auto simp add: s_bound)
      thus "0 < x" unfolding `x = ?s n` .
    qed
  qed auto

  def S \<equiv> "min (min (x0 - a) (b - x0)) S'"
  hence "0 < S" and S_a: "S \<le> x0 - a" and S_b: "S \<le> b - x0"
    and "S \<le> S'" using x0_in_I and `0 < S'`
    by auto

  {
    fix x
    assume "x \<noteq> 0" and "\<bar> x \<bar> < S"
    hence x_in_I: "x0 + x \<in> { a <..< b }"
      using S_a S_b by auto

    note diff_smbl = summable_diff[OF allf_summable[OF x_in_I] allf_summable[OF x0_in_I]]
    note div_smbl = summable_divide[OF diff_smbl]
    note all_smbl = summable_diff[OF div_smbl `summable (f' x0)`]
    note ign = summable_ignore_initial_segment[where k="?N"]
    note diff_shft_smbl = summable_diff[OF ign[OF allf_summable[OF x_in_I]] ign[OF allf_summable[OF x0_in_I]]]
    note div_shft_smbl = summable_divide[OF diff_shft_smbl]
    note all_shft_smbl = summable_diff[OF div_smbl ign[OF `summable (f' x0)`]]

    {
      fix n
      have "\<bar> ?diff (n + ?N) x \<bar> \<le> L (n + ?N) * \<bar> (x0 + x) - x0 \<bar> / \<bar> x \<bar>"
        using divide_right_mono[OF L_def[OF x_in_I x0_in_I] abs_ge_zero]
        unfolding abs_divide .
      hence "\<bar> (\<bar>?diff (n + ?N) x \<bar>) \<bar> \<le> L (n + ?N)"
        using `x \<noteq> 0` by auto
    } note L_ge = summable_le2[OF allI[OF this] ign[OF `summable L`]]
    from order_trans[OF summable_rabs[OF conjunct1[OF L_ge]] L_ge[THEN conjunct2]]
    have "\<bar> \<Sum> i. ?diff (i + ?N) x \<bar> \<le> (\<Sum> i. L (i + ?N))" .
    hence "\<bar> \<Sum> i. ?diff (i + ?N) x \<bar> \<le> r / 3" (is "?L_part \<le> r/3")
      using L_estimate by auto

    have "\<bar>\<Sum>n \<in> { 0 ..< ?N}. ?diff n x - f' x0 n \<bar> \<le>
      (\<Sum>n \<in> { 0 ..< ?N}. \<bar>?diff n x - f' x0 n \<bar>)" ..
    also have "\<dots> < (\<Sum>n \<in> { 0 ..< ?N}. ?r)"
    proof (rule setsum_strict_mono)
      fix n
      assume "n \<in> { 0 ..< ?N}"
      have "\<bar>x\<bar> < S" using `\<bar>x\<bar> < S` .
      also have "S \<le> S'" using `S \<le> S'` .
      also have "S' \<le> ?s n" unfolding S'_def
      proof (rule Min_le_iff[THEN iffD2])
        have "?s n \<in> (?s ` {0..<?N}) \<and> ?s n \<le> ?s n"
          using `n \<in> { 0 ..< ?N}` by auto
        thus "\<exists> a \<in> (?s ` {0..<?N}). a \<le> ?s n" by blast
      qed auto
      finally have "\<bar>x\<bar> < ?s n" .

      from DERIV_D[OF DERIV_f[where n=n], THEN LIM_D, OF `0 < ?r`, unfolded real_norm_def diff_0_right, unfolded some_eq_ex[symmetric], THEN conjunct2]
      have "\<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < ?s n \<longrightarrow> \<bar>?diff n x - f' x0 n\<bar> < ?r" .
      with `x \<noteq> 0` and `\<bar>x\<bar> < ?s n` show "\<bar>?diff n x - f' x0 n\<bar> < ?r"
        by blast
    qed auto
    also have "\<dots> = of_nat (card {0 ..< ?N}) * ?r"
      by (rule setsum_constant)
    also have "\<dots> = real ?N * ?r"
      unfolding real_eq_of_nat by auto
    also have "\<dots> = r/3" by auto
    finally have "\<bar>\<Sum>n \<in> { 0 ..< ?N}. ?diff n x - f' x0 n \<bar> < r / 3" (is "?diff_part < r / 3") .

    from suminf_diff[OF allf_summable[OF x_in_I] allf_summable[OF x0_in_I]]
    have "\<bar>(suminf (f (x0 + x)) - (suminf (f x0))) / x - suminf (f' x0)\<bar> =
        \<bar>\<Sum>n. ?diff n x - f' x0 n\<bar>"
      unfolding suminf_diff[OF div_smbl `summable (f' x0)`, symmetric]
      using suminf_divide[OF diff_smbl, symmetric] by auto
    also have "\<dots> \<le> ?diff_part + \<bar> (\<Sum>n. ?diff (n + ?N) x) - (\<Sum> n. f' x0 (n + ?N)) \<bar>"
      unfolding suminf_split_initial_segment[OF all_smbl, where k="?N"]
      unfolding suminf_diff[OF div_shft_smbl ign[OF `summable (f' x0)`]]
      by (rule abs_triangle_ineq)
    also have "\<dots> \<le> ?diff_part + ?L_part + ?f'_part"
      using abs_triangle_ineq4 by auto
    also have "\<dots> < r /3 + r/3 + r/3"
      using `?diff_part < r/3` `?L_part \<le> r/3` and `?f'_part < r/3`
      by (rule add_strict_mono [OF add_less_le_mono])
    finally have "\<bar>(suminf (f (x0 + x)) - suminf (f x0)) / x - suminf (f' x0)\<bar> < r"
      by auto
  }
  thus "\<exists> s > 0. \<forall> x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow>
      norm (((\<Sum>n. f (x0 + x) n) - (\<Sum>n. f x0 n)) / x - (\<Sum>n. f' x0 n)) < r"
    using `0 < S` unfolding real_norm_def diff_0_right by blast
qed

lemma DERIV_power_series':
  fixes f :: "nat \<Rightarrow> real"
  assumes converges: "\<And> x. x \<in> {-R <..< R} \<Longrightarrow> summable (\<lambda> n. f n * real (Suc n) * x^n)"
    and x0_in_I: "x0 \<in> {-R <..< R}" and "0 < R"
  shows "DERIV (\<lambda> x. (\<Sum> n. f n * x^(Suc n))) x0 :> (\<Sum> n. f n * real (Suc n) * x0^n)"
  (is "DERIV (\<lambda> x. (suminf (?f x))) x0 :> (suminf (?f' x0))")
proof -
  {
    fix R'
    assume "0 < R'" and "R' < R" and "-R' < x0" and "x0 < R'"
    hence "x0 \<in> {-R' <..< R'}" and "R' \<in> {-R <..< R}" and "x0 \<in> {-R <..< R}"
      by auto
    have "DERIV (\<lambda> x. (suminf (?f x))) x0 :> (suminf (?f' x0))"
    proof (rule DERIV_series')
      show "summable (\<lambda> n. \<bar>f n * real (Suc n) * R'^n\<bar>)"
      proof -
        have "(R' + R) / 2 < R" and "0 < (R' + R) / 2"
          using `0 < R'` `0 < R` `R' < R` by auto
        hence in_Rball: "(R' + R) / 2 \<in> {-R <..< R}"
          using `R' < R` by auto
        have "norm R' < norm ((R' + R) / 2)"
          using `0 < R'` `0 < R` `R' < R` by auto
        from powser_insidea[OF converges[OF in_Rball] this] show ?thesis
          by auto
      qed
      {
        fix n x y
        assume "x \<in> {-R' <..< R'}" and "y \<in> {-R' <..< R'}"
        show "\<bar>?f x n - ?f y n\<bar> \<le> \<bar>f n * real (Suc n) * R'^n\<bar> * \<bar>x-y\<bar>"
        proof -
          have "\<bar>f n * x ^ (Suc n) - f n * y ^ (Suc n)\<bar> =
            (\<bar>f n\<bar> * \<bar>x-y\<bar>) * \<bar>\<Sum>p = 0..<Suc n. x ^ p * y ^ (n - p)\<bar>"
            unfolding right_diff_distrib[symmetric] lemma_realpow_diff_sumr2 abs_mult
            by auto
          also have "\<dots> \<le> (\<bar>f n\<bar> * \<bar>x-y\<bar>) * (\<bar>real (Suc n)\<bar> * \<bar>R' ^ n\<bar>)"
          proof (rule mult_left_mono)
            have "\<bar>\<Sum>p = 0..<Suc n. x ^ p * y ^ (n - p)\<bar> \<le> (\<Sum>p = 0..<Suc n. \<bar>x ^ p * y ^ (n - p)\<bar>)"
              by (rule setsum_abs)
            also have "\<dots> \<le> (\<Sum>p = 0..<Suc n. R' ^ n)"
            proof (rule setsum_mono)
              fix p
              assume "p \<in> {0..<Suc n}"
              hence "p \<le> n" by auto
              {
                fix n
                fix x :: real
                assume "x \<in> {-R'<..<R'}"
                hence "\<bar>x\<bar> \<le> R'"  by auto
                hence "\<bar>x^n\<bar> \<le> R'^n"
                  unfolding power_abs by (rule power_mono, auto)
              }
              from mult_mono[OF this[OF `x \<in> {-R'<..<R'}`, of p] this[OF `y \<in> {-R'<..<R'}`, of "n-p"]] `0 < R'`
              have "\<bar>x^p * y^(n-p)\<bar> \<le> R'^p * R'^(n-p)"
                unfolding abs_mult by auto
              thus "\<bar>x^p * y^(n-p)\<bar> \<le> R'^n"
                unfolding power_add[symmetric] using `p \<le> n` by auto
            qed
            also have "\<dots> = real (Suc n) * R' ^ n"
              unfolding setsum_constant card_atLeastLessThan real_of_nat_def by auto
            finally show "\<bar>\<Sum>p = 0..<Suc n. x ^ p * y ^ (n - p)\<bar> \<le> \<bar>real (Suc n)\<bar> * \<bar>R' ^ n\<bar>"
              unfolding abs_real_of_nat_cancel abs_of_nonneg[OF zero_le_power[OF less_imp_le[OF `0 < R'`]]] .
            show "0 \<le> \<bar>f n\<bar> * \<bar>x - y\<bar>"
              unfolding abs_mult[symmetric] by auto
          qed
          also have "\<dots> = \<bar>f n * real (Suc n) * R' ^ n\<bar> * \<bar>x - y\<bar>"
            unfolding abs_mult mult_assoc[symmetric] by algebra
          finally show ?thesis .
        qed
      }
      {
        fix n
        show "DERIV (\<lambda> x. ?f x n) x0 :> (?f' x0 n)"
          by (auto intro!: DERIV_intros simp del: power_Suc)
      }
      {
        fix x
        assume "x \<in> {-R' <..< R'}"
        hence "R' \<in> {-R <..< R}" and "norm x < norm R'"
          using assms `R' < R` by auto
        have "summable (\<lambda> n. f n * x^n)"
        proof (rule summable_le2[THEN conjunct1, OF _ powser_insidea[OF converges[OF `R' \<in> {-R <..< R}`] `norm x < norm R'`]], rule allI)
          fix n
          have le: "\<bar>f n\<bar> * 1 \<le> \<bar>f n\<bar> * real (Suc n)"
            by (rule mult_left_mono) auto
          show "\<bar>f n * x ^ n\<bar> \<le> norm (f n * real (Suc n) * x ^ n)"
            unfolding real_norm_def abs_mult
            by (rule mult_right_mono) (auto simp add: le[unfolded mult_1_right])
        qed
        from this[THEN summable_mult2[where c=x], unfolded mult_assoc, unfolded mult_commute]
        show "summable (?f x)" by auto
      }
      show "summable (?f' x0)"
        using converges[OF `x0 \<in> {-R <..< R}`] .
      show "x0 \<in> {-R' <..< R'}"
        using `x0 \<in> {-R' <..< R'}` .
    qed
  } note for_subinterval = this
  let ?R = "(R + \<bar>x0\<bar>) / 2"
  have "\<bar>x0\<bar> < ?R" using assms by auto
  hence "- ?R < x0"
  proof (cases "x0 < 0")
    case True
    hence "- x0 < ?R" using `\<bar>x0\<bar> < ?R` by auto
    thus ?thesis unfolding neg_less_iff_less[symmetric, of "- x0"] by auto
  next
    case False
    have "- ?R < 0" using assms by auto
    also have "\<dots> \<le> x0" using False by auto
    finally show ?thesis .
  qed
  hence "0 < ?R" "?R < R" "- ?R < x0" and "x0 < ?R"
    using assms by auto
  from for_subinterval[OF this]
  show ?thesis .
qed


subsection {* Exponential Function *}

definition exp :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  where "exp = (\<lambda>x. \<Sum>n. x ^ n /\<^sub>R real (fact n))"

lemma summable_exp_generic:
  fixes x :: "'a::{real_normed_algebra_1,banach}"
  defines S_def: "S \<equiv> \<lambda>n. x ^ n /\<^sub>R real (fact n)"
  shows "summable S"
proof -
  have S_Suc: "\<And>n. S (Suc n) = (x * S n) /\<^sub>R real (Suc n)"
    unfolding S_def by (simp del: mult_Suc)
  obtain r :: real where r0: "0 < r" and r1: "r < 1"
    using dense [OF zero_less_one] by fast
  obtain N :: nat where N: "norm x < real N * r"
    using reals_Archimedean3 [OF r0] by fast
  from r1 show ?thesis
  proof (rule ratio_test [rule_format])
    fix n :: nat
    assume n: "N \<le> n"
    have "norm x \<le> real N * r"
      using N by (rule order_less_imp_le)
    also have "real N * r \<le> real (Suc n) * r"
      using r0 n by (simp add: mult_right_mono)
    finally have "norm x * norm (S n) \<le> real (Suc n) * r * norm (S n)"
      using norm_ge_zero by (rule mult_right_mono)
    hence "norm (x * S n) \<le> real (Suc n) * r * norm (S n)"
      by (rule order_trans [OF norm_mult_ineq])
    hence "norm (x * S n) / real (Suc n) \<le> r * norm (S n)"
      by (simp add: pos_divide_le_eq mult_ac)
    thus "norm (S (Suc n)) \<le> r * norm (S n)"
      by (simp add: S_Suc inverse_eq_divide)
  qed
qed

lemma summable_norm_exp:
  fixes x :: "'a::{real_normed_algebra_1,banach}"
  shows "summable (\<lambda>n. norm (x ^ n /\<^sub>R real (fact n)))"
proof (rule summable_norm_comparison_test [OF exI, rule_format])
  show "summable (\<lambda>n. norm x ^ n /\<^sub>R real (fact n))"
    by (rule summable_exp_generic)
  fix n
  show "norm (x ^ n /\<^sub>R real (fact n)) \<le> norm x ^ n /\<^sub>R real (fact n)"
    by (simp add: norm_power_ineq)
qed

lemma summable_exp: "summable (\<lambda>n. inverse (real (fact n)) * x ^ n)"
  using summable_exp_generic [where x=x] by simp

lemma exp_converges: "(\<lambda>n. x ^ n /\<^sub>R real (fact n)) sums exp x"
  unfolding exp_def by (rule summable_exp_generic [THEN summable_sums])


lemma exp_fdiffs:
      "diffs (\<lambda>n. inverse(real (fact n))) = (\<lambda>n. inverse(real (fact n)))"
  by (simp add: diffs_def mult_assoc [symmetric] real_of_nat_def of_nat_mult
        del: mult_Suc of_nat_Suc)

lemma diffs_of_real: "diffs (\<lambda>n. of_real (f n)) = (\<lambda>n. of_real (diffs f n))"
  by (simp add: diffs_def)

lemma DERIV_exp [simp]: "DERIV exp x :> exp(x)"
  unfolding exp_def scaleR_conv_of_real
  apply (rule DERIV_cong)
  apply (rule termdiffs [where K="of_real (1 + norm x)"])
  apply (simp_all only: diffs_of_real scaleR_conv_of_real exp_fdiffs)
  apply (rule exp_converges [THEN sums_summable, unfolded scaleR_conv_of_real])+
  apply (simp del: of_real_add)
  done

declare DERIV_exp[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]

lemma isCont_exp: "isCont exp x"
  by (rule DERIV_exp [THEN DERIV_isCont])

lemma isCont_exp' [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. exp (f x)) a"
  by (rule isCont_o2 [OF _ isCont_exp])

lemma tendsto_exp [tendsto_intros]:
  "(f ---> a) F \<Longrightarrow> ((\<lambda>x. exp (f x)) ---> exp a) F"
  by (rule isCont_tendsto_compose [OF isCont_exp])

lemma continuous_exp [continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. exp (f x))"
  unfolding continuous_def by (rule tendsto_exp)

lemma continuous_on_exp [continuous_on_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. exp (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_exp)


subsubsection {* Properties of the Exponential Function *}

lemma powser_zero:
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_algebra_1}"
  shows "(\<Sum>n. f n * 0 ^ n) = f 0"
proof -
  have "(\<Sum>n = 0..<1. f n * 0 ^ n) = (\<Sum>n. f n * 0 ^ n)"
    by (rule sums_unique [OF series_zero], simp add: power_0_left)
  thus ?thesis unfolding One_nat_def by simp
qed

lemma exp_zero [simp]: "exp 0 = 1"
  unfolding exp_def by (simp add: scaleR_conv_of_real powser_zero)

lemma setsum_cl_ivl_Suc2:
  "(\<Sum>i=m..Suc n. f i) = (if Suc n < m then 0 else f m + (\<Sum>i=m..n. f (Suc i)))"
  by (simp add: setsum_head_Suc setsum_shift_bounds_cl_Suc_ivl
           del: setsum_cl_ivl_Suc)

lemma exp_series_add:
  fixes x y :: "'a::{real_field}"
  defines S_def: "S \<equiv> \<lambda>x n. x ^ n /\<^sub>R real (fact n)"
  shows "S (x + y) n = (\<Sum>i=0..n. S x i * S y (n - i))"
proof (induct n)
  case 0
  show ?case
    unfolding S_def by simp
next
  case (Suc n)
  have S_Suc: "\<And>x n. S x (Suc n) = (x * S x n) /\<^sub>R real (Suc n)"
    unfolding S_def by (simp del: mult_Suc)
  hence times_S: "\<And>x n. x * S x n = real (Suc n) *\<^sub>R S x (Suc n)"
    by simp

  have "real (Suc n) *\<^sub>R S (x + y) (Suc n) = (x + y) * S (x + y) n"
    by (simp only: times_S)
  also have "\<dots> = (x + y) * (\<Sum>i=0..n. S x i * S y (n-i))"
    by (simp only: Suc)
  also have "\<dots> = x * (\<Sum>i=0..n. S x i * S y (n-i))
                + y * (\<Sum>i=0..n. S x i * S y (n-i))"
    by (rule distrib_right)
  also have "\<dots> = (\<Sum>i=0..n. (x * S x i) * S y (n-i))
                + (\<Sum>i=0..n. S x i * (y * S y (n-i)))"
    by (simp only: setsum_right_distrib mult_ac)
  also have "\<dots> = (\<Sum>i=0..n. real (Suc i) *\<^sub>R (S x (Suc i) * S y (n-i)))
                + (\<Sum>i=0..n. real (Suc n-i) *\<^sub>R (S x i * S y (Suc n-i)))"
    by (simp add: times_S Suc_diff_le)
  also have "(\<Sum>i=0..n. real (Suc i) *\<^sub>R (S x (Suc i) * S y (n-i))) =
             (\<Sum>i=0..Suc n. real i *\<^sub>R (S x i * S y (Suc n-i)))"
    by (subst setsum_cl_ivl_Suc2, simp)
  also have "(\<Sum>i=0..n. real (Suc n-i) *\<^sub>R (S x i * S y (Suc n-i))) =
             (\<Sum>i=0..Suc n. real (Suc n-i) *\<^sub>R (S x i * S y (Suc n-i)))"
    by (subst setsum_cl_ivl_Suc, simp)
  also have "(\<Sum>i=0..Suc n. real i *\<^sub>R (S x i * S y (Suc n-i))) +
             (\<Sum>i=0..Suc n. real (Suc n-i) *\<^sub>R (S x i * S y (Suc n-i))) =
             (\<Sum>i=0..Suc n. real (Suc n) *\<^sub>R (S x i * S y (Suc n-i)))"
    by (simp only: setsum_addf [symmetric] scaleR_left_distrib [symmetric]
              real_of_nat_add [symmetric], simp)
  also have "\<dots> = real (Suc n) *\<^sub>R (\<Sum>i=0..Suc n. S x i * S y (Suc n-i))"
    by (simp only: scaleR_right.setsum)
  finally show
    "S (x + y) (Suc n) = (\<Sum>i=0..Suc n. S x i * S y (Suc n - i))"
    by (simp del: setsum_cl_ivl_Suc)
qed

lemma exp_add: "exp (x + y) = exp x * exp y"
  unfolding exp_def
  by (simp only: Cauchy_product summable_norm_exp exp_series_add)

lemma mult_exp_exp: "exp x * exp y = exp (x + y)"
  by (rule exp_add [symmetric])

lemma exp_of_real: "exp (of_real x) = of_real (exp x)"
  unfolding exp_def
  apply (subst suminf_of_real)
  apply (rule summable_exp_generic)
  apply (simp add: scaleR_conv_of_real)
  done

lemma exp_not_eq_zero [simp]: "exp x \<noteq> 0"
proof
  have "exp x * exp (- x) = 1" by (simp add: mult_exp_exp)
  also assume "exp x = 0"
  finally show "False" by simp
qed

lemma exp_minus: "exp (- x) = inverse (exp x)"
  by (rule inverse_unique [symmetric], simp add: mult_exp_exp)

lemma exp_diff: "exp (x - y) = exp x / exp y"
  using exp_add [of x "- y"] by (simp add: exp_minus divide_inverse)


subsubsection {* Properties of the Exponential Function on Reals *}

text {* Comparisons of @{term "exp x"} with zero. *}

text{*Proof: because every exponential can be seen as a square.*}
lemma exp_ge_zero [simp]: "0 \<le> exp (x::real)"
proof -
  have "0 \<le> exp (x/2) * exp (x/2)" by simp
  thus ?thesis by (simp add: exp_add [symmetric])
qed

lemma exp_gt_zero [simp]: "0 < exp (x::real)"
  by (simp add: order_less_le)

lemma not_exp_less_zero [simp]: "\<not> exp (x::real) < 0"
  by (simp add: not_less)

lemma not_exp_le_zero [simp]: "\<not> exp (x::real) \<le> 0"
  by (simp add: not_le)

lemma abs_exp_cancel [simp]: "\<bar>exp x::real\<bar> = exp x"
  by simp

lemma exp_real_of_nat_mult: "exp(real n * x) = exp(x) ^ n"
  by (induct n) (auto simp add: real_of_nat_Suc distrib_left exp_add mult_commute)

text {* Strict monotonicity of exponential. *}

lemma exp_ge_add_one_self_aux: 
  assumes "0 \<le> (x::real)" shows "1+x \<le> exp(x)"
using order_le_imp_less_or_eq [OF assms]
proof 
  assume "0 < x"
  have "1+x \<le> (\<Sum>n = 0..<2. inverse (real (fact n)) * x ^ n)"
    by (auto simp add: numeral_2_eq_2)
  also have "... \<le> (\<Sum>n. inverse (real (fact n)) * x ^ n)"
    apply (rule series_pos_le [OF summable_exp])
    using `0 < x`
    apply (auto  simp add:  zero_le_mult_iff)
    done
  finally show "1+x \<le> exp x" 
    by (simp add: exp_def)
next
  assume "0 = x"
  then show "1 + x \<le> exp x"
    by auto
qed

lemma exp_gt_one: "0 < (x::real) \<Longrightarrow> 1 < exp x"
proof -
  assume x: "0 < x"
  hence "1 < 1 + x" by simp
  also from x have "1 + x \<le> exp x"
    by (simp add: exp_ge_add_one_self_aux)
  finally show ?thesis .
qed

lemma exp_less_mono:
  fixes x y :: real
  assumes "x < y"
  shows "exp x < exp y"
proof -
  from `x < y` have "0 < y - x" by simp
  hence "1 < exp (y - x)" by (rule exp_gt_one)
  hence "1 < exp y / exp x" by (simp only: exp_diff)
  thus "exp x < exp y" by simp
qed

lemma exp_less_cancel: "exp (x::real) < exp y \<Longrightarrow> x < y"
  unfolding linorder_not_le [symmetric]
  by (auto simp add: order_le_less exp_less_mono)

lemma exp_less_cancel_iff [iff]: "exp (x::real) < exp y \<longleftrightarrow> x < y"
  by (auto intro: exp_less_mono exp_less_cancel)

lemma exp_le_cancel_iff [iff]: "exp (x::real) \<le> exp y \<longleftrightarrow> x \<le> y"
  by (auto simp add: linorder_not_less [symmetric])

lemma exp_inj_iff [iff]: "exp (x::real) = exp y \<longleftrightarrow> x = y"
  by (simp add: order_eq_iff)

text {* Comparisons of @{term "exp x"} with one. *}

lemma one_less_exp_iff [simp]: "1 < exp (x::real) \<longleftrightarrow> 0 < x"
  using exp_less_cancel_iff [where x=0 and y=x] by simp

lemma exp_less_one_iff [simp]: "exp (x::real) < 1 \<longleftrightarrow> x < 0"
  using exp_less_cancel_iff [where x=x and y=0] by simp

lemma one_le_exp_iff [simp]: "1 \<le> exp (x::real) \<longleftrightarrow> 0 \<le> x"
  using exp_le_cancel_iff [where x=0 and y=x] by simp

lemma exp_le_one_iff [simp]: "exp (x::real) \<le> 1 \<longleftrightarrow> x \<le> 0"
  using exp_le_cancel_iff [where x=x and y=0] by simp

lemma exp_eq_one_iff [simp]: "exp (x::real) = 1 \<longleftrightarrow> x = 0"
  using exp_inj_iff [where x=x and y=0] by simp

lemma lemma_exp_total: "1 \<le> y \<Longrightarrow> \<exists>x. 0 \<le> x & x \<le> y - 1 & exp(x::real) = y"
proof (rule IVT)
  assume "1 \<le> y"
  hence "0 \<le> y - 1" by simp
  hence "1 + (y - 1) \<le> exp (y - 1)" by (rule exp_ge_add_one_self_aux)
  thus "y \<le> exp (y - 1)" by simp
qed (simp_all add: le_diff_eq)

lemma exp_total: "0 < (y::real) \<Longrightarrow> \<exists>x. exp x = y"
proof (rule linorder_le_cases [of 1 y])
  assume "1 \<le> y"
  thus "\<exists>x. exp x = y" by (fast dest: lemma_exp_total)
next
  assume "0 < y" and "y \<le> 1"
  hence "1 \<le> inverse y" by (simp add: one_le_inverse_iff)
  then obtain x where "exp x = inverse y" by (fast dest: lemma_exp_total)
  hence "exp (- x) = y" by (simp add: exp_minus)
  thus "\<exists>x. exp x = y" ..
qed


subsection {* Natural Logarithm *}

definition ln :: "real \<Rightarrow> real"
  where "ln x = (THE u. exp u = x)"

lemma ln_exp [simp]: "ln (exp x) = x"
  by (simp add: ln_def)

lemma exp_ln [simp]: "0 < x \<Longrightarrow> exp (ln x) = x"
  by (auto dest: exp_total)

lemma exp_ln_iff [simp]: "exp (ln x) = x \<longleftrightarrow> 0 < x"
  by (metis exp_gt_zero exp_ln)

lemma ln_unique: "exp y = x \<Longrightarrow> ln x = y"
  by (erule subst, rule ln_exp)

lemma ln_one [simp]: "ln 1 = 0"
  by (rule ln_unique) simp

lemma ln_mult: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln (x * y) = ln x + ln y"
  by (rule ln_unique) (simp add: exp_add)

lemma ln_inverse: "0 < x \<Longrightarrow> ln (inverse x) = - ln x"
  by (rule ln_unique) (simp add: exp_minus)

lemma ln_div: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln (x / y) = ln x - ln y"
  by (rule ln_unique) (simp add: exp_diff)

lemma ln_realpow: "0 < x \<Longrightarrow> ln (x ^ n) = real n * ln x"
  by (rule ln_unique) (simp add: exp_real_of_nat_mult)

lemma ln_less_cancel_iff [simp]: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln x < ln y \<longleftrightarrow> x < y"
  by (subst exp_less_cancel_iff [symmetric]) simp

lemma ln_le_cancel_iff [simp]: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln x \<le> ln y \<longleftrightarrow> x \<le> y"
  by (simp add: linorder_not_less [symmetric])

lemma ln_inj_iff [simp]: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln x = ln y \<longleftrightarrow> x = y"
  by (simp add: order_eq_iff)

lemma ln_add_one_self_le_self [simp]: "0 \<le> x \<Longrightarrow> ln (1 + x) \<le> x"
  apply (rule exp_le_cancel_iff [THEN iffD1])
  apply (simp add: exp_ge_add_one_self_aux)
  done

lemma ln_less_self [simp]: "0 < x \<Longrightarrow> ln x < x"
  by (rule order_less_le_trans [where y="ln (1 + x)"]) simp_all

lemma ln_ge_zero [simp]: "1 \<le> x \<Longrightarrow> 0 \<le> ln x"
  using ln_le_cancel_iff [of 1 x] by simp

lemma ln_ge_zero_imp_ge_one: "0 \<le> ln x \<Longrightarrow> 0 < x \<Longrightarrow> 1 \<le> x"
  using ln_le_cancel_iff [of 1 x] by simp

lemma ln_ge_zero_iff [simp]: "0 < x \<Longrightarrow> 0 \<le> ln x \<longleftrightarrow> 1 \<le> x"
  using ln_le_cancel_iff [of 1 x] by simp

lemma ln_less_zero_iff [simp]: "0 < x \<Longrightarrow> ln x < 0 \<longleftrightarrow> x < 1"
  using ln_less_cancel_iff [of x 1] by simp

lemma ln_gt_zero: "1 < x \<Longrightarrow> 0 < ln x"
  using ln_less_cancel_iff [of 1 x] by simp

lemma ln_gt_zero_imp_gt_one: "0 < ln x \<Longrightarrow> 0 < x \<Longrightarrow> 1 < x"
  using ln_less_cancel_iff [of 1 x] by simp

lemma ln_gt_zero_iff [simp]: "0 < x \<Longrightarrow> 0 < ln x \<longleftrightarrow> 1 < x"
  using ln_less_cancel_iff [of 1 x] by simp

lemma ln_eq_zero_iff [simp]: "0 < x \<Longrightarrow> ln x = 0 \<longleftrightarrow> x = 1"
  using ln_inj_iff [of x 1] by simp

lemma ln_less_zero: "0 < x \<Longrightarrow> x < 1 \<Longrightarrow> ln x < 0"
  by simp

lemma isCont_ln: "0 < x \<Longrightarrow> isCont ln x"
  apply (subgoal_tac "isCont ln (exp (ln x))", simp)
  apply (rule isCont_inverse_function [where f=exp], simp_all)
  done

lemma tendsto_ln [tendsto_intros]:
  "(f ---> a) F \<Longrightarrow> 0 < a \<Longrightarrow> ((\<lambda>x. ln (f x)) ---> ln a) F"
  by (rule isCont_tendsto_compose [OF isCont_ln])

lemma continuous_ln:
  "continuous F f \<Longrightarrow> 0 < f (Lim F (\<lambda>x. x)) \<Longrightarrow> continuous F (\<lambda>x. ln (f x))"
  unfolding continuous_def by (rule tendsto_ln)

lemma isCont_ln' [continuous_intros]:
  "continuous (at x) f \<Longrightarrow> 0 < f x \<Longrightarrow> continuous (at x) (\<lambda>x. ln (f x))"
  unfolding continuous_at by (rule tendsto_ln)

lemma continuous_within_ln [continuous_intros]:
  "continuous (at x within s) f \<Longrightarrow> 0 < f x \<Longrightarrow> continuous (at x within s) (\<lambda>x. ln (f x))"
  unfolding continuous_within by (rule tendsto_ln)

lemma continuous_on_ln [continuous_on_intros]:
  "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. 0 < f x) \<Longrightarrow> continuous_on s (\<lambda>x. ln (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_ln)

lemma DERIV_ln: "0 < x \<Longrightarrow> DERIV ln x :> inverse x"
  apply (rule DERIV_inverse_function [where f=exp and a=0 and b="x+1"])
  apply (auto intro: DERIV_cong [OF DERIV_exp exp_ln] isCont_ln)
  done

lemma DERIV_ln_divide: "0 < x \<Longrightarrow> DERIV ln x :> 1 / x"
  by (rule DERIV_ln[THEN DERIV_cong], simp, simp add: divide_inverse)

declare DERIV_ln_divide[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]

lemma ln_series:
  assumes "0 < x" and "x < 2"
  shows "ln x = (\<Sum> n. (-1)^n * (1 / real (n + 1)) * (x - 1)^(Suc n))"
  (is "ln x = suminf (?f (x - 1))")
proof -
  let ?f' = "\<lambda>x n. (-1)^n * (x - 1)^n"

  have "ln x - suminf (?f (x - 1)) = ln 1 - suminf (?f (1 - 1))"
  proof (rule DERIV_isconst3[where x=x])
    fix x :: real
    assume "x \<in> {0 <..< 2}"
    hence "0 < x" and "x < 2" by auto
    have "norm (1 - x) < 1"
      using `0 < x` and `x < 2` by auto
    have "1 / x = 1 / (1 - (1 - x))" by auto
    also have "\<dots> = (\<Sum> n. (1 - x)^n)"
      using geometric_sums[OF `norm (1 - x) < 1`] by (rule sums_unique)
    also have "\<dots> = suminf (?f' x)"
      unfolding power_mult_distrib[symmetric]
      by (rule arg_cong[where f=suminf], rule arg_cong[where f="op ^"], auto)
    finally have "DERIV ln x :> suminf (?f' x)"
      using DERIV_ln[OF `0 < x`] unfolding divide_inverse by auto
    moreover
    have repos: "\<And> h x :: real. h - 1 + x = h + x - 1" by auto
    have "DERIV (\<lambda>x. suminf (?f x)) (x - 1) :>
      (\<Sum>n. (-1)^n * (1 / real (n + 1)) * real (Suc n) * (x - 1) ^ n)"
    proof (rule DERIV_power_series')
      show "x - 1 \<in> {- 1<..<1}" and "(0 :: real) < 1"
        using `0 < x` `x < 2` by auto
      fix x :: real
      assume "x \<in> {- 1<..<1}"
      hence "norm (-x) < 1" by auto
      show "summable (\<lambda>n. -1 ^ n * (1 / real (n + 1)) * real (Suc n) * x ^ n)"
        unfolding One_nat_def
        by (auto simp add: power_mult_distrib[symmetric] summable_geometric[OF `norm (-x) < 1`])
    qed
    hence "DERIV (\<lambda>x. suminf (?f x)) (x - 1) :> suminf (?f' x)"
      unfolding One_nat_def by auto
    hence "DERIV (\<lambda>x. suminf (?f (x - 1))) x :> suminf (?f' x)"
      unfolding DERIV_iff repos .
    ultimately have "DERIV (\<lambda>x. ln x - suminf (?f (x - 1))) x :> (suminf (?f' x) - suminf (?f' x))"
      by (rule DERIV_diff)
    thus "DERIV (\<lambda>x. ln x - suminf (?f (x - 1))) x :> 0" by auto
  qed (auto simp add: assms)
  thus ?thesis by auto
qed

lemma exp_first_two_terms: "exp x = 1 + x + (\<Sum> n. inverse(fact (n+2)) * (x ^ (n+2)))"
proof -
  have "exp x = suminf (\<lambda>n. inverse(fact n) * (x ^ n))"
    by (simp add: exp_def)
  also from summable_exp have "... = (\<Sum> n::nat = 0 ..< 2. inverse(fact n) * (x ^ n)) +
      (\<Sum> n. inverse(fact(n+2)) * (x ^ (n+2)))" (is "_ = ?a + _")
    by (rule suminf_split_initial_segment)
  also have "?a = 1 + x"
    by (simp add: numeral_2_eq_2)
  finally show ?thesis .
qed

lemma exp_bound: "0 <= (x::real) \<Longrightarrow> x <= 1 \<Longrightarrow> exp x <= 1 + x + x\<^sup>2"
proof -
  assume a: "0 <= x"
  assume b: "x <= 1"
  {
    fix n :: nat
    have "2 * 2 ^ n \<le> fact (n + 2)"
      by (induct n) simp_all
    hence "real ((2::nat) * 2 ^ n) \<le> real (fact (n + 2))"
      by (simp only: real_of_nat_le_iff)
    hence "2 * 2 ^ n \<le> real (fact (n + 2))"
      by simp
    hence "inverse (fact (n + 2)) \<le> inverse (2 * 2 ^ n)"
      by (rule le_imp_inverse_le) simp
    hence "inverse (fact (n + 2)) \<le> 1/2 * (1/2)^n"
      by (simp add: power_inverse)
    hence "inverse (fact (n + 2)) * (x^n * x\<^sup>2) \<le> 1/2 * (1/2)^n * (1 * x\<^sup>2)"
      by (rule mult_mono)
        (rule mult_mono, simp_all add: power_le_one a b mult_nonneg_nonneg)
    hence "inverse (fact (n + 2)) * x ^ (n + 2) \<le> (x\<^sup>2/2) * ((1/2)^n)"
      unfolding power_add by (simp add: mult_ac del: fact_Suc) }
  note aux1 = this
  have "(\<lambda>n. x\<^sup>2 / 2 * (1 / 2) ^ n) sums (x\<^sup>2 / 2 * (1 / (1 - 1 / 2)))"
    by (intro sums_mult geometric_sums, simp)
  hence aux2: "(\<lambda>n. x\<^sup>2 / 2 * (1 / 2) ^ n) sums x\<^sup>2"
    by simp
  have "suminf (\<lambda>n. inverse(fact (n+2)) * (x ^ (n+2))) <= x\<^sup>2"
  proof -
    have "suminf (\<lambda>n. inverse(fact (n+2)) * (x ^ (n+2))) <=
        suminf (\<lambda>n. (x\<^sup>2/2) * ((1/2)^n))"
      apply (rule summable_le)
      apply (rule allI, rule aux1)
      apply (rule summable_exp [THEN summable_ignore_initial_segment])
      by (rule sums_summable, rule aux2)
    also have "... = x\<^sup>2"
      by (rule sums_unique [THEN sym], rule aux2)
    finally show ?thesis .
  qed
  thus ?thesis unfolding exp_first_two_terms by auto
qed

lemma ln_one_minus_pos_upper_bound: "0 <= x \<Longrightarrow> x < 1 \<Longrightarrow> ln (1 - x) <= - x"
proof -
  assume a: "0 <= (x::real)" and b: "x < 1"
  have "(1 - x) * (1 + x + x\<^sup>2) = (1 - x^3)"
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  also have "... <= 1"
    by (auto simp add: a)
  finally have "(1 - x) * (1 + x + x\<^sup>2) <= 1" .
  moreover have c: "0 < 1 + x + x\<^sup>2"
    by (simp add: add_pos_nonneg a)
  ultimately have "1 - x <= 1 / (1 + x + x\<^sup>2)"
    by (elim mult_imp_le_div_pos)
  also have "... <= 1 / exp x"
    by (metis a abs_one b exp_bound exp_gt_zero frac_le less_eq_real_def real_sqrt_abs 
              real_sqrt_pow2_iff real_sqrt_power)
  also have "... = exp (-x)"
    by (auto simp add: exp_minus divide_inverse)
  finally have "1 - x <= exp (- x)" .
  also have "1 - x = exp (ln (1 - x))"
    by (metis b diff_0 exp_ln_iff less_iff_diff_less_0 minus_diff_eq)
  finally have "exp (ln (1 - x)) <= exp (- x)" .
  thus ?thesis by (auto simp only: exp_le_cancel_iff)
qed

lemma exp_ge_add_one_self [simp]: "1 + (x::real) <= exp x"
  apply (case_tac "0 <= x")
  apply (erule exp_ge_add_one_self_aux)
  apply (case_tac "x <= -1")
  apply (subgoal_tac "1 + x <= 0")
  apply (erule order_trans)
  apply simp
  apply simp
  apply (subgoal_tac "1 + x = exp(ln (1 + x))")
  apply (erule ssubst)
  apply (subst exp_le_cancel_iff)
  apply (subgoal_tac "ln (1 - (- x)) <= - (- x)")
  apply simp
  apply (rule ln_one_minus_pos_upper_bound)
  apply auto
done

lemma ln_one_plus_pos_lower_bound: "0 <= x \<Longrightarrow> x <= 1 \<Longrightarrow> x - x\<^sup>2 <= ln (1 + x)"
proof -
  assume a: "0 <= x" and b: "x <= 1"
  have "exp (x - x\<^sup>2) = exp x / exp (x\<^sup>2)"
    by (rule exp_diff)
  also have "... <= (1 + x + x\<^sup>2) / exp (x \<^sup>2)"
    by (metis a b divide_right_mono exp_bound exp_ge_zero)
  also have "... <= (1 + x + x\<^sup>2) / (1 + x\<^sup>2)"
    by (simp add: a divide_left_mono mult_pos_pos add_pos_nonneg)
  also from a have "... <= 1 + x"
    by (simp add: field_simps add_strict_increasing zero_le_mult_iff)
  finally have "exp (x - x\<^sup>2) <= 1 + x" .
  also have "... = exp (ln (1 + x))"
  proof -
    from a have "0 < 1 + x" by auto
    thus ?thesis
      by (auto simp only: exp_ln_iff [THEN sym])
  qed
  finally have "exp (x - x\<^sup>2) <= exp (ln (1 + x))" .
  thus ?thesis
    by (metis exp_le_cancel_iff) 
qed

lemma ln_one_minus_pos_lower_bound:
  "0 <= x \<Longrightarrow> x <= (1 / 2) \<Longrightarrow> - x - 2 * x\<^sup>2 <= ln (1 - x)"
proof -
  assume a: "0 <= x" and b: "x <= (1 / 2)"
  from b have c: "x < 1" by auto
  then have "ln (1 - x) = - ln (1 + x / (1 - x))"
    apply (subst ln_inverse [symmetric])
    apply (simp add: field_simps)
    apply (rule arg_cong [where f=ln])
    apply (simp add: field_simps)
    done
  also have "- (x / (1 - x)) <= ..."
  proof -
    have "ln (1 + x / (1 - x)) <= x / (1 - x)"
      apply (rule ln_add_one_self_le_self)
      apply (rule divide_nonneg_pos)
      using a c apply auto
      done
    thus ?thesis
      by auto
  qed
  also have "- (x / (1 - x)) = -x / (1 - x)"
    by auto
  finally have d: "- x / (1 - x) <= ln (1 - x)" .
  have "0 < 1 - x" using a b by simp
  hence e: "-x - 2 * x\<^sup>2 <= - x / (1 - x)"
    using mult_right_le_one_le[of "x*x" "2*x"] a b
    by (simp add: field_simps power2_eq_square)
  from e d show "- x - 2 * x\<^sup>2 <= ln (1 - x)"
    by (rule order_trans)
qed

lemma ln_add_one_self_le_self2: "-1 < x \<Longrightarrow> ln(1 + x) <= x"
  apply (subgoal_tac "ln (1 + x) \<le> ln (exp x)", simp)
  apply (subst ln_le_cancel_iff)
  apply auto
  done

lemma abs_ln_one_plus_x_minus_x_bound_nonneg:
  "0 <= x \<Longrightarrow> x <= 1 \<Longrightarrow> abs(ln (1 + x) - x) <= x\<^sup>2"
proof -
  assume x: "0 <= x"
  assume x1: "x <= 1"
  from x have "ln (1 + x) <= x"
    by (rule ln_add_one_self_le_self)
  then have "ln (1 + x) - x <= 0"
    by simp
  then have "abs(ln(1 + x) - x) = - (ln(1 + x) - x)"
    by (rule abs_of_nonpos)
  also have "... = x - ln (1 + x)"
    by simp
  also have "... <= x\<^sup>2"
  proof -
    from x x1 have "x - x\<^sup>2 <= ln (1 + x)"
      by (intro ln_one_plus_pos_lower_bound)
    thus ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma abs_ln_one_plus_x_minus_x_bound_nonpos:
  "-(1 / 2) <= x \<Longrightarrow> x <= 0 \<Longrightarrow> abs(ln (1 + x) - x) <= 2 * x\<^sup>2"
proof -
  assume a: "-(1 / 2) <= x"
  assume b: "x <= 0"
  have "abs(ln (1 + x) - x) = x - ln(1 - (-x))"
    apply (subst abs_of_nonpos)
    apply simp
    apply (rule ln_add_one_self_le_self2)
    using a apply auto
    done
  also have "... <= 2 * x\<^sup>2"
    apply (subgoal_tac "- (-x) - 2 * (-x)\<^sup>2 <= ln (1 - (-x))")
    apply (simp add: algebra_simps)
    apply (rule ln_one_minus_pos_lower_bound)
    using a b apply auto
    done
  finally show ?thesis .
qed

lemma abs_ln_one_plus_x_minus_x_bound:
    "abs x <= 1 / 2 \<Longrightarrow> abs(ln (1 + x) - x) <= 2 * x\<^sup>2"
  apply (case_tac "0 <= x")
  apply (rule order_trans)
  apply (rule abs_ln_one_plus_x_minus_x_bound_nonneg)
  apply auto
  apply (rule abs_ln_one_plus_x_minus_x_bound_nonpos)
  apply auto
  done

lemma ln_x_over_x_mono: "exp 1 <= x \<Longrightarrow> x <= y \<Longrightarrow> (ln y / y) <= (ln x / x)"
proof -
  assume x: "exp 1 <= x" "x <= y"
  moreover have "0 < exp (1::real)" by simp
  ultimately have a: "0 < x" and b: "0 < y"
    by (fast intro: less_le_trans order_trans)+
  have "x * ln y - x * ln x = x * (ln y - ln x)"
    by (simp add: algebra_simps)
  also have "... = x * ln(y / x)"
    by (simp only: ln_div a b)
  also have "y / x = (x + (y - x)) / x"
    by simp
  also have "... = 1 + (y - x) / x"
    using x a by (simp add: field_simps)
  also have "x * ln(1 + (y - x) / x) <= x * ((y - x) / x)"
    apply (rule mult_left_mono)
    apply (rule ln_add_one_self_le_self)
    apply (rule divide_nonneg_pos)
    using x a apply simp_all
    done
  also have "... = y - x" using a by simp
  also have "... = (y - x) * ln (exp 1)" by simp
  also have "... <= (y - x) * ln x"
    apply (rule mult_left_mono)
    apply (subst ln_le_cancel_iff)
    apply fact
    apply (rule a)
    apply (rule x)
    using x apply simp
    done
  also have "... = y * ln x - x * ln x"
    by (rule left_diff_distrib)
  finally have "x * ln y <= y * ln x"
    by arith
  then have "ln y <= (y * ln x) / x" using a by (simp add: field_simps)
  also have "... = y * (ln x / x)" by simp
  finally show ?thesis using b by (simp add: field_simps)
qed

lemma ln_le_minus_one: "0 < x \<Longrightarrow> ln x \<le> x - 1"
  using exp_ge_add_one_self[of "ln x"] by simp

lemma ln_eq_minus_one:
  assumes "0 < x" "ln x = x - 1"
  shows "x = 1"
proof -
  let ?l = "\<lambda>y. ln y - y + 1"
  have D: "\<And>x. 0 < x \<Longrightarrow> DERIV ?l x :> (1 / x - 1)"
    by (auto intro!: DERIV_intros)

  show ?thesis
  proof (cases rule: linorder_cases)
    assume "x < 1"
    from dense[OF `x < 1`] obtain a where "x < a" "a < 1" by blast
    from `x < a` have "?l x < ?l a"
    proof (rule DERIV_pos_imp_increasing, safe)
      fix y
      assume "x \<le> y" "y \<le> a"
      with `0 < x` `a < 1` have "0 < 1 / y - 1" "0 < y"
        by (auto simp: field_simps)
      with D show "\<exists>z. DERIV ?l y :> z \<and> 0 < z"
        by auto
    qed
    also have "\<dots> \<le> 0"
      using ln_le_minus_one `0 < x` `x < a` by (auto simp: field_simps)
    finally show "x = 1" using assms by auto
  next
    assume "1 < x"
    from dense[OF this] obtain a where "1 < a" "a < x" by blast
    from `a < x` have "?l x < ?l a"
    proof (rule DERIV_neg_imp_decreasing, safe)
      fix y
      assume "a \<le> y" "y \<le> x"
      with `1 < a` have "1 / y - 1 < 0" "0 < y"
        by (auto simp: field_simps)
      with D show "\<exists>z. DERIV ?l y :> z \<and> z < 0"
        by blast
    qed
    also have "\<dots> \<le> 0"
      using ln_le_minus_one `1 < a` by (auto simp: field_simps)
    finally show "x = 1" using assms by auto
  next
    assume "x = 1"
    then show ?thesis by simp
  qed
qed

lemma exp_at_bot: "(exp ---> (0::real)) at_bot"
  unfolding tendsto_Zfun_iff
proof (rule ZfunI, simp add: eventually_at_bot_dense)
  fix r :: real assume "0 < r"
  {
    fix x
    assume "x < ln r"
    then have "exp x < exp (ln r)"
      by simp
    with `0 < r` have "exp x < r"
      by simp
  }
  then show "\<exists>k. \<forall>n<k. exp n < r" by auto
qed

lemma exp_at_top: "LIM x at_top. exp x :: real :> at_top"
  by (rule filterlim_at_top_at_top[where Q="\<lambda>x. True" and P="\<lambda>x. 0 < x" and g="ln"])
     (auto intro: eventually_gt_at_top)

lemma ln_at_0: "LIM x at_right 0. ln x :> at_bot"
  by (rule filterlim_at_bot_at_right[where Q="\<lambda>x. 0 < x" and P="\<lambda>x. True" and g="exp"])
     (auto simp: eventually_at_filter)

lemma ln_at_top: "LIM x at_top. ln x :> at_top"
  by (rule filterlim_at_top_at_top[where Q="\<lambda>x. 0 < x" and P="\<lambda>x. True" and g="exp"])
     (auto intro: eventually_gt_at_top)

lemma tendsto_power_div_exp_0: "((\<lambda>x. x ^ k / exp x) ---> (0::real)) at_top"
proof (induct k)
  case 0
  show "((\<lambda>x. x ^ 0 / exp x) ---> (0::real)) at_top"
    by (simp add: inverse_eq_divide[symmetric])
       (metis filterlim_compose[OF tendsto_inverse_0] exp_at_top filterlim_mono
              at_top_le_at_infinity order_refl)
next
  case (Suc k)
  show ?case
  proof (rule lhospital_at_top_at_top)
    show "eventually (\<lambda>x. DERIV (\<lambda>x. x ^ Suc k) x :> (real (Suc k) * x^k)) at_top"
      by eventually_elim (intro DERIV_intros, simp, simp)
    show "eventually (\<lambda>x. DERIV exp x :> exp x) at_top"
      by eventually_elim (auto intro!: DERIV_intros)
    show "eventually (\<lambda>x. exp x \<noteq> 0) at_top"
      by auto
    from tendsto_mult[OF tendsto_const Suc, of "real (Suc k)"]
    show "((\<lambda>x. real (Suc k) * x ^ k / exp x) ---> 0) at_top"
      by simp
  qed (rule exp_at_top)
qed


definition powr :: "[real,real] => real"  (infixr "powr" 80)
  -- {*exponentation with real exponent*}
  where "x powr a = exp(a * ln x)"

definition log :: "[real,real] => real"
  -- {*logarithm of @{term x} to base @{term a}*}
  where "log a x = ln x / ln a"


lemma tendsto_log [tendsto_intros]:
  "\<lbrakk>(f ---> a) F; (g ---> b) F; 0 < a; a \<noteq> 1; 0 < b\<rbrakk> \<Longrightarrow> ((\<lambda>x. log (f x) (g x)) ---> log a b) F"
  unfolding log_def by (intro tendsto_intros) auto

lemma continuous_log:
  assumes "continuous F f"
    and "continuous F g"
    and "0 < f (Lim F (\<lambda>x. x))"
    and "f (Lim F (\<lambda>x. x)) \<noteq> 1"
    and "0 < g (Lim F (\<lambda>x. x))"
  shows "continuous F (\<lambda>x. log (f x) (g x))"
  using assms unfolding continuous_def by (rule tendsto_log)

lemma continuous_at_within_log[continuous_intros]:
  assumes "continuous (at a within s) f"
    and "continuous (at a within s) g"
    and "0 < f a"
    and "f a \<noteq> 1"
    and "0 < g a"
  shows "continuous (at a within s) (\<lambda>x. log (f x) (g x))"
  using assms unfolding continuous_within by (rule tendsto_log)

lemma isCont_log[continuous_intros, simp]:
  assumes "isCont f a" "isCont g a" "0 < f a" "f a \<noteq> 1" "0 < g a"
  shows "isCont (\<lambda>x. log (f x) (g x)) a"
  using assms unfolding continuous_at by (rule tendsto_log)

lemma continuous_on_log[continuous_on_intros]:
  assumes "continuous_on s f" "continuous_on s g"
    and "\<forall>x\<in>s. 0 < f x" "\<forall>x\<in>s. f x \<noteq> 1" "\<forall>x\<in>s. 0 < g x"
  shows "continuous_on s (\<lambda>x. log (f x) (g x))"
  using assms unfolding continuous_on_def by (fast intro: tendsto_log)

lemma powr_one_eq_one [simp]: "1 powr a = 1"
  by (simp add: powr_def)

lemma powr_zero_eq_one [simp]: "x powr 0 = 1"
  by (simp add: powr_def)

lemma powr_one_gt_zero_iff [simp]: "(x powr 1 = x) = (0 < x)"
  by (simp add: powr_def)
declare powr_one_gt_zero_iff [THEN iffD2, simp]

lemma powr_mult: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> (x * y) powr a = (x powr a) * (y powr a)"
  by (simp add: powr_def exp_add [symmetric] ln_mult distrib_left)

lemma powr_gt_zero [simp]: "0 < x powr a"
  by (simp add: powr_def)

lemma powr_ge_pzero [simp]: "0 <= x powr y"
  by (rule order_less_imp_le, rule powr_gt_zero)

lemma powr_not_zero [simp]: "x powr a \<noteq> 0"
  by (simp add: powr_def)

lemma powr_divide: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> (x / y) powr a = (x powr a) / (y powr a)"
  apply (simp add: divide_inverse positive_imp_inverse_positive powr_mult)
  apply (simp add: powr_def exp_minus [symmetric] exp_add [symmetric] ln_inverse)
  done

lemma powr_divide2: "x powr a / x powr b = x powr (a - b)"
  apply (simp add: powr_def)
  apply (subst exp_diff [THEN sym])
  apply (simp add: left_diff_distrib)
  done

lemma powr_add: "x powr (a + b) = (x powr a) * (x powr b)"
  by (simp add: powr_def exp_add [symmetric] distrib_right)

lemma powr_mult_base: "0 < x \<Longrightarrow>x * x powr y = x powr (1 + y)"
  using assms by (auto simp: powr_add)

lemma powr_powr: "(x powr a) powr b = x powr (a * b)"
  by (simp add: powr_def)

lemma powr_powr_swap: "(x powr a) powr b = (x powr b) powr a"
  by (simp add: powr_powr mult_commute)

lemma powr_minus: "x powr (-a) = inverse (x powr a)"
  by (simp add: powr_def exp_minus [symmetric])

lemma powr_minus_divide: "x powr (-a) = 1/(x powr a)"
  by (simp add: divide_inverse powr_minus)

lemma powr_less_mono: "a < b \<Longrightarrow> 1 < x \<Longrightarrow> x powr a < x powr b"
  by (simp add: powr_def)

lemma powr_less_cancel: "x powr a < x powr b \<Longrightarrow> 1 < x \<Longrightarrow> a < b"
  by (simp add: powr_def)

lemma powr_less_cancel_iff [simp]: "1 < x \<Longrightarrow> (x powr a < x powr b) = (a < b)"
  by (blast intro: powr_less_cancel powr_less_mono)

lemma powr_le_cancel_iff [simp]: "1 < x \<Longrightarrow> (x powr a \<le> x powr b) = (a \<le> b)"
  by (simp add: linorder_not_less [symmetric])

lemma log_ln: "ln x = log (exp(1)) x"
  by (simp add: log_def)

lemma DERIV_log:
  assumes "x > 0"
  shows "DERIV (\<lambda>y. log b y) x :> 1 / (ln b * x)"
proof -
  def lb \<equiv> "1 / ln b"
  moreover have "DERIV (\<lambda>y. lb * ln y) x :> lb / x"
    using `x > 0` by (auto intro!: DERIV_intros)
  ultimately show ?thesis
    by (simp add: log_def)
qed

lemmas DERIV_log[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]

lemma powr_log_cancel [simp]: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> a powr (log a x) = x"
  by (simp add: powr_def log_def)

lemma log_powr_cancel [simp]: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> log a (a powr y) = y"
  by (simp add: log_def powr_def)

lemma log_mult:
  "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow>
    log a (x * y) = log a x + log a y"
  by (simp add: log_def ln_mult divide_inverse distrib_right)

lemma log_eq_div_ln_mult_log:
  "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < b \<Longrightarrow> b \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow>
    log a x = (ln b/ln a) * log b x"
  by (simp add: log_def divide_inverse)

text{*Base 10 logarithms*}
lemma log_base_10_eq1: "0 < x \<Longrightarrow> log 10 x = (ln (exp 1) / ln 10) * ln x"
  by (simp add: log_def)

lemma log_base_10_eq2: "0 < x \<Longrightarrow> log 10 x = (log 10 (exp 1)) * ln x"
  by (simp add: log_def)

lemma log_one [simp]: "log a 1 = 0"
  by (simp add: log_def)

lemma log_eq_one [simp]: "[| 0 < a; a \<noteq> 1 |] ==> log a a = 1"
  by (simp add: log_def)

lemma log_inverse: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> log a (inverse x) = - log a x"
  apply (rule_tac a1 = "log a x" in add_left_cancel [THEN iffD1])
  apply (simp add: log_mult [symmetric])
  done

lemma log_divide: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> log a (x/y) = log a x - log a y"
  by (simp add: log_mult divide_inverse log_inverse)

lemma log_less_cancel_iff [simp]:
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> log a x < log a y \<longleftrightarrow> x < y"
  apply safe
  apply (rule_tac [2] powr_less_cancel)
  apply (drule_tac a = "log a x" in powr_less_mono, auto)
  done

lemma log_inj:
  assumes "1 < b"
  shows "inj_on (log b) {0 <..}"
proof (rule inj_onI, simp)
  fix x y
  assume pos: "0 < x" "0 < y" and *: "log b x = log b y"
  show "x = y"
  proof (cases rule: linorder_cases)
    assume "x = y"
    then show ?thesis by simp
  next
    assume "x < y" hence "log b x < log b y"
      using log_less_cancel_iff[OF `1 < b`] pos by simp
    then show ?thesis using * by simp
  next
    assume "y < x" hence "log b y < log b x"
      using log_less_cancel_iff[OF `1 < b`] pos by simp
    then show ?thesis using * by simp
  qed
qed

lemma log_le_cancel_iff [simp]:
  "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> (log a x \<le> log a y) = (x \<le> y)"
  by (simp add: linorder_not_less [symmetric])

lemma zero_less_log_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < log a x \<longleftrightarrow> 1 < x"
  using log_less_cancel_iff[of a 1 x] by simp

lemma zero_le_log_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 \<le> log a x \<longleftrightarrow> 1 \<le> x"
  using log_le_cancel_iff[of a 1 x] by simp

lemma log_less_zero_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> log a x < 0 \<longleftrightarrow> x < 1"
  using log_less_cancel_iff[of a x 1] by simp

lemma log_le_zero_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> log a x \<le> 0 \<longleftrightarrow> x \<le> 1"
  using log_le_cancel_iff[of a x 1] by simp

lemma one_less_log_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 1 < log a x \<longleftrightarrow> a < x"
  using log_less_cancel_iff[of a a x] by simp

lemma one_le_log_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 1 \<le> log a x \<longleftrightarrow> a \<le> x"
  using log_le_cancel_iff[of a a x] by simp

lemma log_less_one_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> log a x < 1 \<longleftrightarrow> x < a"
  using log_less_cancel_iff[of a x a] by simp

lemma log_le_one_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> log a x \<le> 1 \<longleftrightarrow> x \<le> a"
  using log_le_cancel_iff[of a x a] by simp

lemma powr_realpow: "0 < x ==> x powr (real n) = x^n"
  apply (induct n)
  apply simp
  apply (subgoal_tac "real(Suc n) = real n + 1")
  apply (erule ssubst)
  apply (subst powr_add, simp, simp)
  done

lemma powr_realpow_numeral: "0 < x \<Longrightarrow> x powr (numeral n :: real) = x ^ (numeral n)"
  unfolding real_of_nat_numeral [symmetric] by (rule powr_realpow)

lemma powr_realpow2: "0 <= x ==> 0 < n ==> x^n = (if (x = 0) then 0 else x powr (real n))"
  apply (case_tac "x = 0", simp, simp)
  apply (rule powr_realpow [THEN sym], simp)
  done

lemma powr_int:
  assumes "x > 0"
  shows "x powr i = (if i \<ge> 0 then x ^ nat i else 1 / x ^ nat (-i))"
proof (cases "i < 0")
  case True
  have r: "x powr i = 1 / x powr (-i)" by (simp add: powr_minus field_simps)
  show ?thesis using `i < 0` `x > 0` by (simp add: r field_simps powr_realpow[symmetric])
next
  case False
  then show ?thesis by (simp add: assms powr_realpow[symmetric])
qed

lemma powr_one: "0 < x \<Longrightarrow> x powr 1 = x"
  using powr_realpow [of x 1] by simp

lemma powr_numeral: "0 < x \<Longrightarrow> x powr numeral n = x ^ numeral n"
  by (fact powr_realpow_numeral)

lemma powr_neg_one: "0 < x \<Longrightarrow> x powr - 1 = 1 / x"
  using powr_int [of x "- 1"] by simp

lemma powr_neg_numeral: "0 < x \<Longrightarrow> x powr - numeral n = 1 / x ^ numeral n"
  using powr_int [of x "- numeral n"] by simp

lemma root_powr_inverse: "0 < n \<Longrightarrow> 0 < x \<Longrightarrow> root n x = x powr (1/n)"
  by (rule real_root_pos_unique) (auto simp: powr_realpow[symmetric] powr_powr)

lemma ln_powr: "0 < x ==> 0 < y ==> ln(x powr y) = y * ln x"
  unfolding powr_def by simp

lemma log_powr: "0 < x ==> 0 \<le> y ==> log b (x powr y) = y * log b x"
  apply (cases "y = 0")
  apply force
  apply (auto simp add: log_def ln_powr field_simps)
  done

lemma log_nat_power: "0 < x ==> log b (x^n) = real n * log b x"
  apply (subst powr_realpow [symmetric])
  apply (auto simp add: log_powr)
  done

lemma ln_bound: "1 <= x ==> ln x <= x"
  apply (subgoal_tac "ln(1 + (x - 1)) <= x - 1")
  apply simp
  apply (rule ln_add_one_self_le_self, simp)
  done

lemma powr_mono: "a <= b ==> 1 <= x ==> x powr a <= x powr b"
  apply (cases "x = 1", simp)
  apply (cases "a = b", simp)
  apply (rule order_less_imp_le)
  apply (rule powr_less_mono, auto)
  done

lemma ge_one_powr_ge_zero: "1 <= x ==> 0 <= a ==> 1 <= x powr a"
  apply (subst powr_zero_eq_one [THEN sym])
  apply (rule powr_mono, assumption+)
  done

lemma powr_less_mono2: "0 < a ==> 0 < x ==> x < y ==> x powr a < y powr a"
  apply (unfold powr_def)
  apply (rule exp_less_mono)
  apply (rule mult_strict_left_mono)
  apply (subst ln_less_cancel_iff, assumption)
  apply (rule order_less_trans)
  prefer 2
  apply assumption+
  done

lemma powr_less_mono2_neg: "a < 0 ==> 0 < x ==> x < y ==> y powr a < x powr a"
  apply (unfold powr_def)
  apply (rule exp_less_mono)
  apply (rule mult_strict_left_mono_neg)
  apply (subst ln_less_cancel_iff)
  apply assumption
  apply (rule order_less_trans)
  prefer 2
  apply assumption+
  done

lemma powr_mono2: "0 <= a ==> 0 < x ==> x <= y ==> x powr a <= y powr a"
  apply (case_tac "a = 0", simp)
  apply (case_tac "x = y", simp)
  apply (metis less_eq_real_def powr_less_mono2)
  done

lemma powr_inj: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> a powr x = a powr y \<longleftrightarrow> x = y"
  unfolding powr_def exp_inj_iff by simp

lemma ln_powr_bound: "1 <= x ==> 0 < a ==> ln x <= (x powr a) / a"
  by (metis less_eq_real_def ln_less_self mult_imp_le_div_pos ln_powr mult_commute 
            order.strict_trans2 powr_gt_zero zero_less_one)

lemma ln_powr_bound2:
  assumes "1 < x" and "0 < a"
  shows "(ln x) powr a <= (a powr a) * x"
proof -
  from assms have "ln x <= (x powr (1 / a)) / (1 / a)"
    by (metis less_eq_real_def ln_powr_bound zero_less_divide_1_iff)
  also have "... = a * (x powr (1 / a))"
    by simp
  finally have "(ln x) powr a <= (a * (x powr (1 / a))) powr a"
    by (metis assms less_imp_le ln_gt_zero powr_mono2)
  also have "... = (a powr a) * ((x powr (1 / a)) powr a)"
    by (metis assms(2) powr_mult powr_gt_zero)
  also have "(x powr (1 / a)) powr a = x powr ((1 / a) * a)"
    by (rule powr_powr)
  also have "... = x" using assms
    by auto
  finally show ?thesis .
qed

lemma tendsto_powr [tendsto_intros]:
  "\<lbrakk>(f ---> a) F; (g ---> b) F; 0 < a\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x powr g x) ---> a powr b) F"
  unfolding powr_def by (intro tendsto_intros)

lemma continuous_powr:
  assumes "continuous F f"
    and "continuous F g"
    and "0 < f (Lim F (\<lambda>x. x))"
  shows "continuous F (\<lambda>x. (f x) powr (g x))"
  using assms unfolding continuous_def by (rule tendsto_powr)

lemma continuous_at_within_powr[continuous_intros]:
  assumes "continuous (at a within s) f"
    and "continuous (at a within s) g"
    and "0 < f a"
  shows "continuous (at a within s) (\<lambda>x. (f x) powr (g x))"
  using assms unfolding continuous_within by (rule tendsto_powr)

lemma isCont_powr[continuous_intros, simp]:
  assumes "isCont f a" "isCont g a" "0 < f a"
  shows "isCont (\<lambda>x. (f x) powr g x) a"
  using assms unfolding continuous_at by (rule tendsto_powr)

lemma continuous_on_powr[continuous_on_intros]:
  assumes "continuous_on s f" "continuous_on s g" and "\<forall>x\<in>s. 0 < f x"
  shows "continuous_on s (\<lambda>x. (f x) powr (g x))"
  using assms unfolding continuous_on_def by (fast intro: tendsto_powr)

(* FIXME: generalize by replacing d by with g x and g ---> d? *)
lemma tendsto_zero_powrI:
  assumes "eventually (\<lambda>x. 0 < f x ) F" and "(f ---> 0) F"
    and "0 < d"
  shows "((\<lambda>x. f x powr d) ---> 0) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  def Z \<equiv> "e powr (1 / d)"
  with `0 < e` have "0 < Z" by simp
  with assms have "eventually (\<lambda>x. 0 < f x \<and> dist (f x) 0 < Z) F"
    by (intro eventually_conj tendstoD)
  moreover
  from assms have "\<And>x. 0 < x \<and> dist x 0 < Z \<Longrightarrow> x powr d < Z powr d"
    by (intro powr_less_mono2) (auto simp: dist_real_def)
  with assms `0 < e` have "\<And>x. 0 < x \<and> dist x 0 < Z \<Longrightarrow> dist (x powr d) 0 < e"
    unfolding dist_real_def Z_def by (auto simp: powr_powr)
  ultimately
  show "eventually (\<lambda>x. dist (f x powr d) 0 < e) F" by (rule eventually_elim1)
qed

lemma tendsto_neg_powr:
  assumes "s < 0"
    and "LIM x F. f x :> at_top"
  shows "((\<lambda>x. f x powr s) ---> 0) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  def Z \<equiv> "e powr (1 / s)"
  from assms have "eventually (\<lambda>x. Z < f x) F"
    by (simp add: filterlim_at_top_dense)
  moreover
  from assms have "\<And>x. Z < x \<Longrightarrow> x powr s < Z powr s"
    by (auto simp: Z_def intro!: powr_less_mono2_neg)
  with assms `0 < e` have "\<And>x. Z < x \<Longrightarrow> dist (x powr s) 0 < e"
    by (simp add: powr_powr Z_def dist_real_def)
  ultimately
  show "eventually (\<lambda>x. dist (f x powr s) 0 < e) F" by (rule eventually_elim1)
qed

subsection {* Sine and Cosine *}

definition sin_coeff :: "nat \<Rightarrow> real" where
  "sin_coeff = (\<lambda>n. if even n then 0 else -1 ^ ((n - Suc 0) div 2) / real (fact n))"

definition cos_coeff :: "nat \<Rightarrow> real" where
  "cos_coeff = (\<lambda>n. if even n then (-1 ^ (n div 2)) / real (fact n) else 0)"

definition sin :: "real \<Rightarrow> real"
  where "sin = (\<lambda>x. \<Sum>n. sin_coeff n * x ^ n)"

definition cos :: "real \<Rightarrow> real"
  where "cos = (\<lambda>x. \<Sum>n. cos_coeff n * x ^ n)"

lemma sin_coeff_0 [simp]: "sin_coeff 0 = 0"
  unfolding sin_coeff_def by simp

lemma cos_coeff_0 [simp]: "cos_coeff 0 = 1"
  unfolding cos_coeff_def by simp

lemma sin_coeff_Suc: "sin_coeff (Suc n) = cos_coeff n / real (Suc n)"
  unfolding cos_coeff_def sin_coeff_def
  by (simp del: mult_Suc)

lemma cos_coeff_Suc: "cos_coeff (Suc n) = - sin_coeff n / real (Suc n)"
  unfolding cos_coeff_def sin_coeff_def
  by (simp del: mult_Suc, auto simp add: odd_Suc_mult_two_ex)

lemma summable_sin: "summable (\<lambda>n. sin_coeff n * x ^ n)"
  unfolding sin_coeff_def
  apply (rule summable_comparison_test [OF _ summable_exp [where x="\<bar>x\<bar>"]])
  apply (auto simp add: divide_inverse abs_mult power_abs [symmetric] zero_le_mult_iff)
  done

lemma summable_cos: "summable (\<lambda>n. cos_coeff n * x ^ n)"
  unfolding cos_coeff_def
  apply (rule summable_comparison_test [OF _ summable_exp [where x="\<bar>x\<bar>"]])
  apply (auto simp add: divide_inverse abs_mult power_abs [symmetric] zero_le_mult_iff)
  done

lemma sin_converges: "(\<lambda>n. sin_coeff n * x ^ n) sums sin(x)"
  unfolding sin_def by (rule summable_sin [THEN summable_sums])

lemma cos_converges: "(\<lambda>n. cos_coeff n * x ^ n) sums cos(x)"
  unfolding cos_def by (rule summable_cos [THEN summable_sums])

lemma diffs_sin_coeff: "diffs sin_coeff = cos_coeff"
  by (simp add: diffs_def sin_coeff_Suc real_of_nat_def del: of_nat_Suc)

lemma diffs_cos_coeff: "diffs cos_coeff = (\<lambda>n. - sin_coeff n)"
  by (simp add: diffs_def cos_coeff_Suc real_of_nat_def del: of_nat_Suc)

text{*Now at last we can get the derivatives of exp, sin and cos*}

lemma DERIV_sin [simp]: "DERIV sin x :> cos(x)"
  unfolding sin_def cos_def
  apply (rule DERIV_cong, rule termdiffs [where K="1 + \<bar>x\<bar>"])
  apply (simp_all add: diffs_sin_coeff diffs_cos_coeff
    summable_minus summable_sin summable_cos)
  done

declare DERIV_sin[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]

lemma DERIV_cos [simp]: "DERIV cos x :> -sin(x)"
  unfolding cos_def sin_def
  apply (rule DERIV_cong, rule termdiffs [where K="1 + \<bar>x\<bar>"])
  apply (simp_all add: diffs_sin_coeff diffs_cos_coeff diffs_minus
    summable_minus summable_sin summable_cos suminf_minus)
  done

declare DERIV_cos[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]

lemma isCont_sin: "isCont sin x"
  by (rule DERIV_sin [THEN DERIV_isCont])

lemma isCont_cos: "isCont cos x"
  by (rule DERIV_cos [THEN DERIV_isCont])

lemma isCont_sin' [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. sin (f x)) a"
  by (rule isCont_o2 [OF _ isCont_sin])

lemma isCont_cos' [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. cos (f x)) a"
  by (rule isCont_o2 [OF _ isCont_cos])

lemma tendsto_sin [tendsto_intros]:
  "(f ---> a) F \<Longrightarrow> ((\<lambda>x. sin (f x)) ---> sin a) F"
  by (rule isCont_tendsto_compose [OF isCont_sin])

lemma tendsto_cos [tendsto_intros]:
  "(f ---> a) F \<Longrightarrow> ((\<lambda>x. cos (f x)) ---> cos a) F"
  by (rule isCont_tendsto_compose [OF isCont_cos])

lemma continuous_sin [continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. sin (f x))"
  unfolding continuous_def by (rule tendsto_sin)

lemma continuous_on_sin [continuous_on_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. sin (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_sin)

lemma continuous_cos [continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. cos (f x))"
  unfolding continuous_def by (rule tendsto_cos)

lemma continuous_on_cos [continuous_on_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. cos (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_cos)

subsection {* Properties of Sine and Cosine *}

lemma sin_zero [simp]: "sin 0 = 0"
  unfolding sin_def sin_coeff_def by (simp add: powser_zero)

lemma cos_zero [simp]: "cos 0 = 1"
  unfolding cos_def cos_coeff_def by (simp add: powser_zero)

lemma sin_cos_squared_add [simp]: "(sin x)\<^sup>2 + (cos x)\<^sup>2 = 1"
proof -
  have "\<forall>x. DERIV (\<lambda>x. (sin x)\<^sup>2 + (cos x)\<^sup>2) x :> 0"
    by (auto intro!: DERIV_intros)
  hence "(sin x)\<^sup>2 + (cos x)\<^sup>2 = (sin 0)\<^sup>2 + (cos 0)\<^sup>2"
    by (rule DERIV_isconst_all)
  thus "(sin x)\<^sup>2 + (cos x)\<^sup>2 = 1" by simp
qed

lemma sin_cos_squared_add2 [simp]: "(cos x)\<^sup>2 + (sin x)\<^sup>2 = 1"
  by (subst add_commute, rule sin_cos_squared_add)

lemma sin_cos_squared_add3 [simp]: "cos x * cos x + sin x * sin x = 1"
  using sin_cos_squared_add2 [unfolded power2_eq_square] .

lemma sin_squared_eq: "(sin x)\<^sup>2 = 1 - (cos x)\<^sup>2"
  unfolding eq_diff_eq by (rule sin_cos_squared_add)

lemma cos_squared_eq: "(cos x)\<^sup>2 = 1 - (sin x)\<^sup>2"
  unfolding eq_diff_eq by (rule sin_cos_squared_add2)

lemma abs_sin_le_one [simp]: "\<bar>sin x\<bar> \<le> 1"
  by (rule power2_le_imp_le, simp_all add: sin_squared_eq)

lemma sin_ge_minus_one [simp]: "-1 \<le> sin x"
  using abs_sin_le_one [of x] unfolding abs_le_iff by simp

lemma sin_le_one [simp]: "sin x \<le> 1"
  using abs_sin_le_one [of x] unfolding abs_le_iff by simp

lemma abs_cos_le_one [simp]: "\<bar>cos x\<bar> \<le> 1"
  by (rule power2_le_imp_le, simp_all add: cos_squared_eq)

lemma cos_ge_minus_one [simp]: "-1 \<le> cos x"
  using abs_cos_le_one [of x] unfolding abs_le_iff by simp

lemma cos_le_one [simp]: "cos x \<le> 1"
  using abs_cos_le_one [of x] unfolding abs_le_iff by simp

lemma DERIV_fun_pow: "DERIV g x :> m ==>
      DERIV (\<lambda>x. (g x) ^ n) x :> real n * (g x) ^ (n - 1) * m"
  by (auto intro!: DERIV_intros)

lemma DERIV_fun_exp:
     "DERIV g x :> m ==> DERIV (\<lambda>x. exp(g x)) x :> exp(g x) * m"
  by (auto intro!: DERIV_intros)

lemma DERIV_fun_sin:
     "DERIV g x :> m ==> DERIV (\<lambda>x. sin(g x)) x :> cos(g x) * m"
  by (auto intro!: DERIV_intros)

lemma DERIV_fun_cos:
     "DERIV g x :> m ==> DERIV (\<lambda>x. cos(g x)) x :> -sin(g x) * m"
  by (auto intro!: DERIV_intros)

lemma sin_cos_add_lemma:
  "(sin (x + y) - (sin x * cos y + cos x * sin y))\<^sup>2 +
    (cos (x + y) - (cos x * cos y - sin x * sin y))\<^sup>2 = 0"
  (is "?f x = 0")
proof -
  have "\<forall>x. DERIV (\<lambda>x. ?f x) x :> 0"
    by (auto intro!: DERIV_intros simp add: algebra_simps)
  hence "?f x = ?f 0"
    by (rule DERIV_isconst_all)
  thus ?thesis by simp
qed

lemma sin_add: "sin (x + y) = sin x * cos y + cos x * sin y"
  using sin_cos_add_lemma unfolding realpow_two_sum_zero_iff by simp

lemma cos_add: "cos (x + y) = cos x * cos y - sin x * sin y"
  using sin_cos_add_lemma unfolding realpow_two_sum_zero_iff by simp

lemma sin_cos_minus_lemma:
  "(sin(-x) + sin(x))\<^sup>2 + (cos(-x) - cos(x))\<^sup>2 = 0" (is "?f x = 0")
proof -
  have "\<forall>x. DERIV (\<lambda>x. ?f x) x :> 0"
    by (auto intro!: DERIV_intros simp add: algebra_simps)
  hence "?f x = ?f 0"
    by (rule DERIV_isconst_all)
  thus ?thesis by simp
qed

lemma sin_minus [simp]: "sin (-x) = -sin(x)"
  using sin_cos_minus_lemma [where x=x] by simp

lemma cos_minus [simp]: "cos (-x) = cos(x)"
  using sin_cos_minus_lemma [where x=x] by simp

lemma sin_diff: "sin (x - y) = sin x * cos y - cos x * sin y"
  using sin_add [of x "- y"] by simp

lemma sin_diff2: "sin (x - y) = cos y * sin x - sin y * cos x"
  by (simp add: sin_diff mult_commute)

lemma cos_diff: "cos (x - y) = cos x * cos y + sin x * sin y"
  using cos_add [of x "- y"] by simp

lemma cos_diff2: "cos (x - y) = cos y * cos x + sin y * sin x"
  by (simp add: cos_diff mult_commute)

lemma sin_double [simp]: "sin(2 * x) = 2* sin x * cos x"
  using sin_add [where x=x and y=x] by simp

lemma cos_double: "cos(2* x) = ((cos x)\<^sup>2) - ((sin x)\<^sup>2)"
  using cos_add [where x=x and y=x]
  by (simp add: power2_eq_square)


subsection {* The Constant Pi *}

definition pi :: real
  where "pi = 2 * (THE x. 0 \<le> (x::real) & x \<le> 2 & cos x = 0)"

text{*Show that there's a least positive @{term x} with @{term "cos(x) = 0"};
   hence define pi.*}

lemma sin_paired:
  "(\<lambda>n. -1 ^ n /(real (fact (2 * n + 1))) * x ^ (2 * n + 1)) sums  sin x"
proof -
  have "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2. sin_coeff k * x ^ k) sums sin x"
    by (rule sin_converges [THEN sums_group], simp)
  thus ?thesis unfolding One_nat_def sin_coeff_def by (simp add: mult_ac)
qed

lemma sin_gt_zero:
  assumes "0 < x" and "x < 2"
  shows "0 < sin x"
proof -
  let ?f = "\<lambda>n. \<Sum>k = n*2..<n*2+2. -1 ^ k / real (fact (2*k+1)) * x^(2*k+1)"
  have pos: "\<forall>n. 0 < ?f n"
  proof
    fix n :: nat
    let ?k2 = "real (Suc (Suc (4 * n)))"
    let ?k3 = "real (Suc (Suc (Suc (4 * n))))"
    have "x * x < ?k2 * ?k3"
      using assms by (intro mult_strict_mono', simp_all)
    hence "x * x * x * x ^ (n * 4) < ?k2 * ?k3 * x * x ^ (n * 4)"
      by (intro mult_strict_right_mono zero_less_power `0 < x`)
    thus "0 < ?f n"
      by (simp del: mult_Suc,
        simp add: less_divide_eq mult_pos_pos field_simps del: mult_Suc)
  qed
  have sums: "?f sums sin x"
    by (rule sin_paired [THEN sums_group], simp)
  show "0 < sin x"
    unfolding sums_unique [OF sums]
    using sums_summable [OF sums] pos
    by (rule suminf_gt_zero)
qed

lemma cos_double_less_one: "0 < x \<Longrightarrow> x < 2 \<Longrightarrow> cos (2 * x) < 1"
  using sin_gt_zero [where x = x] by (auto simp add: cos_squared_eq cos_double)

lemma cos_paired: "(\<lambda>n. -1 ^ n /(real (fact (2 * n))) * x ^ (2 * n)) sums cos x"
proof -
  have "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2. cos_coeff k * x ^ k) sums cos x"
    by (rule cos_converges [THEN sums_group], simp)
  thus ?thesis unfolding cos_coeff_def by (simp add: mult_ac)
qed

lemma real_mult_inverse_cancel:
     "[|(0::real) < x; 0 < x1; x1 * y < x * u |]
      ==> inverse x * y < inverse x1 * u"
  by (metis field_divide_inverse mult_commute mult_assoc pos_divide_less_eq pos_less_divide_eq)

lemma real_mult_inverse_cancel2:
     "[|(0::real) < x;0 < x1; x1 * y < x * u |] ==> y * inverse x < u * inverse x1"
  by (auto dest: real_mult_inverse_cancel simp add: mult_ac)

lemmas realpow_num_eq_if = power_eq_if

lemma cos_two_less_zero [simp]:
  "cos 2 < 0"
proof -
  note fact_Suc [simp del]
  from cos_paired
  have "(\<lambda>n. - (-1 ^ n / real (fact (2 * n)) * 2 ^ (2 * n))) sums - cos 2"
    by (rule sums_minus)
  then have *: "(\<lambda>n. - (-1 ^ n * 2 ^ (2 * n) / real (fact (2 * n)))) sums - cos 2"
    by simp
  then have **: "summable (\<lambda>n. - (-1 ^ n * 2 ^ (2 * n) / real (fact (2 * n))))"
    by (rule sums_summable)
  have "0 < (\<Sum>n = 0..<Suc (Suc (Suc 0)). - (-1 ^ n * 2 ^ (2 * n) / real (fact (2 * n))))"
    by (simp add: fact_num_eq_if_nat realpow_num_eq_if)
  moreover have "(\<Sum>n = 0..<Suc (Suc (Suc 0)). - (-1 ^ n  * 2 ^ (2 * n) / real (fact (2 * n))))
    < (\<Sum>n. - (-1 ^ n * 2 ^ (2 * n) / real (fact (2 * n))))"
  proof -
    { fix d
      have "4 * real (fact (Suc (Suc (Suc (Suc (Suc (Suc (4 * d))))))))
       < real (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (4 * d)))))))) *
           fact (Suc (Suc (Suc (Suc (Suc (Suc (Suc (4 * d)))))))))"
        by (simp only: real_of_nat_mult) (auto intro!: mult_strict_mono fact_less_mono_nat)
      then have "4 * real (fact (Suc (Suc (Suc (Suc (Suc (Suc (4 * d))))))))
        < real (fact (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (4 * d))))))))))"
        by (simp only: fact_Suc [of "Suc (Suc (Suc (Suc (Suc (Suc (Suc (4 * d)))))))"])
      then have "4 * inverse (real (fact (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (4 * d)))))))))))
        < inverse (real (fact (Suc (Suc (Suc (Suc (Suc (Suc (4 * d)))))))))"
        by (simp add: inverse_eq_divide less_divide_eq)
    }
    note *** = this
    have [simp]: "\<And>x y::real. 0 < x - y \<longleftrightarrow> y < x" by arith
    from ** show ?thesis by (rule sumr_pos_lt_pair)
      (simp add: divide_inverse mult_assoc [symmetric] ***)
  qed
  ultimately have "0 < (\<Sum>n. - (-1 ^ n * 2 ^ (2 * n) / real (fact (2 * n))))"
    by (rule order_less_trans)
  moreover from * have "- cos 2 = (\<Sum>n. - (-1 ^ n * 2 ^ (2 * n) / real (fact (2 * n))))"
    by (rule sums_unique)
  ultimately have "0 < - cos 2" by simp
  then show ?thesis by simp
qed

lemmas cos_two_neq_zero [simp] = cos_two_less_zero [THEN less_imp_neq]
lemmas cos_two_le_zero [simp] = cos_two_less_zero [THEN order_less_imp_le]

lemma cos_is_zero: "EX! x. 0 \<le> x & x \<le> 2 \<and> cos x = 0"
proof (rule ex_ex1I)
  show "\<exists>x. 0 \<le> x & x \<le> 2 & cos x = 0"
    by (rule IVT2, simp_all)
next
  fix x y
  assume x: "0 \<le> x \<and> x \<le> 2 \<and> cos x = 0"
  assume y: "0 \<le> y \<and> y \<le> 2 \<and> cos y = 0"
  have [simp]: "\<forall>x. cos differentiable x"
    unfolding differentiable_def by (auto intro: DERIV_cos)
  from x y show "x = y"
    apply (cut_tac less_linear [of x y], auto)
    apply (drule_tac f = cos in Rolle)
    apply (drule_tac [5] f = cos in Rolle)
    apply (auto dest!: DERIV_cos [THEN DERIV_unique])
    apply (metis order_less_le_trans less_le sin_gt_zero)
    apply (metis order_less_le_trans less_le sin_gt_zero)
    done
qed

lemma pi_half: "pi/2 = (THE x. 0 \<le> x & x \<le> 2 & cos x = 0)"
  by (simp add: pi_def)

lemma cos_pi_half [simp]: "cos (pi / 2) = 0"
  by (simp add: pi_half cos_is_zero [THEN theI'])

lemma pi_half_gt_zero [simp]: "0 < pi / 2"
  apply (rule order_le_neq_trans)
  apply (simp add: pi_half cos_is_zero [THEN theI'])
  apply (metis cos_pi_half cos_zero zero_neq_one)
  done

lemmas pi_half_neq_zero [simp] = pi_half_gt_zero [THEN less_imp_neq, symmetric]
lemmas pi_half_ge_zero [simp] = pi_half_gt_zero [THEN order_less_imp_le]

lemma pi_half_less_two [simp]: "pi / 2 < 2"
  apply (rule order_le_neq_trans)
  apply (simp add: pi_half cos_is_zero [THEN theI'])
  apply (metis cos_pi_half cos_two_neq_zero)
  done

lemmas pi_half_neq_two [simp] = pi_half_less_two [THEN less_imp_neq]
lemmas pi_half_le_two [simp] =  pi_half_less_two [THEN order_less_imp_le]

lemma pi_gt_zero [simp]: "0 < pi"
  using pi_half_gt_zero by simp

lemma pi_ge_zero [simp]: "0 \<le> pi"
  by (rule pi_gt_zero [THEN order_less_imp_le])

lemma pi_neq_zero [simp]: "pi \<noteq> 0"
  by (rule pi_gt_zero [THEN less_imp_neq, symmetric])

lemma pi_not_less_zero [simp]: "\<not> pi < 0"
  by (simp add: linorder_not_less)

lemma minus_pi_half_less_zero: "-(pi/2) < 0"
  by simp

lemma m2pi_less_pi: "- (2 * pi) < pi"
  by simp

lemma sin_pi_half [simp]: "sin(pi/2) = 1"
  using sin_cos_squared_add2 [where x = "pi/2"]
  using sin_gt_zero [OF pi_half_gt_zero pi_half_less_two]
  by (simp add: power2_eq_1_iff)

lemma cos_pi [simp]: "cos pi = -1"
  using cos_add [where x = "pi/2" and y = "pi/2"] by simp

lemma sin_pi [simp]: "sin pi = 0"
  using sin_add [where x = "pi/2" and y = "pi/2"] by simp

lemma sin_cos_eq: "sin x = cos (pi/2 - x)"
  by (simp add: cos_diff)

lemma minus_sin_cos_eq: "-sin x = cos (x + pi/2)"
  by (simp add: cos_add)

lemma cos_sin_eq: "cos x = sin (pi/2 - x)"
  by (simp add: sin_diff)

lemma sin_periodic_pi [simp]: "sin (x + pi) = - sin x"
  by (simp add: sin_add)

lemma sin_periodic_pi2 [simp]: "sin (pi + x) = - sin x"
  by (simp add: sin_add)

lemma cos_periodic_pi [simp]: "cos (x + pi) = - cos x"
  by (simp add: cos_add)

lemma sin_periodic [simp]: "sin (x + 2*pi) = sin x"
  by (simp add: sin_add cos_double)

lemma cos_periodic [simp]: "cos (x + 2*pi) = cos x"
  by (simp add: cos_add cos_double)

lemma cos_npi [simp]: "cos (real n * pi) = -1 ^ n"
  by (induct n) (auto simp add: real_of_nat_Suc distrib_right)

lemma cos_npi2 [simp]: "cos (pi * real n) = -1 ^ n"
  by (metis cos_npi mult_commute)

lemma sin_npi [simp]: "sin (real (n::nat) * pi) = 0"
  by (induct n) (auto simp add: real_of_nat_Suc distrib_right)

lemma sin_npi2 [simp]: "sin (pi * real (n::nat)) = 0"
  by (simp add: mult_commute [of pi])

lemma cos_two_pi [simp]: "cos (2 * pi) = 1"
  by (simp add: cos_double)

lemma sin_two_pi [simp]: "sin (2 * pi) = 0"
  by simp

lemma sin_gt_zero2: "[| 0 < x; x < pi/2 |] ==> 0 < sin x"
  by (metis sin_gt_zero order_less_trans pi_half_less_two)

lemma sin_less_zero:
  assumes "- pi/2 < x" and "x < 0"
  shows "sin x < 0"
proof -
  have "0 < sin (- x)" using assms by (simp only: sin_gt_zero2)
  thus ?thesis by simp
qed

lemma pi_less_4: "pi < 4"
  using pi_half_less_two by auto

lemma cos_gt_zero: "[| 0 < x; x < pi/2 |] ==> 0 < cos x"
  apply (cut_tac pi_less_4)
  apply (cut_tac f = cos and a = 0 and b = x and y = 0 in IVT2_objl, safe, simp_all)
  apply (cut_tac cos_is_zero, safe)
  apply (rename_tac y z)
  apply (drule_tac x = y in spec)
  apply (drule_tac x = "pi/2" in spec, simp)
  done

lemma cos_gt_zero_pi: "[| -(pi/2) < x; x < pi/2 |] ==> 0 < cos x"
  apply (rule_tac x = x and y = 0 in linorder_cases)
  apply (metis cos_gt_zero cos_minus minus_less_iff neg_0_less_iff_less)
  apply (auto intro: cos_gt_zero)
  done

lemma cos_ge_zero: "[| -(pi/2) \<le> x; x \<le> pi/2 |] ==> 0 \<le> cos x"
  apply (auto simp add: order_le_less cos_gt_zero_pi)
  apply (subgoal_tac "x = pi/2", auto)
  done

lemma sin_gt_zero_pi: "[| 0 < x; x < pi  |] ==> 0 < sin x"
  by (simp add: sin_cos_eq cos_gt_zero_pi)

lemma pi_ge_two: "2 \<le> pi"
proof (rule ccontr)
  assume "\<not> 2 \<le> pi" hence "pi < 2" by auto
  have "\<exists>y > pi. y < 2 \<and> y < 2 * pi"
  proof (cases "2 < 2 * pi")
    case True with dense[OF `pi < 2`] show ?thesis by auto
  next
    case False have "pi < 2 * pi" by auto
    from dense[OF this] and False show ?thesis by auto
  qed
  then obtain y where "pi < y" and "y < 2" and "y < 2 * pi" by blast
  hence "0 < sin y" using sin_gt_zero by auto
  moreover
  have "sin y < 0" using sin_gt_zero_pi[of "y - pi"] `pi < y` and `y < 2 * pi` sin_periodic_pi[of "y - pi"] by auto
  ultimately show False by auto
qed

lemma sin_ge_zero: "[| 0 \<le> x; x \<le> pi |] ==> 0 \<le> sin x"
  by (auto simp add: order_le_less sin_gt_zero_pi)

text {* FIXME: This proof is almost identical to lemma @{text cos_is_zero}.
  It should be possible to factor out some of the common parts. *}

lemma cos_total: "[| -1 \<le> y; y \<le> 1 |] ==> EX! x. 0 \<le> x & x \<le> pi & (cos x = y)"
proof (rule ex_ex1I)
  assume y: "-1 \<le> y" "y \<le> 1"
  show "\<exists>x. 0 \<le> x & x \<le> pi & cos x = y"
    by (rule IVT2, simp_all add: y)
next
  fix a b
  assume a: "0 \<le> a \<and> a \<le> pi \<and> cos a = y"
  assume b: "0 \<le> b \<and> b \<le> pi \<and> cos b = y"
  have [simp]: "\<forall>x. cos differentiable x"
    unfolding differentiable_def by (auto intro: DERIV_cos)
  from a b show "a = b"
    apply (cut_tac less_linear [of a b], auto)
    apply (drule_tac f = cos in Rolle)
    apply (drule_tac [5] f = cos in Rolle)
    apply (auto dest!: DERIV_cos [THEN DERIV_unique])
    apply (metis order_less_le_trans less_le sin_gt_zero_pi)
    apply (metis order_less_le_trans less_le sin_gt_zero_pi)
    done
qed

lemma sin_total:
     "[| -1 \<le> y; y \<le> 1 |] ==> EX! x. -(pi/2) \<le> x & x \<le> pi/2 & (sin x = y)"
apply (rule ccontr)
apply (subgoal_tac "\<forall>x. (- (pi/2) \<le> x & x \<le> pi/2 & (sin x = y)) = (0 \<le> (x + pi/2) & (x + pi/2) \<le> pi & (cos (x + pi/2) = -y))")
apply (erule contrapos_np)
apply simp
apply (cut_tac y="-y" in cos_total, simp) apply simp
apply (erule ex1E)
apply (rule_tac a = "x - (pi/2)" in ex1I)
apply (simp (no_asm) add: add_assoc)
apply (rotate_tac 3)
apply (drule_tac x = "xa + pi/2" in spec, safe, simp_all add: cos_add)
done

lemma reals_Archimedean4:
     "[| 0 < y; 0 \<le> x |] ==> \<exists>n. real n * y \<le> x & x < real (Suc n) * y"
apply (auto dest!: reals_Archimedean3)
apply (drule_tac x = x in spec, clarify)
apply (subgoal_tac "x < real(LEAST m::nat. x < real m * y) * y")
 prefer 2 apply (erule LeastI)
apply (case_tac "LEAST m::nat. x < real m * y", simp)
apply (rename_tac m)
apply (subgoal_tac "~ x < real m * y")
 prefer 2 apply (rule not_less_Least, simp, force)
done

(* Pre Isabelle99-2 proof was simpler- numerals arithmetic
   now causes some unwanted re-arrangements of literals!   *)
lemma cos_zero_lemma:
     "[| 0 \<le> x; cos x = 0 |] ==>
      \<exists>n::nat. ~even n & x = real n * (pi/2)"
apply (drule pi_gt_zero [THEN reals_Archimedean4], safe)
apply (subgoal_tac "0 \<le> x - real n * pi &
                    (x - real n * pi) \<le> pi & (cos (x - real n * pi) = 0) ")
apply (auto simp add: algebra_simps real_of_nat_Suc)
 prefer 2 apply (simp add: cos_diff)
apply (simp add: cos_diff)
apply (subgoal_tac "EX! x. 0 \<le> x & x \<le> pi & cos x = 0")
apply (rule_tac [2] cos_total, safe)
apply (drule_tac x = "x - real n * pi" in spec)
apply (drule_tac x = "pi/2" in spec)
apply (simp add: cos_diff)
apply (rule_tac x = "Suc (2 * n)" in exI)
apply (simp add: real_of_nat_Suc algebra_simps, auto)
done

lemma sin_zero_lemma:
     "[| 0 \<le> x; sin x = 0 |] ==>
      \<exists>n::nat. even n & x = real n * (pi/2)"
apply (subgoal_tac "\<exists>n::nat. ~ even n & x + pi/2 = real n * (pi/2) ")
 apply (clarify, rule_tac x = "n - 1" in exI)
 apply (force simp add: odd_Suc_mult_two_ex real_of_nat_Suc distrib_right)
apply (rule cos_zero_lemma)
apply (simp_all add: cos_add)
done


lemma cos_zero_iff:
     "(cos x = 0) =
      ((\<exists>n::nat. ~even n & (x = real n * (pi/2))) |
       (\<exists>n::nat. ~even n & (x = -(real n * (pi/2)))))"
apply (rule iffI)
apply (cut_tac linorder_linear [of 0 x], safe)
apply (drule cos_zero_lemma, assumption+)
apply (cut_tac x="-x" in cos_zero_lemma, simp, simp)
apply (force simp add: minus_equation_iff [of x])
apply (auto simp only: odd_Suc_mult_two_ex real_of_nat_Suc distrib_right)
apply (auto simp add: cos_diff cos_add)
done

(* ditto: but to a lesser extent *)
lemma sin_zero_iff:
     "(sin x = 0) =
      ((\<exists>n::nat. even n & (x = real n * (pi/2))) |
       (\<exists>n::nat. even n & (x = -(real n * (pi/2)))))"
apply (rule iffI)
apply (cut_tac linorder_linear [of 0 x], safe)
apply (drule sin_zero_lemma, assumption+)
apply (cut_tac x="-x" in sin_zero_lemma, simp, simp, safe)
apply (force simp add: minus_equation_iff [of x])
apply (auto simp add: even_mult_two_ex)
done

lemma cos_monotone_0_pi:
  assumes "0 \<le> y" and "y < x" and "x \<le> pi"
  shows "cos x < cos y"
proof -
  have "- (x - y) < 0" using assms by auto

  from MVT2[OF `y < x` DERIV_cos[THEN impI, THEN allI]]
  obtain z where "y < z" and "z < x" and cos_diff: "cos x - cos y = (x - y) * - sin z"
    by auto
  hence "0 < z" and "z < pi" using assms by auto
  hence "0 < sin z" using sin_gt_zero_pi by auto
  hence "cos x - cos y < 0"
    unfolding cos_diff minus_mult_commute[symmetric]
    using `- (x - y) < 0` by (rule mult_pos_neg2)
  thus ?thesis by auto
qed

lemma cos_monotone_0_pi':
  assumes "0 \<le> y" and "y \<le> x" and "x \<le> pi"
  shows "cos x \<le> cos y"
proof (cases "y < x")
  case True
  show ?thesis
    using cos_monotone_0_pi[OF `0 \<le> y` True `x \<le> pi`] by auto
next
  case False
  hence "y = x" using `y \<le> x` by auto
  thus ?thesis by auto
qed

lemma cos_monotone_minus_pi_0:
  assumes "-pi \<le> y" and "y < x" and "x \<le> 0"
  shows "cos y < cos x"
proof -
  have "0 \<le> -x" and "-x < -y" and "-y \<le> pi"
    using assms by auto
  from cos_monotone_0_pi[OF this] show ?thesis
    unfolding cos_minus .
qed

lemma cos_monotone_minus_pi_0':
  assumes "-pi \<le> y" and "y \<le> x" and "x \<le> 0"
  shows "cos y \<le> cos x"
proof (cases "y < x")
  case True
  show ?thesis using cos_monotone_minus_pi_0[OF `-pi \<le> y` True `x \<le> 0`]
    by auto
next
  case False
  hence "y = x" using `y \<le> x` by auto
  thus ?thesis by auto
qed

lemma sin_monotone_2pi':
  assumes "- (pi / 2) \<le> y" and "y \<le> x" and "x \<le> pi / 2"
  shows "sin y \<le> sin x"
proof -
  have "0 \<le> y + pi / 2" and "y + pi / 2 \<le> x + pi / 2" and "x + pi /2 \<le> pi"
    using pi_ge_two and assms by auto
  from cos_monotone_0_pi'[OF this] show ?thesis
    unfolding minus_sin_cos_eq[symmetric] by auto
qed


subsection {* Tangent *}

definition tan :: "real \<Rightarrow> real"
  where "tan = (\<lambda>x. sin x / cos x)"

lemma tan_zero [simp]: "tan 0 = 0"
  by (simp add: tan_def)

lemma tan_pi [simp]: "tan pi = 0"
  by (simp add: tan_def)

lemma tan_npi [simp]: "tan (real (n::nat) * pi) = 0"
  by (simp add: tan_def)

lemma tan_minus [simp]: "tan (-x) = - tan x"
  by (simp add: tan_def)

lemma tan_periodic [simp]: "tan (x + 2*pi) = tan x"
  by (simp add: tan_def)

lemma lemma_tan_add1:
  "\<lbrakk>cos x \<noteq> 0; cos y \<noteq> 0\<rbrakk> \<Longrightarrow> 1 - tan x * tan y = cos (x + y)/(cos x * cos y)"
  by (simp add: tan_def cos_add field_simps)

lemma add_tan_eq:
  "\<lbrakk>cos x \<noteq> 0; cos y \<noteq> 0\<rbrakk> \<Longrightarrow> tan x + tan y = sin(x + y)/(cos x * cos y)"
  by (simp add: tan_def sin_add field_simps)

lemma tan_add:
     "[| cos x \<noteq> 0; cos y \<noteq> 0; cos (x + y) \<noteq> 0 |]
      ==> tan(x + y) = (tan(x) + tan(y))/(1 - tan(x) * tan(y))"
  by (simp add: add_tan_eq lemma_tan_add1, simp add: tan_def)

lemma tan_double:
     "[| cos x \<noteq> 0; cos (2 * x) \<noteq> 0 |]
      ==> tan (2 * x) = (2 * tan x) / (1 - (tan x)\<^sup>2)"
  using tan_add [of x x] by (simp add: power2_eq_square)

lemma tan_gt_zero: "[| 0 < x; x < pi/2 |] ==> 0 < tan x"
  by (simp add: tan_def zero_less_divide_iff sin_gt_zero2 cos_gt_zero_pi)

lemma tan_less_zero:
  assumes lb: "- pi/2 < x" and "x < 0"
  shows "tan x < 0"
proof -
  have "0 < tan (- x)" using assms by (simp only: tan_gt_zero)
  thus ?thesis by simp
qed

lemma tan_half: "tan x = sin (2 * x) / (cos (2 * x) + 1)"
  unfolding tan_def sin_double cos_double sin_squared_eq
  by (simp add: power2_eq_square)

lemma DERIV_tan [simp]: "cos x \<noteq> 0 \<Longrightarrow> DERIV tan x :> inverse ((cos x)\<^sup>2)"
  unfolding tan_def
  by (auto intro!: DERIV_intros, simp add: divide_inverse power2_eq_square)

lemma isCont_tan: "cos x \<noteq> 0 \<Longrightarrow> isCont tan x"
  by (rule DERIV_tan [THEN DERIV_isCont])

lemma isCont_tan' [simp]:
  "\<lbrakk>isCont f a; cos (f a) \<noteq> 0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. tan (f x)) a"
  by (rule isCont_o2 [OF _ isCont_tan])

lemma tendsto_tan [tendsto_intros]:
  "\<lbrakk>(f ---> a) F; cos a \<noteq> 0\<rbrakk> \<Longrightarrow> ((\<lambda>x. tan (f x)) ---> tan a) F"
  by (rule isCont_tendsto_compose [OF isCont_tan])

lemma continuous_tan:
  "continuous F f \<Longrightarrow> cos (f (Lim F (\<lambda>x. x))) \<noteq> 0 \<Longrightarrow> continuous F (\<lambda>x. tan (f x))"
  unfolding continuous_def by (rule tendsto_tan)

lemma isCont_tan'' [continuous_intros]:
  "continuous (at x) f \<Longrightarrow> cos (f x) \<noteq> 0 \<Longrightarrow> continuous (at x) (\<lambda>x. tan (f x))"
  unfolding continuous_at by (rule tendsto_tan)

lemma continuous_within_tan [continuous_intros]:
  "continuous (at x within s) f \<Longrightarrow> cos (f x) \<noteq> 0 \<Longrightarrow> continuous (at x within s) (\<lambda>x. tan (f x))"
  unfolding continuous_within by (rule tendsto_tan)

lemma continuous_on_tan [continuous_on_intros]:
  "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. cos (f x) \<noteq> 0) \<Longrightarrow> continuous_on s (\<lambda>x. tan (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_tan)

lemma LIM_cos_div_sin: "(\<lambda>x. cos(x)/sin(x)) -- pi/2 --> 0"
  by (rule LIM_cong_limit, (rule tendsto_intros)+, simp_all)

lemma lemma_tan_total: "0 < y ==> \<exists>x. 0 < x & x < pi/2 & y < tan x"
  apply (cut_tac LIM_cos_div_sin)
  apply (simp only: LIM_eq)
  apply (drule_tac x = "inverse y" in spec, safe, force)
  apply (drule_tac ?d1.0 = s in pi_half_gt_zero [THEN [2] real_lbound_gt_zero], safe)
  apply (rule_tac x = "(pi/2) - e" in exI)
  apply (simp (no_asm_simp))
  apply (drule_tac x = "(pi/2) - e" in spec)
  apply (auto simp add: tan_def sin_diff cos_diff)
  apply (rule inverse_less_iff_less [THEN iffD1])
  apply (auto simp add: divide_inverse)
  apply (rule mult_pos_pos)
  apply (subgoal_tac [3] "0 < sin e & 0 < cos e")
  apply (auto intro: cos_gt_zero sin_gt_zero2 simp add: mult_commute)
  done

lemma tan_total_pos: "0 \<le> y ==> \<exists>x. 0 \<le> x & x < pi/2 & tan x = y"
  apply (frule order_le_imp_less_or_eq, safe)
   prefer 2 apply force
  apply (drule lemma_tan_total, safe)
  apply (cut_tac f = tan and a = 0 and b = x and y = y in IVT_objl)
  apply (auto intro!: DERIV_tan [THEN DERIV_isCont])
  apply (drule_tac y = xa in order_le_imp_less_or_eq)
  apply (auto dest: cos_gt_zero)
  done

lemma lemma_tan_total1: "\<exists>x. -(pi/2) < x & x < (pi/2) & tan x = y"
  apply (cut_tac linorder_linear [of 0 y], safe)
  apply (drule tan_total_pos)
  apply (cut_tac [2] y="-y" in tan_total_pos, safe)
  apply (rule_tac [3] x = "-x" in exI)
  apply (auto del: exI intro!: exI)
  done

lemma tan_total: "EX! x. -(pi/2) < x & x < (pi/2) & tan x = y"
  apply (cut_tac y = y in lemma_tan_total1, auto)
  apply (cut_tac x = xa and y = y in linorder_less_linear, auto)
  apply (subgoal_tac [2] "\<exists>z. y < z & z < xa & DERIV tan z :> 0")
  apply (subgoal_tac "\<exists>z. xa < z & z < y & DERIV tan z :> 0")
  apply (rule_tac [4] Rolle)
  apply (rule_tac [2] Rolle)
  apply (auto del: exI intro!: DERIV_tan DERIV_isCont exI
              simp add: differentiable_def)
  txt{*Now, simulate TRYALL*}
  apply (rule_tac [!] DERIV_tan asm_rl)
  apply (auto dest!: DERIV_unique [OF _ DERIV_tan]
              simp add: cos_gt_zero_pi [THEN less_imp_neq, THEN not_sym])
  done

lemma tan_monotone:
  assumes "- (pi / 2) < y" and "y < x" and "x < pi / 2"
  shows "tan y < tan x"
proof -
  have "\<forall>x'. y \<le> x' \<and> x' \<le> x \<longrightarrow> DERIV tan x' :> inverse ((cos x')\<^sup>2)"
  proof (rule allI, rule impI)
    fix x' :: real
    assume "y \<le> x' \<and> x' \<le> x"
    hence "-(pi/2) < x'" and "x' < pi/2" using assms by auto
    from cos_gt_zero_pi[OF this]
    have "cos x' \<noteq> 0" by auto
    thus "DERIV tan x' :> inverse ((cos x')\<^sup>2)" by (rule DERIV_tan)
  qed
  from MVT2[OF `y < x` this]
  obtain z where "y < z" and "z < x"
    and tan_diff: "tan x - tan y = (x - y) * inverse ((cos z)\<^sup>2)" by auto
  hence "- (pi / 2) < z" and "z < pi / 2" using assms by auto
  hence "0 < cos z" using cos_gt_zero_pi by auto
  hence inv_pos: "0 < inverse ((cos z)\<^sup>2)" by auto
  have "0 < x - y" using `y < x` by auto
  from mult_pos_pos [OF this inv_pos]
  have "0 < tan x - tan y" unfolding tan_diff by auto
  thus ?thesis by auto
qed

lemma tan_monotone':
  assumes "- (pi / 2) < y"
    and "y < pi / 2"
    and "- (pi / 2) < x"
    and "x < pi / 2"
  shows "(y < x) = (tan y < tan x)"
proof
  assume "y < x"
  thus "tan y < tan x"
    using tan_monotone and `- (pi / 2) < y` and `x < pi / 2` by auto
next
  assume "tan y < tan x"
  show "y < x"
  proof (rule ccontr)
    assume "\<not> y < x" hence "x \<le> y" by auto
    hence "tan x \<le> tan y"
    proof (cases "x = y")
      case True thus ?thesis by auto
    next
      case False hence "x < y" using `x \<le> y` by auto
      from tan_monotone[OF `- (pi/2) < x` this `y < pi / 2`] show ?thesis by auto
    qed
    thus False using `tan y < tan x` by auto
  qed
qed

lemma tan_inverse: "1 / (tan y) = tan (pi / 2 - y)"
  unfolding tan_def sin_cos_eq[of y] cos_sin_eq[of y] by auto

lemma tan_periodic_pi[simp]: "tan (x + pi) = tan x"
  by (simp add: tan_def)

lemma tan_periodic_nat[simp]:
  fixes n :: nat
  shows "tan (x + real n * pi) = tan x"
proof (induct n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have split_pi_off: "x + real (Suc n) * pi = (x + real n * pi) + pi"
    unfolding Suc_eq_plus1 real_of_nat_add real_of_one distrib_right by auto
  show ?case unfolding split_pi_off using Suc by auto
qed

lemma tan_periodic_int[simp]: fixes i :: int shows "tan (x + real i * pi) = tan x"
proof (cases "0 \<le> i")
  case True
  hence i_nat: "real i = real (nat i)" by auto
  show ?thesis unfolding i_nat by auto
next
  case False
  hence i_nat: "real i = - real (nat (-i))" by auto
  have "tan x = tan (x + real i * pi - real i * pi)"
    by auto
  also have "\<dots> = tan (x + real i * pi)"
    unfolding i_nat mult_minus_left diff_minus_eq_add by (rule tan_periodic_nat)
  finally show ?thesis by auto
qed

lemma tan_periodic_n[simp]: "tan (x + numeral n * pi) = tan x"
  using tan_periodic_int[of _ "numeral n" ] unfolding real_numeral .

subsection {* Inverse Trigonometric Functions *}

definition arcsin :: "real => real"
  where "arcsin y = (THE x. -(pi/2) \<le> x & x \<le> pi/2 & sin x = y)"

definition arccos :: "real => real"
  where "arccos y = (THE x. 0 \<le> x & x \<le> pi & cos x = y)"

definition arctan :: "real => real"
  where "arctan y = (THE x. -(pi/2) < x & x < pi/2 & tan x = y)"

lemma arcsin:
  "-1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow>
    -(pi/2) \<le> arcsin y & arcsin y \<le> pi/2 & sin(arcsin y) = y"
  unfolding arcsin_def by (rule theI' [OF sin_total])

lemma arcsin_pi:
  "-1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> -(pi/2) \<le> arcsin y & arcsin y \<le> pi & sin(arcsin y) = y"
  apply (drule (1) arcsin)
  apply (force intro: order_trans)
  done

lemma sin_arcsin [simp]: "-1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> sin(arcsin y) = y"
  by (blast dest: arcsin)

lemma arcsin_bounded: "-1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> -(pi/2) \<le> arcsin y & arcsin y \<le> pi/2"
  by (blast dest: arcsin)

lemma arcsin_lbound: "-1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> -(pi/2) \<le> arcsin y"
  by (blast dest: arcsin)

lemma arcsin_ubound: "-1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> arcsin y \<le> pi/2"
  by (blast dest: arcsin)

lemma arcsin_lt_bounded:
     "[| -1 < y; y < 1 |] ==> -(pi/2) < arcsin y & arcsin y < pi/2"
  apply (frule order_less_imp_le)
  apply (frule_tac y = y in order_less_imp_le)
  apply (frule arcsin_bounded)
  apply (safe, simp)
  apply (drule_tac y = "arcsin y" in order_le_imp_less_or_eq)
  apply (drule_tac [2] y = "pi/2" in order_le_imp_less_or_eq, safe)
  apply (drule_tac [!] f = sin in arg_cong, auto)
  done

lemma arcsin_sin: "[|-(pi/2) \<le> x; x \<le> pi/2 |] ==> arcsin(sin x) = x"
  apply (unfold arcsin_def)
  apply (rule the1_equality)
  apply (rule sin_total, auto)
  done

lemma arccos:
     "[| -1 \<le> y; y \<le> 1 |]
      ==> 0 \<le> arccos y & arccos y \<le> pi & cos(arccos y) = y"
  unfolding arccos_def by (rule theI' [OF cos_total])

lemma cos_arccos [simp]: "[| -1 \<le> y; y \<le> 1 |] ==> cos(arccos y) = y"
  by (blast dest: arccos)

lemma arccos_bounded: "[| -1 \<le> y; y \<le> 1 |] ==> 0 \<le> arccos y & arccos y \<le> pi"
  by (blast dest: arccos)

lemma arccos_lbound: "[| -1 \<le> y; y \<le> 1 |] ==> 0 \<le> arccos y"
  by (blast dest: arccos)

lemma arccos_ubound: "[| -1 \<le> y; y \<le> 1 |] ==> arccos y \<le> pi"
  by (blast dest: arccos)

lemma arccos_lt_bounded:
     "[| -1 < y; y < 1 |]
      ==> 0 < arccos y & arccos y < pi"
  apply (frule order_less_imp_le)
  apply (frule_tac y = y in order_less_imp_le)
  apply (frule arccos_bounded, auto)
  apply (drule_tac y = "arccos y" in order_le_imp_less_or_eq)
  apply (drule_tac [2] y = pi in order_le_imp_less_or_eq, auto)
  apply (drule_tac [!] f = cos in arg_cong, auto)
  done

lemma arccos_cos: "[|0 \<le> x; x \<le> pi |] ==> arccos(cos x) = x"
  apply (simp add: arccos_def)
  apply (auto intro!: the1_equality cos_total)
  done

lemma arccos_cos2: "[|x \<le> 0; -pi \<le> x |] ==> arccos(cos x) = -x"
  apply (simp add: arccos_def)
  apply (auto intro!: the1_equality cos_total)
  done

lemma cos_arcsin: "\<lbrakk>-1 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> cos (arcsin x) = sqrt (1 - x\<^sup>2)"
  apply (subgoal_tac "x\<^sup>2 \<le> 1")
  apply (rule power2_eq_imp_eq)
  apply (simp add: cos_squared_eq)
  apply (rule cos_ge_zero)
  apply (erule (1) arcsin_lbound)
  apply (erule (1) arcsin_ubound)
  apply simp
  apply (subgoal_tac "\<bar>x\<bar>\<^sup>2 \<le> 1\<^sup>2", simp)
  apply (rule power_mono, simp, simp)
  done

lemma sin_arccos: "\<lbrakk>-1 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> sin (arccos x) = sqrt (1 - x\<^sup>2)"
  apply (subgoal_tac "x\<^sup>2 \<le> 1")
  apply (rule power2_eq_imp_eq)
  apply (simp add: sin_squared_eq)
  apply (rule sin_ge_zero)
  apply (erule (1) arccos_lbound)
  apply (erule (1) arccos_ubound)
  apply simp
  apply (subgoal_tac "\<bar>x\<bar>\<^sup>2 \<le> 1\<^sup>2", simp)
  apply (rule power_mono, simp, simp)
  done

lemma arctan [simp]: "- (pi/2) < arctan y  & arctan y < pi/2 & tan (arctan y) = y"
  unfolding arctan_def by (rule theI' [OF tan_total])

lemma tan_arctan: "tan (arctan y) = y"
  by auto

lemma arctan_bounded: "- (pi/2) < arctan y  & arctan y < pi/2"
  by (auto simp only: arctan)

lemma arctan_lbound: "- (pi/2) < arctan y"
  by auto

lemma arctan_ubound: "arctan y < pi/2"
  by (auto simp only: arctan)

lemma arctan_unique:
  assumes "-(pi/2) < x"
    and "x < pi/2"
    and "tan x = y"
  shows "arctan y = x"
  using assms arctan [of y] tan_total [of y] by (fast elim: ex1E)

lemma arctan_tan: "-(pi/2) < x \<Longrightarrow> x < pi/2 \<Longrightarrow> arctan (tan x) = x"
  by (rule arctan_unique) simp_all

lemma arctan_zero_zero [simp]: "arctan 0 = 0"
  by (rule arctan_unique) simp_all

lemma arctan_minus: "arctan (- x) = - arctan x"
  apply (rule arctan_unique)
  apply (simp only: neg_less_iff_less arctan_ubound)
  apply (metis minus_less_iff arctan_lbound)
  apply simp
  done

lemma cos_arctan_not_zero [simp]: "cos (arctan x) \<noteq> 0"
  by (intro less_imp_neq [symmetric] cos_gt_zero_pi
    arctan_lbound arctan_ubound)

lemma cos_arctan: "cos (arctan x) = 1 / sqrt (1 + x\<^sup>2)"
proof (rule power2_eq_imp_eq)
  have "0 < 1 + x\<^sup>2" by (simp add: add_pos_nonneg)
  show "0 \<le> 1 / sqrt (1 + x\<^sup>2)" by simp
  show "0 \<le> cos (arctan x)"
    by (intro less_imp_le cos_gt_zero_pi arctan_lbound arctan_ubound)
  have "(cos (arctan x))\<^sup>2 * (1 + (tan (arctan x))\<^sup>2) = 1"
    unfolding tan_def by (simp add: distrib_left power_divide)
  thus "(cos (arctan x))\<^sup>2 = (1 / sqrt (1 + x\<^sup>2))\<^sup>2"
    using `0 < 1 + x\<^sup>2` by (simp add: power_divide eq_divide_eq)
qed

lemma sin_arctan: "sin (arctan x) = x / sqrt (1 + x\<^sup>2)"
  using add_pos_nonneg [OF zero_less_one zero_le_power2 [of x]]
  using tan_arctan [of x] unfolding tan_def cos_arctan
  by (simp add: eq_divide_eq)

lemma tan_sec: "cos x \<noteq> 0 ==> 1 + (tan x)\<^sup>2 = (inverse (cos x))\<^sup>2"
  apply (rule power_inverse [THEN subst])
  apply (rule_tac c1 = "(cos x)\<^sup>2" in real_mult_right_cancel [THEN iffD1])
  apply (auto dest: field_power_not_zero
          simp add: power_mult_distrib distrib_right power_divide tan_def
                    mult_assoc power_inverse [symmetric])
  done

lemma arctan_less_iff: "arctan x < arctan y \<longleftrightarrow> x < y"
  by (metis tan_monotone' arctan_lbound arctan_ubound tan_arctan)

lemma arctan_le_iff: "arctan x \<le> arctan y \<longleftrightarrow> x \<le> y"
  by (simp only: not_less [symmetric] arctan_less_iff)

lemma arctan_eq_iff: "arctan x = arctan y \<longleftrightarrow> x = y"
  by (simp only: eq_iff [where 'a=real] arctan_le_iff)

lemma zero_less_arctan_iff [simp]: "0 < arctan x \<longleftrightarrow> 0 < x"
  using arctan_less_iff [of 0 x] by simp

lemma arctan_less_zero_iff [simp]: "arctan x < 0 \<longleftrightarrow> x < 0"
  using arctan_less_iff [of x 0] by simp

lemma zero_le_arctan_iff [simp]: "0 \<le> arctan x \<longleftrightarrow> 0 \<le> x"
  using arctan_le_iff [of 0 x] by simp

lemma arctan_le_zero_iff [simp]: "arctan x \<le> 0 \<longleftrightarrow> x \<le> 0"
  using arctan_le_iff [of x 0] by simp

lemma arctan_eq_zero_iff [simp]: "arctan x = 0 \<longleftrightarrow> x = 0"
  using arctan_eq_iff [of x 0] by simp

lemma continuous_on_arcsin': "continuous_on {-1 .. 1} arcsin"
proof -
  have "continuous_on (sin ` {- pi / 2 .. pi / 2}) arcsin"
    by (rule continuous_on_inv) (auto intro: continuous_on_intros simp: arcsin_sin)
  also have "sin ` {- pi / 2 .. pi / 2} = {-1 .. 1}"
  proof safe
    fix x :: real
    assume "x \<in> {-1..1}"
    then show "x \<in> sin ` {- pi / 2..pi / 2}"
      using arcsin_lbound arcsin_ubound
      by (intro image_eqI[where x="arcsin x"]) auto
  qed simp
  finally show ?thesis .
qed

lemma continuous_on_arcsin [continuous_on_intros]:
  "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. -1 \<le> f x \<and> f x \<le> 1) \<Longrightarrow> continuous_on s (\<lambda>x. arcsin (f x))"
  using continuous_on_compose[of s f, OF _ continuous_on_subset[OF  continuous_on_arcsin']]
  by (auto simp: comp_def subset_eq)

lemma isCont_arcsin: "-1 < x \<Longrightarrow> x < 1 \<Longrightarrow> isCont arcsin x"
  using continuous_on_arcsin'[THEN continuous_on_subset, of "{ -1 <..< 1 }"]
  by (auto simp: continuous_on_eq_continuous_at subset_eq)

lemma continuous_on_arccos': "continuous_on {-1 .. 1} arccos"
proof -
  have "continuous_on (cos ` {0 .. pi}) arccos"
    by (rule continuous_on_inv) (auto intro: continuous_on_intros simp: arccos_cos)
  also have "cos ` {0 .. pi} = {-1 .. 1}"
  proof safe
    fix x :: real
    assume "x \<in> {-1..1}"
    then show "x \<in> cos ` {0..pi}"
      using arccos_lbound arccos_ubound
      by (intro image_eqI[where x="arccos x"]) auto
  qed simp
  finally show ?thesis .
qed

lemma continuous_on_arccos [continuous_on_intros]:
  "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. -1 \<le> f x \<and> f x \<le> 1) \<Longrightarrow> continuous_on s (\<lambda>x. arccos (f x))"
  using continuous_on_compose[of s f, OF _ continuous_on_subset[OF  continuous_on_arccos']]
  by (auto simp: comp_def subset_eq)

lemma isCont_arccos: "-1 < x \<Longrightarrow> x < 1 \<Longrightarrow> isCont arccos x"
  using continuous_on_arccos'[THEN continuous_on_subset, of "{ -1 <..< 1 }"]
  by (auto simp: continuous_on_eq_continuous_at subset_eq)

lemma isCont_arctan: "isCont arctan x"
  apply (rule arctan_lbound [of x, THEN dense, THEN exE], clarify)
  apply (rule arctan_ubound [of x, THEN dense, THEN exE], clarify)
  apply (subgoal_tac "isCont arctan (tan (arctan x))", simp)
  apply (erule (1) isCont_inverse_function2 [where f=tan])
  apply (metis arctan_tan order_le_less_trans order_less_le_trans)
  apply (metis cos_gt_zero_pi isCont_tan order_less_le_trans less_le)
  done

lemma tendsto_arctan [tendsto_intros]: "(f ---> x) F \<Longrightarrow> ((\<lambda>x. arctan (f x)) ---> arctan x) F"
  by (rule isCont_tendsto_compose [OF isCont_arctan])

lemma continuous_arctan [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. arctan (f x))"
  unfolding continuous_def by (rule tendsto_arctan)

lemma continuous_on_arctan [continuous_on_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. arctan (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_arctan)

lemma DERIV_arcsin:
  "\<lbrakk>-1 < x; x < 1\<rbrakk> \<Longrightarrow> DERIV arcsin x :> inverse (sqrt (1 - x\<^sup>2))"
  apply (rule DERIV_inverse_function [where f=sin and a="-1" and b="1"])
  apply (rule DERIV_cong [OF DERIV_sin])
  apply (simp add: cos_arcsin)
  apply (subgoal_tac "\<bar>x\<bar>\<^sup>2 < 1\<^sup>2", simp)
  apply (rule power_strict_mono, simp, simp, simp)
  apply assumption
  apply assumption
  apply simp
  apply (erule (1) isCont_arcsin)
  done

lemma DERIV_arccos:
  "\<lbrakk>-1 < x; x < 1\<rbrakk> \<Longrightarrow> DERIV arccos x :> inverse (- sqrt (1 - x\<^sup>2))"
  apply (rule DERIV_inverse_function [where f=cos and a="-1" and b="1"])
  apply (rule DERIV_cong [OF DERIV_cos])
  apply (simp add: sin_arccos)
  apply (subgoal_tac "\<bar>x\<bar>\<^sup>2 < 1\<^sup>2", simp)
  apply (rule power_strict_mono, simp, simp, simp)
  apply assumption
  apply assumption
  apply simp
  apply (erule (1) isCont_arccos)
  done

lemma DERIV_arctan: "DERIV arctan x :> inverse (1 + x\<^sup>2)"
  apply (rule DERIV_inverse_function [where f=tan and a="x - 1" and b="x + 1"])
  apply (rule DERIV_cong [OF DERIV_tan])
  apply (rule cos_arctan_not_zero)
  apply (simp add: power_inverse tan_sec [symmetric])
  apply (subgoal_tac "0 < 1 + x\<^sup>2", simp)
  apply (simp add: add_pos_nonneg)
  apply (simp, simp, simp, rule isCont_arctan)
  done

declare
  DERIV_arcsin[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]
  DERIV_arccos[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]
  DERIV_arctan[THEN DERIV_chain2, THEN DERIV_cong, DERIV_intros]

lemma filterlim_tan_at_right: "filterlim tan at_bot (at_right (- pi/2))"
  by (rule filterlim_at_bot_at_right[where Q="\<lambda>x. - pi/2 < x \<and> x < pi/2" and P="\<lambda>x. True" and g=arctan])
     (auto simp: le_less eventually_at dist_real_def simp del: less_divide_eq_numeral1
           intro!: tan_monotone exI[of _ "pi/2"])

lemma filterlim_tan_at_left: "filterlim tan at_top (at_left (pi/2))"
  by (rule filterlim_at_top_at_left[where Q="\<lambda>x. - pi/2 < x \<and> x < pi/2" and P="\<lambda>x. True" and g=arctan])
     (auto simp: le_less eventually_at dist_real_def simp del: less_divide_eq_numeral1
           intro!: tan_monotone exI[of _ "pi/2"])

lemma tendsto_arctan_at_top: "(arctan ---> (pi/2)) at_top"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  def y \<equiv> "pi/2 - min (pi/2) e"
  then have y: "0 \<le> y" "y < pi/2" "pi/2 \<le> e + y"
    using `0 < e` by auto

  show "eventually (\<lambda>x. dist (arctan x) (pi / 2) < e) at_top"
  proof (intro eventually_at_top_dense[THEN iffD2] exI allI impI)
    fix x
    assume "tan y < x"
    then have "arctan (tan y) < arctan x"
      by (simp add: arctan_less_iff)
    with y have "y < arctan x"
      by (subst (asm) arctan_tan) simp_all
    with arctan_ubound[of x, arith] y `0 < e`
    show "dist (arctan x) (pi / 2) < e"
      by (simp add: dist_real_def)
  qed
qed

lemma tendsto_arctan_at_bot: "(arctan ---> - (pi/2)) at_bot"
  unfolding filterlim_at_bot_mirror arctan_minus
  by (intro tendsto_minus tendsto_arctan_at_top)


subsection {* More Theorems about Sin and Cos *}

lemma cos_45: "cos (pi / 4) = sqrt 2 / 2"
proof -
  let ?c = "cos (pi / 4)" and ?s = "sin (pi / 4)"
  have nonneg: "0 \<le> ?c"
    by (simp add: cos_ge_zero)
  have "0 = cos (pi / 4 + pi / 4)"
    by simp
  also have "cos (pi / 4 + pi / 4) = ?c\<^sup>2 - ?s\<^sup>2"
    by (simp only: cos_add power2_eq_square)
  also have "\<dots> = 2 * ?c\<^sup>2 - 1"
    by (simp add: sin_squared_eq)
  finally have "?c\<^sup>2 = (sqrt 2 / 2)\<^sup>2"
    by (simp add: power_divide)
  thus ?thesis
    using nonneg by (rule power2_eq_imp_eq) simp
qed

lemma cos_30: "cos (pi / 6) = sqrt 3 / 2"
proof -
  let ?c = "cos (pi / 6)" and ?s = "sin (pi / 6)"
  have pos_c: "0 < ?c"
    by (rule cos_gt_zero, simp, simp)
  have "0 = cos (pi / 6 + pi / 6 + pi / 6)"
    by simp
  also have "\<dots> = (?c * ?c - ?s * ?s) * ?c - (?s * ?c + ?c * ?s) * ?s"
    by (simp only: cos_add sin_add)
  also have "\<dots> = ?c * (?c\<^sup>2 - 3 * ?s\<^sup>2)"
    by (simp add: algebra_simps power2_eq_square)
  finally have "?c\<^sup>2 = (sqrt 3 / 2)\<^sup>2"
    using pos_c by (simp add: sin_squared_eq power_divide)
  thus ?thesis
    using pos_c [THEN order_less_imp_le]
    by (rule power2_eq_imp_eq) simp
qed

lemma sin_45: "sin (pi / 4) = sqrt 2 / 2"
  by (simp add: sin_cos_eq cos_45)

lemma sin_60: "sin (pi / 3) = sqrt 3 / 2"
  by (simp add: sin_cos_eq cos_30)

lemma cos_60: "cos (pi / 3) = 1 / 2"
  apply (rule power2_eq_imp_eq)
  apply (simp add: cos_squared_eq sin_60 power_divide)
  apply (rule cos_ge_zero, rule order_trans [where y=0], simp_all)
  done

lemma sin_30: "sin (pi / 6) = 1 / 2"
  by (simp add: sin_cos_eq cos_60)

lemma tan_30: "tan (pi / 6) = 1 / sqrt 3"
  unfolding tan_def by (simp add: sin_30 cos_30)

lemma tan_45: "tan (pi / 4) = 1"
  unfolding tan_def by (simp add: sin_45 cos_45)

lemma tan_60: "tan (pi / 3) = sqrt 3"
  unfolding tan_def by (simp add: sin_60 cos_60)

lemma sin_cos_npi [simp]: "sin (real (Suc (2 * n)) * pi / 2) = (-1) ^ n"
proof -
  have "sin ((real n + 1/2) * pi) = cos (real n * pi)"
    by (auto simp add: algebra_simps sin_add)
  thus ?thesis
    by (simp add: real_of_nat_Suc distrib_right add_divide_distrib
                  mult_commute [of pi])
qed

lemma cos_2npi [simp]: "cos (2 * real (n::nat) * pi) = 1"
  by (simp add: cos_double mult_assoc power_add [symmetric] numeral_2_eq_2)

lemma cos_3over2_pi [simp]: "cos (3 / 2 * pi) = 0"
  apply (subgoal_tac "cos (pi + pi/2) = 0", simp)
  apply (subst cos_add, simp)
  done

lemma sin_2npi [simp]: "sin (2 * real (n::nat) * pi) = 0"
  by (auto simp add: mult_assoc)

lemma sin_3over2_pi [simp]: "sin (3 / 2 * pi) = - 1"
  apply (subgoal_tac "sin (pi + pi/2) = - 1", simp)
  apply (subst sin_add, simp)
  done

lemma cos_pi_eq_zero [simp]: "cos (pi * real (Suc (2 * m)) / 2) = 0"
  apply (simp only: cos_add sin_add real_of_nat_Suc distrib_right distrib_left add_divide_distrib)
  apply auto
  done

lemma DERIV_cos_add [simp]: "DERIV (\<lambda>x. cos (x + k)) xa :> - sin (xa + k)"
  by (auto intro!: DERIV_intros)

lemma sin_zero_abs_cos_one: "sin x = 0 ==> \<bar>cos x\<bar> = 1"
  by (auto simp add: sin_zero_iff even_mult_two_ex)

lemma cos_one_sin_zero: "cos x = 1 ==> sin x = 0"
  using sin_cos_squared_add3 [where x = x] by auto


subsection {* Machins formula *}

lemma arctan_one: "arctan 1 = pi / 4"
  by (rule arctan_unique, simp_all add: tan_45 m2pi_less_pi)

lemma tan_total_pi4:
  assumes "\<bar>x\<bar> < 1"
  shows "\<exists>z. - (pi / 4) < z \<and> z < pi / 4 \<and> tan z = x"
proof
  show "- (pi / 4) < arctan x \<and> arctan x < pi / 4 \<and> tan (arctan x) = x"
    unfolding arctan_one [symmetric] arctan_minus [symmetric]
    unfolding arctan_less_iff using assms by auto
qed

lemma arctan_add:
  assumes "\<bar>x\<bar> \<le> 1" and "\<bar>y\<bar> < 1"
  shows "arctan x + arctan y = arctan ((x + y) / (1 - x * y))"
proof (rule arctan_unique [symmetric])
  have "- (pi / 4) \<le> arctan x" and "- (pi / 4) < arctan y"
    unfolding arctan_one [symmetric] arctan_minus [symmetric]
    unfolding arctan_le_iff arctan_less_iff using assms by auto
  from add_le_less_mono [OF this]
  show 1: "- (pi / 2) < arctan x + arctan y" by simp
  have "arctan x \<le> pi / 4" and "arctan y < pi / 4"
    unfolding arctan_one [symmetric]
    unfolding arctan_le_iff arctan_less_iff using assms by auto
  from add_le_less_mono [OF this]
  show 2: "arctan x + arctan y < pi / 2" by simp
  show "tan (arctan x + arctan y) = (x + y) / (1 - x * y)"
    using cos_gt_zero_pi [OF 1 2] by (simp add: tan_add)
qed

theorem machin: "pi / 4 = 4 * arctan (1/5) - arctan (1 / 239)"
proof -
  have "\<bar>1 / 5\<bar> < (1 :: real)" by auto
  from arctan_add[OF less_imp_le[OF this] this]
  have "2 * arctan (1 / 5) = arctan (5 / 12)" by auto
  moreover
  have "\<bar>5 / 12\<bar> < (1 :: real)" by auto
  from arctan_add[OF less_imp_le[OF this] this]
  have "2 * arctan (5 / 12) = arctan (120 / 119)" by auto
  moreover
  have "\<bar>1\<bar> \<le> (1::real)" and "\<bar>1 / 239\<bar> < (1::real)" by auto
  from arctan_add[OF this]
  have "arctan 1 + arctan (1 / 239) = arctan (120 / 119)" by auto
  ultimately have "arctan 1 + arctan (1 / 239) = 4 * arctan (1 / 5)" by auto
  thus ?thesis unfolding arctan_one by algebra
qed


subsection {* Introducing the arcus tangens power series *}

lemma monoseq_arctan_series:
  fixes x :: real
  assumes "\<bar>x\<bar> \<le> 1"
  shows "monoseq (\<lambda> n. 1 / real (n*2+1) * x^(n*2+1))" (is "monoseq ?a")
proof (cases "x = 0")
  case True
  thus ?thesis unfolding monoseq_def One_nat_def by auto
next
  case False
  have "norm x \<le> 1" and "x \<le> 1" and "-1 \<le> x" using assms by auto
  show "monoseq ?a"
  proof -
    {
      fix n
      fix x :: real
      assume "0 \<le> x" and "x \<le> 1"
      have "1 / real (Suc (Suc n * 2)) * x ^ Suc (Suc n * 2) \<le>
        1 / real (Suc (n * 2)) * x ^ Suc (n * 2)"
      proof (rule mult_mono)
        show "1 / real (Suc (Suc n * 2)) \<le> 1 / real (Suc (n * 2))"
          by (rule frac_le) simp_all
        show "0 \<le> 1 / real (Suc (n * 2))"
          by auto
        show "x ^ Suc (Suc n * 2) \<le> x ^ Suc (n * 2)"
          by (rule power_decreasing) (simp_all add: `0 \<le> x` `x \<le> 1`)
        show "0 \<le> x ^ Suc (Suc n * 2)"
          by (rule zero_le_power) (simp add: `0 \<le> x`)
      qed
    } note mono = this

    show ?thesis
    proof (cases "0 \<le> x")
      case True from mono[OF this `x \<le> 1`, THEN allI]
      show ?thesis unfolding Suc_eq_plus1[symmetric]
        by (rule mono_SucI2)
    next
      case False
      hence "0 \<le> -x" and "-x \<le> 1" using `-1 \<le> x` by auto
      from mono[OF this]
      have "\<And>n. 1 / real (Suc (Suc n * 2)) * x ^ Suc (Suc n * 2) \<ge>
        1 / real (Suc (n * 2)) * x ^ Suc (n * 2)" using `0 \<le> -x` by auto
      thus ?thesis unfolding Suc_eq_plus1[symmetric] by (rule mono_SucI1[OF allI])
    qed
  qed
qed

lemma zeroseq_arctan_series:
  fixes x :: real
  assumes "\<bar>x\<bar> \<le> 1"
  shows "(\<lambda> n. 1 / real (n*2+1) * x^(n*2+1)) ----> 0" (is "?a ----> 0")
proof (cases "x = 0")
  case True
  thus ?thesis
    unfolding One_nat_def by (auto simp add: tendsto_const)
next
  case False
  have "norm x \<le> 1" and "x \<le> 1" and "-1 \<le> x" using assms by auto
  show "?a ----> 0"
  proof (cases "\<bar>x\<bar> < 1")
    case True
    hence "norm x < 1" by auto
    from tendsto_mult[OF LIMSEQ_inverse_real_of_nat LIMSEQ_power_zero[OF `norm x < 1`, THEN LIMSEQ_Suc]]
    have "(\<lambda>n. 1 / real (n + 1) * x ^ (n + 1)) ----> 0"
      unfolding inverse_eq_divide Suc_eq_plus1 by simp
    then show ?thesis using pos2 by (rule LIMSEQ_linear)
  next
    case False
    hence "x = -1 \<or> x = 1" using `\<bar>x\<bar> \<le> 1` by auto
    hence n_eq: "\<And> n. x ^ (n * 2 + 1) = x"
      unfolding One_nat_def by auto
    from tendsto_mult[OF LIMSEQ_inverse_real_of_nat[THEN LIMSEQ_linear, OF pos2, unfolded inverse_eq_divide] tendsto_const[of x]]
    show ?thesis unfolding n_eq Suc_eq_plus1 by auto
  qed
qed

lemma summable_arctan_series:
  fixes x :: real and n :: nat
  assumes "\<bar>x\<bar> \<le> 1"
  shows "summable (\<lambda> k. (-1)^k * (1 / real (k*2+1) * x ^ (k*2+1)))"
  (is "summable (?c x)")
  by (rule summable_Leibniz(1), rule zeroseq_arctan_series[OF assms], rule monoseq_arctan_series[OF assms])

lemma less_one_imp_sqr_less_one:
  fixes x :: real
  assumes "\<bar>x\<bar> < 1"
  shows "x\<^sup>2 < 1"
proof -
  have "\<bar>x\<^sup>2\<bar> < 1"
    by (metis abs_power2 assms pos2 power2_abs power_0 power_strict_decreasing zero_eq_power2 zero_less_abs_iff) 
  thus ?thesis using zero_le_power2 by auto
qed

lemma DERIV_arctan_series:
  assumes "\<bar> x \<bar> < 1"
  shows "DERIV (\<lambda> x'. \<Sum> k. (-1)^k * (1 / real (k*2+1) * x' ^ (k*2+1))) x :> (\<Sum> k. (-1)^k * x^(k*2))"
  (is "DERIV ?arctan _ :> ?Int")
proof -
  let ?f = "\<lambda>n. if even n then (-1)^(n div 2) * 1 / real (Suc n) else 0"

  have n_even: "\<And>n :: nat. even n \<Longrightarrow> 2 * (n div 2) = n"
    by presburger
  then have if_eq: "\<And>n x'. ?f n * real (Suc n) * x'^n =
    (if even n then (-1)^(n div 2) * x'^(2 * (n div 2)) else 0)"
    by auto

  {
    fix x :: real
    assume "\<bar>x\<bar> < 1"
    hence "x\<^sup>2 < 1" by (rule less_one_imp_sqr_less_one)
    have "summable (\<lambda> n. -1 ^ n * (x\<^sup>2) ^n)"
      by (rule summable_Leibniz(1), auto intro!: LIMSEQ_realpow_zero monoseq_realpow `x\<^sup>2 < 1` order_less_imp_le[OF `x\<^sup>2 < 1`])
    hence "summable (\<lambda> n. -1 ^ n * x^(2*n))" unfolding power_mult .
  } note summable_Integral = this

  {
    fix f :: "nat \<Rightarrow> real"
    have "\<And>x. f sums x = (\<lambda> n. if even n then f (n div 2) else 0) sums x"
    proof
      fix x :: real
      assume "f sums x"
      from sums_if[OF sums_zero this]
      show "(\<lambda>n. if even n then f (n div 2) else 0) sums x"
        by auto
    next
      fix x :: real
      assume "(\<lambda> n. if even n then f (n div 2) else 0) sums x"
      from LIMSEQ_linear[OF this[unfolded sums_def] pos2, unfolded sum_split_even_odd[unfolded mult_commute]]
      show "f sums x" unfolding sums_def by auto
    qed
    hence "op sums f = op sums (\<lambda> n. if even n then f (n div 2) else 0)" ..
  } note sums_even = this

  have Int_eq: "(\<Sum>n. ?f n * real (Suc n) * x^n) = ?Int"
    unfolding if_eq mult_commute[of _ 2] suminf_def sums_even[of "\<lambda> n. -1 ^ n * x ^ (2 * n)", symmetric]
    by auto

  {
    fix x :: real
    have if_eq': "\<And>n. (if even n then -1 ^ (n div 2) * 1 / real (Suc n) else 0) * x ^ Suc n =
      (if even n then -1 ^ (n div 2) * (1 / real (Suc (2 * (n div 2))) * x ^ Suc (2 * (n div 2))) else 0)"
      using n_even by auto
    have idx_eq: "\<And>n. n * 2 + 1 = Suc (2 * n)" by auto
    have "(\<Sum>n. ?f n * x^(Suc n)) = ?arctan x"
      unfolding if_eq' idx_eq suminf_def sums_even[of "\<lambda> n. -1 ^ n * (1 / real (Suc (2 * n)) * x ^ Suc (2 * n))", symmetric]
      by auto
  } note arctan_eq = this

  have "DERIV (\<lambda> x. \<Sum> n. ?f n * x^(Suc n)) x :> (\<Sum> n. ?f n * real (Suc n) * x^n)"
  proof (rule DERIV_power_series')
    show "x \<in> {- 1 <..< 1}" using `\<bar> x \<bar> < 1` by auto
    {
      fix x' :: real
      assume x'_bounds: "x' \<in> {- 1 <..< 1}"
      hence "\<bar>x'\<bar> < 1" by auto

      let ?S = "\<Sum> n. (-1)^n * x'^(2 * n)"
      show "summable (\<lambda> n. ?f n * real (Suc n) * x'^n)" unfolding if_eq
        by (rule sums_summable[where l="0 + ?S"], rule sums_if, rule sums_zero, rule summable_sums, rule summable_Integral[OF `\<bar>x'\<bar> < 1`])
    }
  qed auto
  thus ?thesis unfolding Int_eq arctan_eq .
qed

lemma arctan_series:
  assumes "\<bar> x \<bar> \<le> 1"
  shows "arctan x = (\<Sum>k. (-1)^k * (1 / real (k*2+1) * x ^ (k*2+1)))"
  (is "_ = suminf (\<lambda> n. ?c x n)")
proof -
  let ?c' = "\<lambda>x n. (-1)^n * x^(n*2)"

  {
    fix r x :: real
    assume "0 < r" and "r < 1" and "\<bar> x \<bar> < r"
    have "\<bar>x\<bar> < 1" using `r < 1` and `\<bar>x\<bar> < r` by auto
    from DERIV_arctan_series[OF this] have "DERIV (\<lambda> x. suminf (?c x)) x :> (suminf (?c' x))" .
  } note DERIV_arctan_suminf = this

  {
    fix x :: real
    assume "\<bar>x\<bar> \<le> 1"
    note summable_Leibniz[OF zeroseq_arctan_series[OF this] monoseq_arctan_series[OF this]]
  } note arctan_series_borders = this

  {
    fix x :: real
    assume "\<bar>x\<bar> < 1"
    have "arctan x = (\<Sum>k. ?c x k)"
    proof -
      obtain r where "\<bar>x\<bar> < r" and "r < 1"
        using dense[OF `\<bar>x\<bar> < 1`] by blast
      hence "0 < r" and "-r < x" and "x < r" by auto

      have suminf_eq_arctan_bounded: "\<And>x a b. \<lbrakk> -r < a ; b < r ; a < b ; a \<le> x ; x \<le> b \<rbrakk> \<Longrightarrow>
        suminf (?c x) - arctan x = suminf (?c a) - arctan a"
      proof -
        fix x a b
        assume "-r < a" and "b < r" and "a < b" and "a \<le> x" and "x \<le> b"
        hence "\<bar>x\<bar> < r" by auto
        show "suminf (?c x) - arctan x = suminf (?c a) - arctan a"
        proof (rule DERIV_isconst2[of "a" "b"])
          show "a < b" and "a \<le> x" and "x \<le> b"
            using `a < b` `a \<le> x` `x \<le> b` by auto
          have "\<forall>x. -r < x \<and> x < r \<longrightarrow> DERIV (\<lambda> x. suminf (?c x) - arctan x) x :> 0"
          proof (rule allI, rule impI)
            fix x
            assume "-r < x \<and> x < r"
            hence "\<bar>x\<bar> < r" by auto
            hence "\<bar>x\<bar> < 1" using `r < 1` by auto
            have "\<bar> - (x\<^sup>2) \<bar> < 1"
              using less_one_imp_sqr_less_one[OF `\<bar>x\<bar> < 1`] by auto
            hence "(\<lambda> n. (- (x\<^sup>2)) ^ n) sums (1 / (1 - (- (x\<^sup>2))))"
              unfolding real_norm_def[symmetric] by (rule geometric_sums)
            hence "(?c' x) sums (1 / (1 - (- (x\<^sup>2))))"
              unfolding power_mult_distrib[symmetric] power_mult nat_mult_commute[of _ 2] by auto
            hence suminf_c'_eq_geom: "inverse (1 + x\<^sup>2) = suminf (?c' x)"
              using sums_unique unfolding inverse_eq_divide by auto
            have "DERIV (\<lambda> x. suminf (?c x)) x :> (inverse (1 + x\<^sup>2))"
              unfolding suminf_c'_eq_geom
              by (rule DERIV_arctan_suminf[OF `0 < r` `r < 1` `\<bar>x\<bar> < r`])
            from DERIV_add_minus[OF this DERIV_arctan]
            show "DERIV (\<lambda> x. suminf (?c x) - arctan x) x :> 0"
              by auto
          qed
          hence DERIV_in_rball: "\<forall> y. a \<le> y \<and> y \<le> b \<longrightarrow> DERIV (\<lambda> x. suminf (?c x) - arctan x) y :> 0"
            using `-r < a` `b < r` by auto
          thus "\<forall> y. a < y \<and> y < b \<longrightarrow> DERIV (\<lambda> x. suminf (?c x) - arctan x) y :> 0"
            using `\<bar>x\<bar> < r` by auto
          show "\<forall> y. a \<le> y \<and> y \<le> b \<longrightarrow> isCont (\<lambda> x. suminf (?c x) - arctan x) y"
            using DERIV_in_rball DERIV_isCont by auto
        qed
      qed

      have suminf_arctan_zero: "suminf (?c 0) - arctan 0 = 0"
        unfolding Suc_eq_plus1[symmetric] power_Suc2 mult_zero_right arctan_zero_zero suminf_zero
        by auto

      have "suminf (?c x) - arctan x = 0"
      proof (cases "x = 0")
        case True
        thus ?thesis using suminf_arctan_zero by auto
      next
        case False
        hence "0 < \<bar>x\<bar>" and "- \<bar>x\<bar> < \<bar>x\<bar>" by auto
        have "suminf (?c (-\<bar>x\<bar>)) - arctan (-\<bar>x\<bar>) = suminf (?c 0) - arctan 0"
          by (rule suminf_eq_arctan_bounded[where x="0" and a="-\<bar>x\<bar>" and b="\<bar>x\<bar>", symmetric])
            (simp_all only: `\<bar>x\<bar> < r` `-\<bar>x\<bar> < \<bar>x\<bar>` neg_less_iff_less)
        moreover
        have "suminf (?c x) - arctan x = suminf (?c (-\<bar>x\<bar>)) - arctan (-\<bar>x\<bar>)"
          by (rule suminf_eq_arctan_bounded[where x="x" and a="-\<bar>x\<bar>" and b="\<bar>x\<bar>"])
             (simp_all only: `\<bar>x\<bar> < r` `-\<bar>x\<bar> < \<bar>x\<bar>` neg_less_iff_less)
        ultimately
        show ?thesis using suminf_arctan_zero by auto
      qed
      thus ?thesis by auto
    qed
  } note when_less_one = this

  show "arctan x = suminf (\<lambda> n. ?c x n)"
  proof (cases "\<bar>x\<bar> < 1")
    case True
    thus ?thesis by (rule when_less_one)
  next
    case False
    hence "\<bar>x\<bar> = 1" using `\<bar>x\<bar> \<le> 1` by auto
    let ?a = "\<lambda>x n. \<bar>1 / real (n*2+1) * x^(n*2+1)\<bar>"
    let ?diff = "\<lambda> x n. \<bar> arctan x - (\<Sum> i = 0..<n. ?c x i)\<bar>"
    {
      fix n :: nat
      have "0 < (1 :: real)" by auto
      moreover
      {
        fix x :: real
        assume "0 < x" and "x < 1"
        hence "\<bar>x\<bar> \<le> 1" and "\<bar>x\<bar> < 1" by auto
        from `0 < x` have "0 < 1 / real (0 * 2 + (1::nat)) * x ^ (0 * 2 + 1)"
          by auto
        note bounds = mp[OF arctan_series_borders(2)[OF `\<bar>x\<bar> \<le> 1`] this, unfolded when_less_one[OF `\<bar>x\<bar> < 1`, symmetric], THEN spec]
        have "0 < 1 / real (n*2+1) * x^(n*2+1)"
          by (rule mult_pos_pos, auto simp only: zero_less_power[OF `0 < x`], auto)
        hence a_pos: "?a x n = 1 / real (n*2+1) * x^(n*2+1)"
          by (rule abs_of_pos)
        have "?diff x n \<le> ?a x n"
        proof (cases "even n")
          case True
          hence sgn_pos: "(-1)^n = (1::real)" by auto
          from `even n` obtain m where "2 * m = n"
            unfolding even_mult_two_ex by auto
          from bounds[of m, unfolded this atLeastAtMost_iff]
          have "\<bar>arctan x - (\<Sum>i = 0..<n. (?c x i))\<bar> \<le> (\<Sum>i = 0..<n + 1. (?c x i)) - (\<Sum>i = 0..<n. (?c x i))"
            by auto
          also have "\<dots> = ?c x n" unfolding One_nat_def by auto
          also have "\<dots> = ?a x n" unfolding sgn_pos a_pos by auto
          finally show ?thesis .
        next
          case False
          hence sgn_neg: "(-1)^n = (-1::real)" by auto
          from `odd n` obtain m where m_def: "2 * m + 1 = n"
            unfolding odd_Suc_mult_two_ex by auto
          hence m_plus: "2 * (m + 1) = n + 1" by auto
          from bounds[of "m + 1", unfolded this atLeastAtMost_iff, THEN conjunct1] bounds[of m, unfolded m_def atLeastAtMost_iff, THEN conjunct2]
          have "\<bar>arctan x - (\<Sum>i = 0..<n. (?c x i))\<bar> \<le> (\<Sum>i = 0..<n. (?c x i)) - (\<Sum>i = 0..<n+1. (?c x i))"
            by auto
          also have "\<dots> = - ?c x n" unfolding One_nat_def by auto
          also have "\<dots> = ?a x n" unfolding sgn_neg a_pos by auto
          finally show ?thesis .
        qed
        hence "0 \<le> ?a x n - ?diff x n" by auto
      }
      hence "\<forall> x \<in> { 0 <..< 1 }. 0 \<le> ?a x n - ?diff x n" by auto
      moreover have "\<And>x. isCont (\<lambda> x. ?a x n - ?diff x n) x"
        unfolding diff_conv_add_uminus divide_inverse
        by (auto intro!: isCont_add isCont_rabs isCont_ident isCont_minus isCont_arctan
          isCont_inverse isCont_mult isCont_power isCont_const isCont_setsum
          simp del: add_uminus_conv_diff)
      ultimately have "0 \<le> ?a 1 n - ?diff 1 n"
        by (rule LIM_less_bound)
      hence "?diff 1 n \<le> ?a 1 n" by auto
    }
    have "?a 1 ----> 0"
      unfolding tendsto_rabs_zero_iff power_one divide_inverse One_nat_def
      by (auto intro!: tendsto_mult LIMSEQ_linear LIMSEQ_inverse_real_of_nat)
    have "?diff 1 ----> 0"
    proof (rule LIMSEQ_I)
      fix r :: real
      assume "0 < r"
      obtain N :: nat where N_I: "\<And>n. N \<le> n \<Longrightarrow> ?a 1 n < r"
        using LIMSEQ_D[OF `?a 1 ----> 0` `0 < r`] by auto
      {
        fix n
        assume "N \<le> n" from `?diff 1 n \<le> ?a 1 n` N_I[OF this]
        have "norm (?diff 1 n - 0) < r" by auto
      }
      thus "\<exists> N. \<forall> n \<ge> N. norm (?diff 1 n - 0) < r" by blast
    qed
    from this [unfolded tendsto_rabs_zero_iff, THEN tendsto_add [OF _ tendsto_const], of "- arctan 1", THEN tendsto_minus]
    have "(?c 1) sums (arctan 1)" unfolding sums_def by auto
    hence "arctan 1 = (\<Sum> i. ?c 1 i)" by (rule sums_unique)

    show ?thesis
    proof (cases "x = 1")
      case True
      then show ?thesis by (simp add: `arctan 1 = (\<Sum> i. ?c 1 i)`)
    next
      case False
      hence "x = -1" using `\<bar>x\<bar> = 1` by auto

      have "- (pi / 2) < 0" using pi_gt_zero by auto
      have "- (2 * pi) < 0" using pi_gt_zero by auto

      have c_minus_minus: "\<And>i. ?c (- 1) i = - ?c 1 i"
        unfolding One_nat_def by auto

      have "arctan (- 1) = arctan (tan (-(pi / 4)))"
        unfolding tan_45 tan_minus ..
      also have "\<dots> = - (pi / 4)"
        by (rule arctan_tan, auto simp add: order_less_trans[OF `- (pi / 2) < 0` pi_gt_zero])
      also have "\<dots> = - (arctan (tan (pi / 4)))"
        unfolding neg_equal_iff_equal by (rule arctan_tan[symmetric], auto simp add: order_less_trans[OF `- (2 * pi) < 0` pi_gt_zero])
      also have "\<dots> = - (arctan 1)"
        unfolding tan_45 ..
      also have "\<dots> = - (\<Sum> i. ?c 1 i)"
        using `arctan 1 = (\<Sum> i. ?c 1 i)` by auto
      also have "\<dots> = (\<Sum> i. ?c (- 1) i)"
        using suminf_minus[OF sums_summable[OF `(?c 1) sums (arctan 1)`]]
        unfolding c_minus_minus by auto
      finally show ?thesis using `x = -1` by auto
    qed
  qed
qed

lemma arctan_half:
  fixes x :: real
  shows "arctan x = 2 * arctan (x / (1 + sqrt(1 + x\<^sup>2)))"
proof -
  obtain y where low: "- (pi / 2) < y" and high: "y < pi / 2" and y_eq: "tan y = x"
    using tan_total by blast
  hence low2: "- (pi / 2) < y / 2" and high2: "y / 2 < pi / 2"
    by auto

  have divide_nonzero_divide: "\<And>A B C :: real. C \<noteq> 0 \<Longrightarrow> A / B = (A / C) / (B / C)"
    by auto

  have "0 < cos y" using cos_gt_zero_pi[OF low high] .
  hence "cos y \<noteq> 0" and cos_sqrt: "sqrt ((cos y)\<^sup>2) = cos y"
    by auto

  have "1 + (tan y)\<^sup>2 = 1 + (sin y)\<^sup>2 / (cos y)\<^sup>2"
    unfolding tan_def power_divide ..
  also have "\<dots> = (cos y)\<^sup>2 / (cos y)\<^sup>2 + (sin y)\<^sup>2 / (cos y)\<^sup>2"
    using `cos y \<noteq> 0` by auto
  also have "\<dots> = 1 / (cos y)\<^sup>2"
    unfolding add_divide_distrib[symmetric] sin_cos_squared_add2 ..
  finally have "1 + (tan y)\<^sup>2 = 1 / (cos y)\<^sup>2" .

  have "sin y / (cos y + 1) = tan y / ((cos y + 1) / cos y)"
    unfolding tan_def divide_nonzero_divide[OF `cos y \<noteq> 0`, symmetric] ..
  also have "\<dots> = tan y / (1 + 1 / cos y)"
    using `cos y \<noteq> 0` unfolding add_divide_distrib by auto
  also have "\<dots> = tan y / (1 + 1 / sqrt ((cos y)\<^sup>2))"
    unfolding cos_sqrt ..
  also have "\<dots> = tan y / (1 + sqrt (1 / (cos y)\<^sup>2))"
    unfolding real_sqrt_divide by auto
  finally have eq: "sin y / (cos y + 1) = tan y / (1 + sqrt(1 + (tan y)\<^sup>2))"
    unfolding `1 + (tan y)\<^sup>2 = 1 / (cos y)\<^sup>2` .

  have "arctan x = y"
    using arctan_tan low high y_eq by auto
  also have "\<dots> = 2 * (arctan (tan (y/2)))"
    using arctan_tan[OF low2 high2] by auto
  also have "\<dots> = 2 * (arctan (sin y / (cos y + 1)))"
    unfolding tan_half by auto
  finally show ?thesis
    unfolding eq `tan y = x` .
qed

lemma arctan_monotone: "x < y \<Longrightarrow> arctan x < arctan y"
  by (simp only: arctan_less_iff)

lemma arctan_monotone': "x \<le> y \<Longrightarrow> arctan x \<le> arctan y"
  by (simp only: arctan_le_iff)

lemma arctan_inverse:
  assumes "x \<noteq> 0"
  shows "arctan (1 / x) = sgn x * pi / 2 - arctan x"
proof (rule arctan_unique)
  show "- (pi / 2) < sgn x * pi / 2 - arctan x"
    using arctan_bounded [of x] assms
    unfolding sgn_real_def
    apply (auto simp add: algebra_simps)
    apply (drule zero_less_arctan_iff [THEN iffD2])
    apply arith
    done
  show "sgn x * pi / 2 - arctan x < pi / 2"
    using arctan_bounded [of "- x"] assms
    unfolding sgn_real_def arctan_minus
    by (auto simp add: algebra_simps)
  show "tan (sgn x * pi / 2 - arctan x) = 1 / x"
    unfolding tan_inverse [of "arctan x", unfolded tan_arctan]
    unfolding sgn_real_def
    by (simp add: tan_def cos_arctan sin_arctan sin_diff cos_diff)
qed

theorem pi_series: "pi / 4 = (\<Sum> k. (-1)^k * 1 / real (k*2+1))" (is "_ = ?SUM")
proof -
  have "pi / 4 = arctan 1" using arctan_one by auto
  also have "\<dots> = ?SUM" using arctan_series[of 1] by auto
  finally show ?thesis by auto
qed


subsection {* Existence of Polar Coordinates *}

lemma cos_x_y_le_one: "\<bar>x / sqrt (x\<^sup>2 + y\<^sup>2)\<bar> \<le> 1"
  apply (rule power2_le_imp_le [OF _ zero_le_one])
  apply (simp add: power_divide divide_le_eq not_sum_power2_lt_zero)
  done

lemma cos_arccos_abs: "\<bar>y\<bar> \<le> 1 \<Longrightarrow> cos (arccos y) = y"
  by (simp add: abs_le_iff)

lemma sin_arccos_abs: "\<bar>y\<bar> \<le> 1 \<Longrightarrow> sin (arccos y) = sqrt (1 - y\<^sup>2)"
  by (simp add: sin_arccos abs_le_iff)

lemmas cos_arccos_lemma1 = cos_arccos_abs [OF cos_x_y_le_one]

lemmas sin_arccos_lemma1 = sin_arccos_abs [OF cos_x_y_le_one]

lemma polar_Ex: "\<exists>r a. x = r * cos a & y = r * sin a"
proof -
  have polar_ex1: "\<And>y. 0 < y \<Longrightarrow> \<exists>r a. x = r * cos a & y = r * sin a"
    apply (rule_tac x = "sqrt (x\<^sup>2 + y\<^sup>2)" in exI)
    apply (rule_tac x = "arccos (x / sqrt (x\<^sup>2 + y\<^sup>2))" in exI)
    apply (simp add: cos_arccos_lemma1 sin_arccos_lemma1 power_divide
                     real_sqrt_mult [symmetric] right_diff_distrib)
    done
  show ?thesis
  proof (cases "0::real" y rule: linorder_cases)
    case less 
      then show ?thesis by (rule polar_ex1)
  next
    case equal
      then show ?thesis
        by (force simp add: intro!: cos_zero sin_zero)
  next
    case greater
      then show ?thesis 
     using polar_ex1 [where y="-y"]
    by auto (metis cos_minus minus_minus minus_mult_right sin_minus)
  qed
qed

end
