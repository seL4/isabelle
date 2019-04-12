(*  Title:    HOL/Analysis/Integral_Test.thy
    Author:   Manuel Eberl, TU München
*)

section \<open>Integral Test for Summability\<close>

theory Integral_Test
imports Henstock_Kurzweil_Integration
begin

text \<open>
  The integral test for summability. We show here that for a decreasing non-negative
  function, the infinite sum over that function evaluated at the natural numbers
  converges iff the corresponding integral converges.

  As a useful side result, we also provide some results on the difference between
  the integral and the partial sum. (This is useful e.g. for the definition of the
  Euler-Mascheroni constant)
\<close>

(* TODO: continuous_in \<rightarrow> integrable_on *)
locale\<^marker>\<open>tag important\<close> antimono_fun_sum_integral_diff =
  fixes f :: "real \<Rightarrow> real"
  assumes dec: "\<And>x y. x \<ge> 0 \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<ge> f y"
  assumes nonneg: "\<And>x. x \<ge> 0 \<Longrightarrow> f x \<ge> 0"
  assumes cont: "continuous_on {0..} f"
begin

definition "sum_integral_diff_series n = (\<Sum>k\<le>n. f (of_nat k)) - (integral {0..of_nat n} f)"

lemma sum_integral_diff_series_nonneg:
  "sum_integral_diff_series n \<ge> 0"
proof -
  note int = integrable_continuous_real[OF continuous_on_subset[OF cont]]
  let ?int = "\<lambda>a b. integral {of_nat a..of_nat b} f"
  have "-sum_integral_diff_series n = ?int 0 n - (\<Sum>k\<le>n. f (of_nat k))"
    by (simp add: sum_integral_diff_series_def)
  also have "?int 0 n = (\<Sum>k<n. ?int k (Suc k))"
  proof (induction n)
    case (Suc n)
    have "?int 0 (Suc n) = ?int 0 n + ?int n (Suc n)"
      by (intro integral_combine[symmetric] int) simp_all
    with Suc show ?case by simp
  qed simp_all
  also have "... \<le> (\<Sum>k<n. integral {of_nat k..of_nat (Suc k)} (\<lambda>_::real. f (of_nat k)))"
    by (intro sum_mono integral_le int) (auto intro: dec)
  also have "... = (\<Sum>k<n. f (of_nat k))" by simp
  also have "\<dots> - (\<Sum>k\<le>n. f (of_nat k)) = -(\<Sum>k\<in>{..n} - {..<n}. f (of_nat k))"
    by (subst sum_diff) auto
  also have "\<dots> \<le> 0" by (auto intro!: sum_nonneg nonneg)
  finally show "sum_integral_diff_series n \<ge> 0" by simp
qed

lemma sum_integral_diff_series_antimono:
  assumes "m \<le> n"
  shows   "sum_integral_diff_series m \<ge> sum_integral_diff_series n"
proof -
  let ?int = "\<lambda>a b. integral {of_nat a..of_nat b} f"
  note int = integrable_continuous_real[OF continuous_on_subset[OF cont]]
  have d_mono: "sum_integral_diff_series (Suc n) \<le> sum_integral_diff_series n" for n
  proof -
    fix n :: nat
    have "sum_integral_diff_series (Suc n) - sum_integral_diff_series n =
            f (of_nat (Suc n)) + (?int 0 n - ?int 0 (Suc n))"
      unfolding sum_integral_diff_series_def by (simp add: algebra_simps)
    also have "?int 0 n - ?int 0 (Suc n) = -?int n (Suc n)"
      by (subst integral_combine [symmetric, of "of_nat 0" "of_nat n" "of_nat (Suc n)"])
         (auto intro!: int simp: algebra_simps)
    also have "?int n (Suc n) \<ge> integral {of_nat n..of_nat (Suc n)} (\<lambda>_::real. f (of_nat (Suc n)))"
      by (intro integral_le int) (auto intro: dec)
    hence "f (of_nat (Suc n)) + -?int n (Suc n) \<le> 0" by (simp add: algebra_simps)
    finally show "sum_integral_diff_series (Suc n) \<le> sum_integral_diff_series n" by simp
  qed
  with assms show ?thesis
    by (induction rule: inc_induct) (auto intro: order.trans[OF _ d_mono])
qed

lemma sum_integral_diff_series_Bseq: "Bseq sum_integral_diff_series"
proof -
  from sum_integral_diff_series_nonneg and sum_integral_diff_series_antimono
    have "norm (sum_integral_diff_series n) \<le> sum_integral_diff_series 0" for n by simp
  thus "Bseq sum_integral_diff_series" by (rule BseqI')
qed

lemma sum_integral_diff_series_monoseq: "monoseq sum_integral_diff_series"
  using sum_integral_diff_series_antimono unfolding monoseq_def by blast

lemma sum_integral_diff_series_convergent: "convergent sum_integral_diff_series"
  using sum_integral_diff_series_Bseq sum_integral_diff_series_monoseq
  by (blast intro!: Bseq_monoseq_convergent)

theorem integral_test:
  "summable (\<lambda>n. f (of_nat n)) \<longleftrightarrow> convergent (\<lambda>n. integral {0..of_nat n} f)"
proof -
  have "summable (\<lambda>n. f (of_nat n)) \<longleftrightarrow> convergent (\<lambda>n. \<Sum>k\<le>n. f (of_nat k))"
    by (simp add: summable_iff_convergent')
  also have "... \<longleftrightarrow> convergent (\<lambda>n. integral {0..of_nat n} f)"
  proof
    assume "convergent (\<lambda>n. \<Sum>k\<le>n. f (of_nat k))"
    from convergent_diff[OF this sum_integral_diff_series_convergent]
      show "convergent (\<lambda>n. integral {0..of_nat n} f)"
        unfolding sum_integral_diff_series_def by simp
  next
    assume "convergent (\<lambda>n. integral {0..of_nat n} f)"
    from convergent_add[OF this sum_integral_diff_series_convergent]
      show "convergent (\<lambda>n. \<Sum>k\<le>n. f (of_nat k))" unfolding sum_integral_diff_series_def by simp
  qed
  finally show ?thesis by simp
qed

end

end
