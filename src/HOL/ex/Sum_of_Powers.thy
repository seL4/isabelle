(*  Author:     Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)
section \<open>Sum of Powers\<close>

theory Sum_of_Powers
imports Complex_Main
begin

subsection \<open>Additions to \<^theory>\<open>HOL.Binomial\<close> Theory\<close>

lemma (in field_char_0) one_plus_of_nat_neq_zero [simp]:
  "1 + of_nat n \<noteq> 0"
proof -
  have "of_nat (Suc n) \<noteq> of_nat 0"
    unfolding of_nat_eq_iff by simp
  then show ?thesis by simp
qed

lemma of_nat_binomial_eq_mult_binomial_Suc:
  assumes "k \<le> n"
  shows "(of_nat :: (nat \<Rightarrow> ('a :: field_char_0))) (n choose k) = of_nat (n + 1 - k) / of_nat (n + 1) * of_nat (Suc n choose k)"
proof (cases k)
  case 0 then show ?thesis by simp
next
  case (Suc l)
  have "of_nat (n + 1) * (\<Prod>i=0..<k. of_nat (n - i)) = (of_nat :: (nat \<Rightarrow> 'a)) (n + 1 - k) * (\<Prod>i=0..<k. of_nat (Suc n - i))"
    using prod.atLeast0_lessThan_Suc [where ?'a = 'a, symmetric, of "\<lambda>i. of_nat (Suc n - i)" k]
    by (simp add: ac_simps prod.atLeast0_lessThan_Suc_shift)
  also have "... = (of_nat :: (nat \<Rightarrow> 'a)) (Suc n - k) * (\<Prod>i=0..<k. of_nat (Suc n - i))"
    by (simp add: Suc atLeast0_atMost_Suc atLeastLessThanSuc_atLeastAtMost)
  also have "... = (of_nat :: (nat \<Rightarrow> 'a)) (n + 1 - k) * (\<Prod>i=0..<k. of_nat (Suc n - i))"
    by (simp only: Suc_eq_plus1)
  finally have "(\<Prod>i=0..<k. of_nat (n - i)) = (of_nat :: (nat \<Rightarrow> 'a)) (n + 1 - k) / of_nat (n + 1) * (\<Prod>i=0..<k. of_nat (Suc n - i))"
    by (simp add: field_simps)
  with assms show ?thesis
    by (simp add: binomial_altdef_of_nat prod_dividef)
qed

lemma real_binomial_eq_mult_binomial_Suc:
  assumes "k \<le> n"
  shows "(n choose k) = (n + 1 - k) / (n + 1) * (Suc n choose k)"
by (metis Suc_eq_plus1 add.commute assms le_SucI of_nat_Suc of_nat_binomial_eq_mult_binomial_Suc of_nat_diff)

subsection \<open>Preliminaries\<close>

lemma integrals_eq:
  assumes "f 0 = g 0"
  assumes "\<And> x. ((\<lambda>x. f x - g x) has_real_derivative 0) (at x)"
  shows "f x = g x"
proof -
  show "f x = g x"
  proof (cases "x \<noteq> 0")
    case True
    from assms DERIV_const_ratio_const[OF this, of "\<lambda>x. f x - g x" 0]
    show ?thesis by auto
  qed (simp add: assms)
qed

lemma sum_diff: "((\<Sum>i\<le>n::nat. f (i + 1) - f i)::'a::field) = f (n + 1) - f 0"
by (induct n) (auto simp add: field_simps)

declare One_nat_def [simp del]

subsection \<open>Bernoulli Numbers and Bernoulli Polynomials\<close>

declare sum.cong [fundef_cong]

fun bernoulli :: "nat \<Rightarrow> real"
where
  "bernoulli 0 = (1::real)"
| "bernoulli (Suc n) =  (-1 / (n + 2)) * (\<Sum>k \<le> n. ((n + 2 choose k) * bernoulli k))"

declare bernoulli.simps[simp del]

definition
  "bernpoly n = (\<lambda>x. \<Sum>k \<le> n. (n choose k) * bernoulli k * x ^ (n - k))"

subsection \<open>Basic Observations on Bernoulli Polynomials\<close>

lemma bernpoly_0: "bernpoly n 0 = bernoulli n"
proof (cases n)
  case 0
  then show "bernpoly n 0 = bernoulli n"
    unfolding bernpoly_def bernoulli.simps by auto
next
  case (Suc n')
  have "(\<Sum>k\<le>n'. real (Suc n' choose k) * bernoulli k * 0 ^ (Suc n' - k)) = 0"
    by (rule sum.neutral) auto
  with Suc show ?thesis
    unfolding bernpoly_def by simp
qed

lemma sum_binomial_times_bernoulli:
  "(\<Sum>k\<le>n. ((Suc n) choose k) * bernoulli k) = (if n = 0 then 1 else 0)"
proof (cases n)
  case 0
  then show ?thesis by (simp add: bernoulli.simps)
next
  case Suc
  then show ?thesis
  by (simp add: bernoulli.simps)
    (simp add: field_simps add_2_eq_Suc'[symmetric] del: add_2_eq_Suc add_2_eq_Suc')
qed

subsection \<open>Sum of Powers with Bernoulli Polynomials\<close>

lemma bernpoly_derivative [derivative_intros]:
  "(bernpoly (Suc n) has_real_derivative ((n + 1) * bernpoly n x)) (at x)"
proof -
  have "(bernpoly (Suc n) has_real_derivative (\<Sum>k\<le>n. real (Suc n - k) * x ^ (n - k) * (real (Suc n choose k) * bernoulli k))) (at x)"
    unfolding bernpoly_def by (rule DERIV_cong) (fast intro!: derivative_intros, simp)
  moreover have "(\<Sum>k\<le>n. real (Suc n - k) * x ^ (n - k) * (real (Suc n choose k) * bernoulli k)) = (n + 1) * bernpoly n x"
    unfolding bernpoly_def
    by (auto intro: sum.cong simp add: sum_distrib_left real_binomial_eq_mult_binomial_Suc[of _ n] Suc_eq_plus1 of_nat_diff)
  ultimately show ?thesis by auto
qed

lemma diff_bernpoly:
  "bernpoly n (x + 1) - bernpoly n x = n * x ^ (n - 1)"
proof (induct n arbitrary: x)
  case 0
  show ?case unfolding bernpoly_def by auto
next
  case (Suc n)
  have "bernpoly (Suc n) (0 + 1) - bernpoly (Suc n) 0 = (Suc n) * 0 ^ n"
    unfolding bernpoly_0 unfolding bernpoly_def by (simp add: sum_binomial_times_bernoulli zero_power)
  then have const: "bernpoly (Suc n) (0 + 1) - bernpoly (Suc n) 0 = real (Suc n) * 0 ^ n" by (simp add: power_0_left)
  have hyps': "\<And>x. (real n + 1) * bernpoly n (x + 1) - (real n + 1) * bernpoly n x = real n * x ^ (n - Suc 0) * real (Suc n)"
    unfolding right_diff_distrib[symmetric] by (simp add: Suc.hyps One_nat_def)
  note [derivative_intros] = DERIV_chain'[where f = "\<lambda>x::real. x + 1" and g = "bernpoly (Suc n)" and s="UNIV"]
  have derivative: "\<And>x. ((%x. bernpoly (Suc n) (x + 1) - bernpoly (Suc n) x - real (Suc n) * x ^ n) has_real_derivative 0) (at x)"
    by (rule DERIV_cong) (fast intro!: derivative_intros, simp add: hyps')
  from integrals_eq[OF const derivative] show ?case by simp
qed

lemma sum_of_powers: "(\<Sum>k\<le>n::nat. (real k) ^ m) = (bernpoly (Suc m) (n + 1) - bernpoly (Suc m) 0) / (m + 1)"
proof -
  from diff_bernpoly[of "Suc m", simplified] have "(m + (1::real)) * (\<Sum>k\<le>n. (real k) ^ m) = (\<Sum>k\<le>n. bernpoly (Suc m) (real k + 1) - bernpoly (Suc m) (real k))"
    by (auto simp add: sum_distrib_left intro!: sum.cong)
  also have "... = (\<Sum>k\<le>n. bernpoly (Suc m) (real (k + 1)) - bernpoly (Suc m) (real k))"
    by simp
  also have "... = bernpoly (Suc m) (n + 1) - bernpoly (Suc m) 0"
    by (simp only: sum_diff[where f="\<lambda>k. bernpoly (Suc m) (real k)"]) simp
  finally show ?thesis by (auto simp add: field_simps intro!: eq_divide_imp)
qed

subsection \<open>Instances for Square And Cubic Numbers\<close>

lemma binomial_unroll:
  "n > 0 \<Longrightarrow> (n choose k) = (if k = 0 then 1 else (n - 1) choose (k - 1) + ((n - 1) choose k))"
  by (auto simp add: gr0_conv_Suc)

lemma sum_unroll:
  "(\<Sum>k\<le>n::nat. f k) = (if n = 0 then f 0 else f n + (\<Sum>k\<le>n - 1. f k))"
by auto (metis One_nat_def Suc_pred add.commute sum_atMost_Suc)

lemma bernoulli_unroll:
  "n > 0 \<Longrightarrow> bernoulli n = - 1 / (real n + 1) * (\<Sum>k\<le>n - 1. real (n + 1 choose k) * bernoulli k)"
by (cases n) (simp add: bernoulli.simps One_nat_def)+

lemmas unroll = binomial_unroll
  bernoulli.simps(1) bernoulli_unroll sum_unroll bernpoly_def

lemma sum_of_squares: "(\<Sum>k\<le>n::nat. k ^ 2) = (2 * n ^ 3 + 3 * n ^ 2 + n) / 6"
proof -
  have "real (\<Sum>k\<le>n::nat. k ^ 2) = (\<Sum>k\<le>n::nat. (real k) ^ 2)" by simp
  also have "... = (bernpoly 3 (real (n + 1)) - bernpoly 3 0) / real (3 :: nat)"
    by (auto simp add: sum_of_powers)
  also have "... = (2 * n ^ 3 + 3 * n ^ 2 + n) / 6"
    by (simp add: unroll algebra_simps power2_eq_square power3_eq_cube One_nat_def[symmetric])
  finally show ?thesis by simp
qed

lemma sum_of_squares_nat: "(\<Sum>k\<le>n::nat. k ^ 2) = (2 * n ^ 3 + 3 * n ^ 2 + n) div 6"
proof -
  from sum_of_squares have "real (6 * (\<Sum>k\<le>n. k ^ 2)) = real (2 * n ^ 3 + 3 * n ^ 2 + n)"
    by (auto simp add: field_simps)
  then have "6 * (\<Sum>k\<le>n. k ^ 2) = 2 * n ^ 3 + 3 * n ^ 2 + n"
    using of_nat_eq_iff by blast
  then show ?thesis by auto
qed

lemma sum_of_cubes: "(\<Sum>k\<le>n::nat. k ^ 3) = (n ^ 2 + n) ^ 2 / 4"
proof -
  have two_plus_two: "2 + 2 = 4" by simp
  have power4_eq: "\<And>x::real. x ^ 4 = x * x * x * x"
    by (simp only: two_plus_two[symmetric] power_add power2_eq_square)
  have "real (\<Sum>k\<le>n::nat. k ^ 3) = (\<Sum>k\<le>n::nat. (real k) ^ 3)" by simp
  also have "... = ((bernpoly 4 (n + 1) - bernpoly 4 0)) / (real (4 :: nat))"
    by (auto simp add: sum_of_powers)
  also have "... = ((n ^ 2 + n) / 2) ^ 2"
    by (simp add: unroll algebra_simps power2_eq_square power4_eq power3_eq_cube)
  finally show ?thesis by (simp add: power_divide)
qed
                       
lemma sum_of_cubes_nat: "(\<Sum>k\<le>n::nat. k ^ 3) = (n ^ 2 + n) ^ 2 div 4"
proof -
  from sum_of_cubes have "real (4 * (\<Sum>k\<le>n. k ^ 3)) = real ((n ^ 2 + n) ^ 2)"
    by (auto simp add: field_simps)
  then have "4 * (\<Sum>k\<le>n. k ^ 3) = (n ^ 2 + n) ^ 2"
    using of_nat_eq_iff by blast
  then show ?thesis by auto
qed

end
