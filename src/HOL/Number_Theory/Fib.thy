(*  Title:      HOL/Number_Theory/Fib.thy
    Author:     Lawrence C. Paulson
    Author:     Jeremy Avigad
    Author:     Manuel Eberl
*)

section \<open>The fibonacci function\<close>

theory Fib
  imports Complex_Main
begin


subsection \<open>Fibonacci numbers\<close>

fun fib :: "nat \<Rightarrow> nat"
  where
    fib0: "fib 0 = 0"
  | fib1: "fib (Suc 0) = 1"
  | fib2: "fib (Suc (Suc n)) = fib (Suc n) + fib n"


subsection \<open>Basic Properties\<close>

lemma fib_1 [simp]: "fib 1 = 1"
  by (metis One_nat_def fib1)

lemma fib_2 [simp]: "fib 2 = 1"
  using fib.simps(3) [of 0] by (simp add: numeral_2_eq_2)

lemma fib_plus_2: "fib (n + 2) = fib (n + 1) + fib n"
  by (metis Suc_eq_plus1 add_2_eq_Suc' fib.simps(3))

lemma fib_add: "fib (Suc (n + k)) = fib (Suc k) * fib (Suc n) + fib k * fib n"
  by (induct n rule: fib.induct) (auto simp add: field_simps)

lemma fib_neq_0_nat: "n > 0 \<Longrightarrow> fib n > 0"
  by (induct n rule: fib.induct) auto


subsection \<open>More efficient code\<close>

text \<open>
  The naive approach is very inefficient since the branching recursion leads to many
  values of \<^term>\<open>fib\<close> being computed multiple times. We can avoid this by ``remembering''
  the last two values in the sequence, yielding a tail-recursive version.
  This is far from optimal (it takes roughly $O(n\cdot M(n))$ time where $M(n)$ is the
  time required to multiply two $n$-bit integers), but much better than the naive version,
  which is exponential.
\<close>

fun gen_fib :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "gen_fib a b 0 = a"
  | "gen_fib a b (Suc 0) = b"
  | "gen_fib a b (Suc (Suc n)) = gen_fib b (a + b) (Suc n)"

lemma gen_fib_recurrence: "gen_fib a b (Suc (Suc n)) = gen_fib a b n + gen_fib a b (Suc n)"
  by (induct a b n rule: gen_fib.induct) simp_all

lemma gen_fib_fib: "gen_fib (fib n) (fib (Suc n)) m = fib (n + m)"
  by (induct m rule: fib.induct) (simp_all del: gen_fib.simps(3) add: gen_fib_recurrence)

lemma fib_conv_gen_fib: "fib n = gen_fib 0 1 n"
  using gen_fib_fib[of 0 n] by simp

declare fib_conv_gen_fib [code]


subsection \<open>A Few Elementary Results\<close>

text \<open>
  \<^medskip> Concrete Mathematics, page 278: Cassini's identity.  The proof is
  much easier using integers, not natural numbers!
\<close>

lemma fib_Cassini_int: "int (fib (Suc (Suc n)) * fib n) - int((fib (Suc n))\<^sup>2) = - ((-1)^n)"
  by (induct n rule: fib.induct) (auto simp add: field_simps power2_eq_square power_add)

lemma fib_Cassini_nat:
  "fib (Suc (Suc n)) * fib n =
     (if even n then (fib (Suc n))\<^sup>2 - 1 else (fib (Suc n))\<^sup>2 + 1)"
  using fib_Cassini_int [of n] by (auto simp del: of_nat_mult of_nat_power)


subsection \<open>Law 6.111 of Concrete Mathematics\<close>

lemma coprime_fib_Suc_nat: "coprime (fib n) (fib (Suc n))"
  apply (induct n rule: fib.induct)
    apply (simp_all add: coprime_iff_gcd_eq_1 algebra_simps)
  apply (simp add: add.assoc [symmetric])
  done

lemma gcd_fib_add:
  "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
proof (cases m)
  case 0
  then show ?thesis
    by simp
next
  case (Suc q)
  from coprime_fib_Suc_nat [of q]
  have "coprime (fib (Suc q)) (fib q)"
    by (simp add: ac_simps)
  have "gcd (fib q) (fib (Suc q)) = Suc 0"
    using coprime_fib_Suc_nat [of q] by simp
  then have *: "gcd (fib n * fib q) (fib n * fib (Suc q)) = fib n"
    by (simp add: gcd_mult_distrib_nat [symmetric])
  moreover have "gcd (fib (Suc q)) (fib n * fib q + fib (Suc n) * fib (Suc q)) =
    gcd (fib (Suc q)) (fib n * fib q)"
    using gcd_add_mult [of "fib (Suc q)"] by (simp add: ac_simps)
  moreover have "gcd (fib (Suc q)) (fib n * fib (Suc q)) = fib (Suc q)"
    by simp
  ultimately show ?thesis
    using Suc \<open>coprime (fib (Suc q)) (fib q)\<close>
    by (auto simp add: fib_add algebra_simps gcd_mult_right_right_cancel)
qed

lemma gcd_fib_diff: "m \<le> n \<Longrightarrow> gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
  by (simp add: gcd_fib_add [symmetric, of _ "n-m"])

lemma gcd_fib_mod: "0 < m \<Longrightarrow> gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
proof (induct n rule: less_induct)
  case (less n)
  show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
  proof (cases "m < n")
    case True
    then have "m \<le> n" by auto
    with \<open>0 < m\<close> have "0 < n" by auto
    with \<open>0 < m\<close> \<open>m < n\<close> have *: "n - m < n" by auto
    have "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib ((n - m) mod m))"
      by (simp add: mod_if [of n]) (use \<open>m < n\<close> in auto)
    also have "\<dots> = gcd (fib m)  (fib (n - m))"
      by (simp add: less.hyps * \<open>0 < m\<close>)
    also have "\<dots> = gcd (fib m) (fib n)"
      by (simp add: gcd_fib_diff \<open>m \<le> n\<close>)
    finally show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" .
  next
    case False
    then show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
      by (cases "m = n") auto
  qed
qed

lemma fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)"  \<comment> \<open>Law 6.111\<close>
  by (induct m n rule: gcd_nat_induct) (simp_all add: gcd_non_0_nat gcd.commute gcd_fib_mod)

theorem fib_mult_eq_sum_nat: "fib (Suc n) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  by (induct n rule: nat.induct) (auto simp add:  field_simps)


subsection \<open>Closed form\<close>

lemma fib_closed_form:
  fixes \<phi> \<psi> :: real
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
    and "\<psi> \<equiv> (1 - sqrt 5) / 2"
  shows "of_nat (fib n) = (\<phi> ^ n - \<psi> ^ n) / sqrt 5"
proof (induct n rule: fib.induct)
  fix n :: nat
  assume IH1: "of_nat (fib n) = (\<phi> ^ n - \<psi> ^ n) / sqrt 5"
  assume IH2: "of_nat (fib (Suc n)) = (\<phi> ^ Suc n - \<psi> ^ Suc n) / sqrt 5"
  have "of_nat (fib (Suc (Suc n))) = of_nat (fib (Suc n)) + of_nat (fib n)" by simp
  also have "\<dots> = (\<phi>^n * (\<phi> + 1) - \<psi>^n * (\<psi> + 1)) / sqrt 5"
    by (simp add: IH1 IH2 field_simps)
  also have "\<phi> + 1 = \<phi>\<^sup>2" by (simp add: \<phi>_def field_simps power2_eq_square)
  also have "\<psi> + 1 = \<psi>\<^sup>2" by (simp add: \<psi>_def field_simps power2_eq_square)
  also have "\<phi>^n * \<phi>\<^sup>2 - \<psi>^n * \<psi>\<^sup>2 = \<phi> ^ Suc (Suc n) - \<psi> ^ Suc (Suc n)"
    by (simp add: power2_eq_square)
  finally show "of_nat (fib (Suc (Suc n))) = (\<phi> ^ Suc (Suc n) - \<psi> ^ Suc (Suc n)) / sqrt 5" .
qed (simp_all add: \<phi>_def \<psi>_def field_simps)

lemma fib_closed_form':
  fixes \<phi> \<psi> :: real
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
    and "\<psi> \<equiv> (1 - sqrt 5) / 2"
  assumes "n > 0"
  shows "fib n = round (\<phi> ^ n / sqrt 5)"
proof (rule sym, rule round_unique')
  have "\<bar>\<phi> ^ n / sqrt 5 - of_int (int (fib n))\<bar> = \<bar>\<psi>\<bar> ^ n / sqrt 5"
    by (simp add: fib_closed_form[folded \<phi>_def \<psi>_def] field_simps power_abs)
  also {
    from assms have "\<bar>\<psi>\<bar>^n \<le> \<bar>\<psi>\<bar>^1"
      by (intro power_decreasing) (simp_all add: algebra_simps real_le_lsqrt)
    also have "\<dots> < sqrt 5 / 2" by (simp add: \<psi>_def field_simps)
    finally have "\<bar>\<psi>\<bar>^n / sqrt 5 < 1/2" by (simp add: field_simps)
  }
  finally show "\<bar>\<phi> ^ n / sqrt 5 - of_int (int (fib n))\<bar> < 1/2" .
qed

lemma fib_asymptotics:
  fixes \<phi> :: real
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
  shows "(\<lambda>n. real (fib n) / (\<phi> ^ n / sqrt 5)) \<longlonglongrightarrow> 1"
proof -
  define \<psi> :: real where "\<psi> \<equiv> (1 - sqrt 5) / 2"
  have "\<phi> > 1" by (simp add: \<phi>_def)
  then have *: "\<phi> \<noteq> 0" by auto
  have "(\<lambda>n. (\<psi> / \<phi>) ^ n) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_power_zero) (simp_all add: \<phi>_def \<psi>_def field_simps add_pos_pos)
  then have "(\<lambda>n. 1 - (\<psi> / \<phi>) ^ n) \<longlonglongrightarrow> 1 - 0"
    by (intro tendsto_diff tendsto_const)
  with * show ?thesis
    by (simp add: divide_simps fib_closed_form [folded \<phi>_def \<psi>_def])
qed


subsection \<open>Divide-and-Conquer recurrence\<close>

text \<open>
  The following divide-and-conquer recurrence allows for a more efficient computation
  of Fibonacci numbers; however, it requires memoisation of values to be reasonably
  efficient, cutting the number of values to be computed to logarithmically many instead of
  linearly many. The vast majority of the computation time is then actually spent on the
  multiplication, since the output number is exponential in the input number.
\<close>

lemma fib_rec_odd:
  fixes \<phi> \<psi> :: real
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
    and "\<psi> \<equiv> (1 - sqrt 5) / 2"
  shows "fib (Suc (2 * n)) = fib n^2 + fib (Suc n)^2"
proof -
  have "of_nat (fib n^2 + fib (Suc n)^2) = ((\<phi> ^ n - \<psi> ^ n)\<^sup>2 + (\<phi> * \<phi> ^ n - \<psi> * \<psi> ^ n)\<^sup>2)/5"
    by (simp add: fib_closed_form[folded \<phi>_def \<psi>_def] field_simps power2_eq_square)
  also
  let ?A = "\<phi>^(2 * n) + \<psi>^(2 * n) - 2*(\<phi> * \<psi>)^n + \<phi>^(2 * n + 2) + \<psi>^(2 * n + 2) - 2*(\<phi> * \<psi>)^(n + 1)"
  have "(\<phi> ^ n - \<psi> ^ n)\<^sup>2 + (\<phi> * \<phi> ^ n - \<psi> * \<psi> ^ n)\<^sup>2 = ?A"
    by (simp add: power2_eq_square algebra_simps power_mult power_mult_distrib)
  also have "\<phi> * \<psi> = -1"
    by (simp add: \<phi>_def \<psi>_def field_simps)
  then have "?A = \<phi>^(2 * n + 1) * (\<phi> + inverse \<phi>) + \<psi>^(2 * n + 1) * (\<psi> + inverse \<psi>)"
    by (auto simp: field_simps power2_eq_square)
  also have "1 + sqrt 5 > 0"
    by (auto intro: add_pos_pos)
  then have "\<phi> + inverse \<phi> = sqrt 5"
    by (simp add: \<phi>_def field_simps)
  also have "\<psi> + inverse \<psi> = -sqrt 5"
    by (simp add: \<psi>_def field_simps)
  also have "(\<phi> ^ (2 * n + 1) * sqrt 5 + \<psi> ^ (2 * n + 1) * - sqrt 5) / 5 =
    (\<phi> ^ (2 * n + 1) - \<psi> ^ (2 * n + 1)) * (sqrt 5 / 5)"
    by (simp add: field_simps)
  also have "sqrt 5 / 5 = inverse (sqrt 5)"
    by (simp add: field_simps)
  also have "(\<phi> ^ (2 * n + 1) - \<psi> ^ (2 * n + 1)) * \<dots> = of_nat (fib (Suc (2 * n)))"
    by (simp add: fib_closed_form[folded \<phi>_def \<psi>_def] divide_inverse)
  finally show ?thesis
    by (simp only: of_nat_eq_iff)
qed

lemma fib_rec_even: "fib (2 * n) = (fib (n - 1) + fib (n + 1)) * fib n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?rfib = "\<lambda>x. real (fib x)"
  have "2 * (Suc n) = Suc (Suc (2 * n))" by simp
  also have "real (fib \<dots>) = ?rfib n^2 + ?rfib (Suc n)^2 + (?rfib (n - 1) + ?rfib (n + 1)) * ?rfib n"
    by (simp add: fib_rec_odd Suc)
  also have "(?rfib (n - 1) + ?rfib (n + 1)) * ?rfib n = (2 * ?rfib (n + 1) - ?rfib n) * ?rfib n"
    by (cases n) simp_all
  also have "?rfib n^2 + ?rfib (Suc n)^2 + \<dots> = (?rfib (Suc n) + 2 * ?rfib n) * ?rfib (Suc n)"
    by (simp add: algebra_simps power2_eq_square)
  also have "\<dots> = real ((fib (Suc n - 1) + fib (Suc n + 1)) * fib (Suc n))" by simp
  finally show ?case by (simp only: of_nat_eq_iff)
qed

lemma fib_rec_even': "fib (2 * n) = (2 * fib (n - 1) + fib n) * fib n"
  by (subst fib_rec_even, cases n) simp_all

lemma fib_rec:
  "fib n =
    (if n = 0 then 0 else if n = 1 then 1
     else if even n then let n' = n div 2; fn = fib n' in (2 * fib (n' - 1) + fn) * fn
     else let n' = n div 2 in fib n' ^ 2 + fib (Suc n') ^ 2)"
  by (auto elim: evenE oddE simp: fib_rec_odd fib_rec_even' Let_def)


subsection \<open>Fibonacci and Binomial Coefficients\<close>

lemma sum_drop_zero: "(\<Sum>k = 0..Suc n. if 0<k then (f (k - 1)) else 0) = (\<Sum>j = 0..n. f j)"
  by (induct n) auto

lemma sum_choose_drop_zero:
  "(\<Sum>k = 0..Suc n. if k = 0 then 0 else (Suc n - k) choose (k - 1)) =
    (\<Sum>j = 0..n. (n-j) choose j)"
  by (rule trans [OF sum.cong sum_drop_zero]) auto

lemma ne_diagonal_fib: "(\<Sum>k = 0..n. (n-k) choose k) = fib (Suc n)"
proof (induct n rule: fib.induct)
  case 1
  show ?case by simp
next
  case 2
  show ?case by simp
next
  case (3 n)
  have "(\<Sum>k = 0..Suc n. Suc (Suc n) - k choose k) =
     (\<Sum>k = 0..Suc n. (Suc n - k choose k) + (if k = 0 then 0 else (Suc n - k choose (k - 1))))"
    by (rule sum.cong) (simp_all add: choose_reduce_nat)
  also have "\<dots> =
    (\<Sum>k = 0..Suc n. Suc n - k choose k) +
    (\<Sum>k = 0..Suc n. if k=0 then 0 else (Suc n - k choose (k - 1)))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>k = 0..Suc n. Suc n - k choose k) + (\<Sum>j = 0..n. n - j choose j)"
    by (metis sum_choose_drop_zero)
  finally show ?case using 3
    by simp
qed

end
