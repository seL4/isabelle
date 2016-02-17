(*  Title:      HOL/Number_Theory/Fib.thy
    Author:     Lawrence C. Paulson
    Author:     Jeremy Avigad
*)

section \<open>The fibonacci function\<close>

theory Fib
imports Main GCD Binomial
begin


subsection \<open>Fibonacci numbers\<close>

fun fib :: "nat \<Rightarrow> nat"
where
  fib0: "fib 0 = 0"
| fib1: "fib (Suc 0) = 1"
| fib2: "fib (Suc (Suc n)) = fib (Suc n) + fib n"


subsection \<open>Basic Properties\<close>

lemma fib_1 [simp]: "fib (1::nat) = 1"
  by (metis One_nat_def fib1)

lemma fib_2 [simp]: "fib (2::nat) = 1"
  using fib.simps(3) [of 0]
  by (simp add: numeral_2_eq_2)

lemma fib_plus_2: "fib (n + 2) = fib (n + 1) + fib n"
  by (metis Suc_eq_plus1 add_2_eq_Suc' fib.simps(3))

lemma fib_add: "fib (Suc (n+k)) = fib (Suc k) * fib (Suc n) + fib k * fib n"
  by (induct n rule: fib.induct) (auto simp add: field_simps)

lemma fib_neq_0_nat: "n > 0 \<Longrightarrow> fib n > 0"
  by (induct n rule: fib.induct) (auto simp add: )


subsection \<open>A Few Elementary Results\<close>

text \<open>
  \medskip Concrete Mathematics, page 278: Cassini's identity.  The proof is
  much easier using integers, not natural numbers!
\<close>

lemma fib_Cassini_int: "int (fib (Suc (Suc n)) * fib n) - int((fib (Suc n))\<^sup>2) = - ((-1)^n)"
  by (induct n rule: fib.induct)  (auto simp add: field_simps power2_eq_square power_add)

lemma fib_Cassini_nat:
  "fib (Suc (Suc n)) * fib n =
     (if even n then (fib (Suc n))\<^sup>2 - 1 else (fib (Suc n))\<^sup>2 + 1)"
  using fib_Cassini_int [of n]  by (auto simp del: of_nat_mult of_nat_power)


subsection \<open>Law 6.111 of Concrete Mathematics\<close>

lemma coprime_fib_Suc_nat: "coprime (fib (n::nat)) (fib (Suc n))"
  apply (induct n rule: fib.induct)
  apply auto
  apply (metis gcd_add1_nat add.commute)
  done

lemma gcd_fib_add: "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
  apply (simp add: gcd.commute [of "fib m"])
  apply (cases m)
  apply (auto simp add: fib_add)
  apply (metis gcd.commute mult.commute coprime_fib_Suc_nat
    gcd_add_mult_nat gcd_mult_cancel gcd.commute)
  done

lemma gcd_fib_diff: "m \<le> n \<Longrightarrow> gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
  by (simp add: gcd_fib_add [symmetric, of _ "n-m"])

lemma gcd_fib_mod: "0 < m \<Longrightarrow> gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
proof (induct n rule: less_induct)
  case (less n)
  show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
  proof (cases "m < n")
    case True
    then have "m \<le> n" by auto
    with \<open>0 < m\<close> have pos_n: "0 < n" by auto
    with \<open>0 < m\<close> \<open>m < n\<close> have diff: "n - m < n" by auto
    have "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib ((n - m) mod m))"
      by (simp add: mod_if [of n]) (insert \<open>m < n\<close>, auto)
    also have "\<dots> = gcd (fib m)  (fib (n - m))"
      by (simp add: less.hyps diff \<open>0 < m\<close>)
    also have "\<dots> = gcd (fib m) (fib n)"
      by (simp add: gcd_fib_diff \<open>m \<le> n\<close>)
    finally show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" .
  next
    case False
    then show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
      by (cases "m = n") auto
  qed
qed

lemma fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)"
    -- \<open>Law 6.111\<close>
  by (induct m n rule: gcd_nat_induct) (simp_all add: gcd_non_0_nat gcd.commute gcd_fib_mod)

theorem fib_mult_eq_setsum_nat: "fib (Suc n) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  by (induct n rule: nat.induct) (auto simp add:  field_simps)


subsection \<open>Fibonacci and Binomial Coefficients\<close>

lemma setsum_drop_zero: "(\<Sum>k = 0..Suc n. if 0<k then (f (k - 1)) else 0) = (\<Sum>j = 0..n. f j)"
  by (induct n) auto

lemma setsum_choose_drop_zero:
    "(\<Sum>k = 0..Suc n. if k=0 then 0 else (Suc n - k) choose (k - 1)) = (\<Sum>j = 0..n. (n-j) choose j)"
  by (rule trans [OF setsum.cong setsum_drop_zero]) auto

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
        (\<Sum>k = 0..Suc n. (Suc n - k choose k) + (if k=0 then 0 else (Suc n - k choose (k - 1))))"
    by (rule setsum.cong) (simp_all add: choose_reduce_nat)
  also have "\<dots> = (\<Sum>k = 0..Suc n. Suc n - k choose k) +
                   (\<Sum>k = 0..Suc n. if k=0 then 0 else (Suc n - k choose (k - 1)))"
    by (simp add: setsum.distrib)
  also have "\<dots> = (\<Sum>k = 0..Suc n. Suc n - k choose k) +
                   (\<Sum>j = 0..n. n - j choose j)"
    by (metis setsum_choose_drop_zero)
  finally show ?case using 3
    by simp
qed

end

