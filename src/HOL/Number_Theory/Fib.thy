(*  Title:      HOL/Number_Theory/Fib.thy
    Author:     Lawrence C. Paulson
    Author:     Jeremy Avigad

Defines the fibonacci function.

The original "Fib" is due to Lawrence C. Paulson, and was adapted by
Jeremy Avigad.
*)

section {* Fib *}

theory Fib
imports Binomial
begin


subsection {* Main definitions *}

fun fib :: "nat \<Rightarrow> nat"
where
    fib0: "fib 0 = 0"
  | fib1: "fib (Suc 0) = 1"
  | fib2: "fib (Suc (Suc n)) = fib (Suc n) + fib n"

subsection {* Fibonacci numbers *}

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

text {*
  \medskip Concrete Mathematics, page 278: Cassini's identity.  The proof is
  much easier using integers, not natural numbers!
*}

lemma fib_Cassini_int: "int (fib (Suc (Suc n)) * fib n) - int((fib (Suc n))\<^sup>2) = - ((-1)^n)"
  by (induction n rule: fib.induct)  (auto simp add: field_simps power2_eq_square power_add)

lemma fib_Cassini_nat:
    "fib (Suc (Suc n)) * fib n =
       (if even n then (fib (Suc n))\<^sup>2 - 1 else (fib (Suc n))\<^sup>2 + 1)"
using fib_Cassini_int [of n] by auto


text {* \medskip Toward Law 6.111 of Concrete Mathematics *}

lemma coprime_fib_Suc_nat: "coprime (fib (n::nat)) (fib (Suc n))"
  apply (induct n rule: fib.induct)
  apply auto
  apply (metis gcd_add1_nat add.commute)
  done

lemma gcd_fib_add: "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
  apply (simp add: gcd_commute_nat [of "fib m"])
  apply (cases m)
  apply (auto simp add: fib_add)
  apply (subst gcd_commute_nat)
  apply (subst mult.commute)
  apply (metis coprime_fib_Suc_nat gcd_add_mult_nat gcd_mult_cancel_nat gcd_nat.commute)
  done

lemma gcd_fib_diff: "m \<le> n \<Longrightarrow>
    gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
  by (simp add: gcd_fib_add [symmetric, of _ "n-m"])

lemma gcd_fib_mod: "0 < m \<Longrightarrow>
    gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
proof (induct n rule: less_induct)
  case (less n)
  from less.prems have pos_m: "0 < m" .
  show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
  proof (cases "m < n")
    case True
    then have "m \<le> n" by auto
    with pos_m have pos_n: "0 < n" by auto
    with pos_m `m < n` have diff: "n - m < n" by auto
    have "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib ((n - m) mod m))"
      by (simp add: mod_if [of n]) (insert `m < n`, auto)
    also have "\<dots> = gcd (fib m)  (fib (n - m))"
      by (simp add: less.hyps diff pos_m)
    also have "\<dots> = gcd (fib m) (fib n)"
      by (simp add: gcd_fib_diff `m \<le> n`)
    finally show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" .
  next
    case False
    then show "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
      by (cases "m = n") auto
  qed
qed

lemma fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)"
    -- {* Law 6.111 *}
  by (induct m n rule: gcd_nat_induct) (simp_all add: gcd_non_0_nat gcd_commute_nat gcd_fib_mod)

theorem fib_mult_eq_setsum_nat:
    "fib (Suc n) * fib n = (\<Sum>k \<in> {..n}. fib k * fib k)"
  by (induct n rule: nat.induct) (auto simp add:  field_simps)

end

