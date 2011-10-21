(*  Title:      HOL/Power.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

header {* Exponentiation *}

theory Power
imports Nat
begin

subsection {* Powers for Arbitrary Monoids *}

class power = one + times
begin

primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixr "^" 80) where
    power_0: "a ^ 0 = 1"
  | power_Suc: "a ^ Suc n = a * a ^ n"

notation (latex output)
  power ("(_\<^bsup>_\<^esup>)" [1000] 1000)

notation (HTML output)
  power ("(_\<^bsup>_\<^esup>)" [1000] 1000)

end

context monoid_mult
begin

subclass power .

lemma power_one [simp]:
  "1 ^ n = 1"
  by (induct n) simp_all

lemma power_one_right [simp]:
  "a ^ 1 = a"
  by simp

lemma power_commutes:
  "a ^ n * a = a * a ^ n"
  by (induct n) (simp_all add: mult_assoc)

lemma power_Suc2:
  "a ^ Suc n = a ^ n * a"
  by (simp add: power_commutes)

lemma power_add:
  "a ^ (m + n) = a ^ m * a ^ n"
  by (induct m) (simp_all add: algebra_simps)

lemma power_mult:
  "a ^ (m * n) = (a ^ m) ^ n"
  by (induct n) (simp_all add: power_add)

end

context comm_monoid_mult
begin

lemma power_mult_distrib:
  "(a * b) ^ n = (a ^ n) * (b ^ n)"
  by (induct n) (simp_all add: mult_ac)

end

context semiring_1
begin

lemma of_nat_power:
  "of_nat (m ^ n) = of_nat m ^ n"
  by (induct n) (simp_all add: of_nat_mult)

end

context comm_semiring_1
begin

text {* The divides relation *}

lemma le_imp_power_dvd:
  assumes "m \<le> n" shows "a ^ m dvd a ^ n"
proof
  have "a ^ n = a ^ (m + (n - m))"
    using `m \<le> n` by simp
  also have "\<dots> = a ^ m * a ^ (n - m)"
    by (rule power_add)
  finally show "a ^ n = a ^ m * a ^ (n - m)" .
qed

lemma power_le_dvd:
  "a ^ n dvd b \<Longrightarrow> m \<le> n \<Longrightarrow> a ^ m dvd b"
  by (rule dvd_trans [OF le_imp_power_dvd])

lemma dvd_power_same:
  "x dvd y \<Longrightarrow> x ^ n dvd y ^ n"
  by (induct n) (auto simp add: mult_dvd_mono)

lemma dvd_power_le:
  "x dvd y \<Longrightarrow> m \<ge> n \<Longrightarrow> x ^ n dvd y ^ m"
  by (rule power_le_dvd [OF dvd_power_same])

lemma dvd_power [simp]:
  assumes "n > (0::nat) \<or> x = 1"
  shows "x dvd (x ^ n)"
using assms proof
  assume "0 < n"
  then have "x ^ n = x ^ Suc (n - 1)" by simp
  then show "x dvd (x ^ n)" by simp
next
  assume "x = 1"
  then show "x dvd (x ^ n)" by simp
qed

end

context ring_1
begin

lemma power_minus:
  "(- a) ^ n = (- 1) ^ n * a ^ n"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) then show ?case
    by (simp del: power_Suc add: power_Suc2 mult_assoc)
qed

end

context linordered_semidom
begin

lemma zero_less_power [simp]:
  "0 < a \<Longrightarrow> 0 < a ^ n"
  by (induct n) (simp_all add: mult_pos_pos)

lemma zero_le_power [simp]:
  "0 \<le> a \<Longrightarrow> 0 \<le> a ^ n"
  by (induct n) (simp_all add: mult_nonneg_nonneg)

lemma one_le_power[simp]:
  "1 \<le> a \<Longrightarrow> 1 \<le> a ^ n"
  apply (induct n)
  apply simp_all
  apply (rule order_trans [OF _ mult_mono [of 1 _ 1]])
  apply (simp_all add: order_trans [OF zero_le_one])
  done

lemma power_gt1_lemma:
  assumes gt1: "1 < a"
  shows "1 < a * a ^ n"
proof -
  from gt1 have "0 \<le> a"
    by (fact order_trans [OF zero_le_one less_imp_le])
  have "1 * 1 < a * 1" using gt1 by simp
  also have "\<dots> \<le> a * a ^ n" using gt1
    by (simp only: mult_mono `0 \<le> a` one_le_power order_less_imp_le
        zero_le_one order_refl)
  finally show ?thesis by simp
qed

lemma power_gt1:
  "1 < a \<Longrightarrow> 1 < a ^ Suc n"
  by (simp add: power_gt1_lemma)

lemma one_less_power [simp]:
  "1 < a \<Longrightarrow> 0 < n \<Longrightarrow> 1 < a ^ n"
  by (cases n) (simp_all add: power_gt1_lemma)

lemma power_le_imp_le_exp:
  assumes gt1: "1 < a"
  shows "a ^ m \<le> a ^ n \<Longrightarrow> m \<le> n"
proof (induct m arbitrary: n)
  case 0
  show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases n)
    case 0
    with Suc.prems Suc.hyps have "a * a ^ m \<le> 1" by simp
    with gt1 show ?thesis
      by (force simp only: power_gt1_lemma
          not_less [symmetric])
  next
    case (Suc n)
    with Suc.prems Suc.hyps show ?thesis
      by (force dest: mult_left_le_imp_le
          simp add: less_trans [OF zero_less_one gt1])
  qed
qed

text{*Surely we can strengthen this? It holds for @{text "0<a<1"} too.*}
lemma power_inject_exp [simp]:
  "1 < a \<Longrightarrow> a ^ m = a ^ n \<longleftrightarrow> m = n"
  by (force simp add: order_antisym power_le_imp_le_exp)

text{*Can relax the first premise to @{term "0<a"} in the case of the
natural numbers.*}
lemma power_less_imp_less_exp:
  "1 < a \<Longrightarrow> a ^ m < a ^ n \<Longrightarrow> m < n"
  by (simp add: order_less_le [of m n] less_le [of "a^m" "a^n"]
    power_le_imp_le_exp)

lemma power_mono:
  "a \<le> b \<Longrightarrow> 0 \<le> a \<Longrightarrow> a ^ n \<le> b ^ n"
  by (induct n)
    (auto intro: mult_mono order_trans [of 0 a b])

lemma power_strict_mono [rule_format]:
  "a < b \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 < n \<longrightarrow> a ^ n < b ^ n"
  by (induct n)
   (auto simp add: mult_strict_mono le_less_trans [of 0 a b])

text{*Lemma for @{text power_strict_decreasing}*}
lemma power_Suc_less:
  "0 < a \<Longrightarrow> a < 1 \<Longrightarrow> a * a ^ n < a ^ n"
  by (induct n)
    (auto simp add: mult_strict_left_mono)

lemma power_strict_decreasing [rule_format]:
  "n < N \<Longrightarrow> 0 < a \<Longrightarrow> a < 1 \<longrightarrow> a ^ N < a ^ n"
proof (induct N)
  case 0 then show ?case by simp
next
  case (Suc N) then show ?case 
  apply (auto simp add: power_Suc_less less_Suc_eq)
  apply (subgoal_tac "a * a^N < 1 * a^n")
  apply simp
  apply (rule mult_strict_mono) apply auto
  done
qed

text{*Proof resembles that of @{text power_strict_decreasing}*}
lemma power_decreasing [rule_format]:
  "n \<le> N \<Longrightarrow> 0 \<le> a \<Longrightarrow> a \<le> 1 \<longrightarrow> a ^ N \<le> a ^ n"
proof (induct N)
  case 0 then show ?case by simp
next
  case (Suc N) then show ?case 
  apply (auto simp add: le_Suc_eq)
  apply (subgoal_tac "a * a^N \<le> 1 * a^n", simp)
  apply (rule mult_mono) apply auto
  done
qed

lemma power_Suc_less_one:
  "0 < a \<Longrightarrow> a < 1 \<Longrightarrow> a ^ Suc n < 1"
  using power_strict_decreasing [of 0 "Suc n" a] by simp

text{*Proof again resembles that of @{text power_strict_decreasing}*}
lemma power_increasing [rule_format]:
  "n \<le> N \<Longrightarrow> 1 \<le> a \<Longrightarrow> a ^ n \<le> a ^ N"
proof (induct N)
  case 0 then show ?case by simp
next
  case (Suc N) then show ?case 
  apply (auto simp add: le_Suc_eq)
  apply (subgoal_tac "1 * a^n \<le> a * a^N", simp)
  apply (rule mult_mono) apply (auto simp add: order_trans [OF zero_le_one])
  done
qed

text{*Lemma for @{text power_strict_increasing}*}
lemma power_less_power_Suc:
  "1 < a \<Longrightarrow> a ^ n < a * a ^ n"
  by (induct n) (auto simp add: mult_strict_left_mono less_trans [OF zero_less_one])

lemma power_strict_increasing [rule_format]:
  "n < N \<Longrightarrow> 1 < a \<longrightarrow> a ^ n < a ^ N"
proof (induct N)
  case 0 then show ?case by simp
next
  case (Suc N) then show ?case 
  apply (auto simp add: power_less_power_Suc less_Suc_eq)
  apply (subgoal_tac "1 * a^n < a * a^N", simp)
  apply (rule mult_strict_mono) apply (auto simp add: less_trans [OF zero_less_one] less_imp_le)
  done
qed

lemma power_increasing_iff [simp]:
  "1 < b \<Longrightarrow> b ^ x \<le> b ^ y \<longleftrightarrow> x \<le> y"
  by (blast intro: power_le_imp_le_exp power_increasing less_imp_le)

lemma power_strict_increasing_iff [simp]:
  "1 < b \<Longrightarrow> b ^ x < b ^ y \<longleftrightarrow> x < y"
by (blast intro: power_less_imp_less_exp power_strict_increasing) 

lemma power_le_imp_le_base:
  assumes le: "a ^ Suc n \<le> b ^ Suc n"
    and ynonneg: "0 \<le> b"
  shows "a \<le> b"
proof (rule ccontr)
  assume "~ a \<le> b"
  then have "b < a" by (simp only: linorder_not_le)
  then have "b ^ Suc n < a ^ Suc n"
    by (simp only: assms power_strict_mono)
  from le and this show False
    by (simp add: linorder_not_less [symmetric])
qed

lemma power_less_imp_less_base:
  assumes less: "a ^ n < b ^ n"
  assumes nonneg: "0 \<le> b"
  shows "a < b"
proof (rule contrapos_pp [OF less])
  assume "~ a < b"
  hence "b \<le> a" by (simp only: linorder_not_less)
  hence "b ^ n \<le> a ^ n" using nonneg by (rule power_mono)
  thus "\<not> a ^ n < b ^ n" by (simp only: linorder_not_less)
qed

lemma power_inject_base:
  "a ^ Suc n = b ^ Suc n \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a = b"
by (blast intro: power_le_imp_le_base antisym eq_refl sym)

lemma power_eq_imp_eq_base:
  "a ^ n = b ^ n \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 < n \<Longrightarrow> a = b"
  by (cases n) (simp_all del: power_Suc, rule power_inject_base)

end

context linordered_idom
begin

lemma power_abs:
  "abs (a ^ n) = abs a ^ n"
  by (induct n) (auto simp add: abs_mult)

lemma abs_power_minus [simp]:
  "abs ((-a) ^ n) = abs (a ^ n)"
  by (simp add: power_abs)

lemma zero_less_power_abs_iff [simp, no_atp]:
  "0 < abs a ^ n \<longleftrightarrow> a \<noteq> 0 \<or> n = 0"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) show ?case by (auto simp add: Suc zero_less_mult_iff)
qed

lemma zero_le_power_abs [simp]:
  "0 \<le> abs a ^ n"
  by (rule zero_le_power [OF abs_ge_zero])

end

context ring_1_no_zero_divisors
begin

lemma field_power_not_zero:
  "a \<noteq> 0 \<Longrightarrow> a ^ n \<noteq> 0"
  by (induct n) auto

end

context division_ring
begin

text {* FIXME reorient or rename to @{text nonzero_inverse_power} *}
lemma nonzero_power_inverse:
  "a \<noteq> 0 \<Longrightarrow> inverse (a ^ n) = (inverse a) ^ n"
  by (induct n)
    (simp_all add: nonzero_inverse_mult_distrib power_commutes field_power_not_zero)

end

context field
begin

lemma nonzero_power_divide:
  "b \<noteq> 0 \<Longrightarrow> (a / b) ^ n = a ^ n / b ^ n"
  by (simp add: divide_inverse power_mult_distrib nonzero_power_inverse)

end

lemma power_0_Suc [simp]:
  "(0::'a::{power, semiring_0}) ^ Suc n = 0"
  by simp

text{*It looks plausible as a simprule, but its effect can be strange.*}
lemma power_0_left:
  "0 ^ n = (if n = 0 then 1 else (0::'a::{power, semiring_0}))"
  by (induct n) simp_all

lemma power_eq_0_iff [simp]:
  "a ^ n = 0 \<longleftrightarrow>
     a = (0::'a::{mult_zero,zero_neq_one,no_zero_divisors,power}) \<and> n \<noteq> 0"
  by (induct n)
    (auto simp add: no_zero_divisors elim: contrapos_pp)

lemma (in field) power_diff:
  assumes nz: "a \<noteq> 0"
  shows "n \<le> m \<Longrightarrow> a ^ (m - n) = a ^ m / a ^ n"
  by (induct m n rule: diff_induct) (simp_all add: nz field_power_not_zero)

text{*Perhaps these should be simprules.*}
lemma power_inverse:
  fixes a :: "'a::division_ring_inverse_zero"
  shows "inverse (a ^ n) = inverse a ^ n"
apply (cases "a = 0")
apply (simp add: power_0_left)
apply (simp add: nonzero_power_inverse)
done (* TODO: reorient or rename to inverse_power *)

lemma power_one_over:
  "1 / (a::'a::{field_inverse_zero, power}) ^ n =  (1 / a) ^ n"
  by (simp add: divide_inverse) (rule power_inverse)

lemma power_divide:
  "(a / b) ^ n = (a::'a::field_inverse_zero) ^ n / b ^ n"
apply (cases "b = 0")
apply (simp add: power_0_left)
apply (rule nonzero_power_divide)
apply assumption
done


subsection {* Exponentiation for the Natural Numbers *}

lemma nat_one_le_power [simp]:
  "Suc 0 \<le> i \<Longrightarrow> Suc 0 \<le> i ^ n"
  by (rule one_le_power [of i n, unfolded One_nat_def])

lemma nat_zero_less_power_iff [simp]:
  "x ^ n > 0 \<longleftrightarrow> x > (0::nat) \<or> n = 0"
  by (induct n) auto

lemma nat_power_eq_Suc_0_iff [simp]: 
  "x ^ m = Suc 0 \<longleftrightarrow> m = 0 \<or> x = Suc 0"
  by (induct m) auto

lemma power_Suc_0 [simp]:
  "Suc 0 ^ n = Suc 0"
  by simp

text{*Valid for the naturals, but what if @{text"0<i<1"}?
Premises cannot be weakened: consider the case where @{term "i=0"},
@{term "m=1"} and @{term "n=0"}.*}
lemma nat_power_less_imp_less:
  assumes nonneg: "0 < (i\<Colon>nat)"
  assumes less: "i ^ m < i ^ n"
  shows "m < n"
proof (cases "i = 1")
  case True with less power_one [where 'a = nat] show ?thesis by simp
next
  case False with nonneg have "1 < i" by auto
  from power_strict_increasing_iff [OF this] less show ?thesis ..
qed

lemma power_dvd_imp_le:
  "i ^ m dvd i ^ n \<Longrightarrow> (1::nat) < i \<Longrightarrow> m \<le> n"
  apply (rule power_le_imp_le_exp, assumption)
  apply (erule dvd_imp_le, simp)
  done


subsection {* Code generator tweak *}

lemma power_power_power [code]:
  "power = power.power (1::'a::{power}) (op *)"
  unfolding power_def power.power_def ..

declare power.power.simps [code]

code_modulename SML
  Power Arith

code_modulename OCaml
  Power Arith

code_modulename Haskell
  Power Arith

end
