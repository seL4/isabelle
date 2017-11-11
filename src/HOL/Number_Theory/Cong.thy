(*  Title:      HOL/Number_Theory/Cong.thy
    Author:     Christophe Tabacznyj
    Author:     Lawrence C. Paulson
    Author:     Amine Chaieb
    Author:     Thomas M. Rasmussen
    Author:     Jeremy Avigad

Defines congruence (notation: [x = y] (mod z)) for natural numbers and
integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on @{cite davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD".

The original theory, "IntPrimes", by Thomas M. Rasmussen, defined and
developed the congruence relations on the integers. The notion was
extended to the natural numbers by Chaieb. Jeremy Avigad combined
these, revised and tidied them, made the development uniform for the
natural numbers and the integers, and added a number of new theorems.
*)

section \<open>Congruence\<close>

theory Cong
  imports "HOL-Computational_Algebra.Primes"
begin

subsection \<open>Generic congruences\<close>
 
context unique_euclidean_semiring
begin

definition cong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  ("(1[_ = _] '(()mod _'))")
  where "cong b c a \<longleftrightarrow> b mod a = c mod a"
  
abbreviation notcong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  ("(1[_ \<noteq> _] '(()mod _'))")
  where "notcong b c a \<equiv> \<not> cong b c a"

lemma cong_mod_left [simp]:
  "[b mod a = c] (mod a) \<longleftrightarrow> [b = c] (mod a)"
  by (simp add: cong_def)  

lemma cong_mod_right [simp]:
  "[b = c mod a] (mod a) \<longleftrightarrow> [b = c] (mod a)"
  by (simp add: cong_def)  

lemma cong_dvd_iff:
  "a dvd b \<longleftrightarrow> a dvd c" if "[b = c] (mod a)"
  using that by (auto simp: cong_def dvd_eq_mod_eq_0)

lemma cong_0 [simp, presburger]:
  "[b = c] (mod 0) \<longleftrightarrow> b = c"
  by (simp add: cong_def)

lemma cong_1 [simp, presburger]:
  "[b = c] (mod 1)"
  by (simp add: cong_def)

lemma cong_refl [simp]:
  "[b = b] (mod a)"
  by (simp add: cong_def)

lemma cong_sym: 
  "[b = c] (mod a) \<Longrightarrow> [c = b] (mod a)"
  by (simp add: cong_def)

lemma cong_sym_eq:
  "[b = c] (mod a) \<longleftrightarrow> [c = b] (mod a)"
  by (auto simp add: cong_def)

lemma cong_trans [trans]:
  "[b = c] (mod a) \<Longrightarrow> [c = d] (mod a) \<Longrightarrow> [b = d] (mod a)"
  by (simp add: cong_def)

lemma cong_add:
  "[b = c] (mod a) \<Longrightarrow> [d = e] (mod a) \<Longrightarrow> [b + d = c + e] (mod a)"
  by (auto simp add: cong_def intro: mod_add_cong)

lemma cong_mult:
  "[b = c] (mod a) \<Longrightarrow> [d = e] (mod a) \<Longrightarrow> [b * d = c * e] (mod a)"
  by (auto simp add: cong_def intro: mod_mult_cong)

lemma cong_pow:
  "[b = c] (mod a) \<Longrightarrow> [b ^ n = c ^ n] (mod a)"
  by (simp add: cong_def power_mod [symmetric, of b n a] power_mod [symmetric, of c n a])

lemma cong_sum:
  "[sum f A = sum g A] (mod a)" if "\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (mod a)"
  using that by (induct A rule: infinite_finite_induct) (auto intro: cong_add)

lemma cong_prod:
  "[prod f A = prod g A] (mod a)" if "(\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (mod a))"
  using that by (induct A rule: infinite_finite_induct) (auto intro: cong_mult)

lemma cong_scalar_right:
  "[b = c] (mod a) \<Longrightarrow> [b * d = c * d] (mod a)"
  by (simp add: cong_mult)

lemma cong_scalar_left:
  "[b = c] (mod a) \<Longrightarrow> [d * b = d * c] (mod a)"
  by (simp add: cong_mult)

lemma cong_mult_self_right: "[b * a = 0] (mod a)"
  by (simp add: cong_def)

lemma cong_mult_self_left: "[a * b = 0] (mod a)"
  by (simp add: cong_def)

lemma cong_0_iff: "[b = 0] (mod a) \<longleftrightarrow> a dvd b"
  by (simp add: cong_def dvd_eq_mod_eq_0)

lemma mod_mult_cong_right:
  "[c mod (a * b) = d] (mod a) \<longleftrightarrow> [c = d] (mod a)"
  by (simp add: cong_def mod_mod_cancel mod_add_left_eq)

lemma mod_mult_cong_left:
  "[c mod (b * a) = d] (mod a) \<longleftrightarrow> [c = d] (mod a)"
  using mod_mult_cong_right [of c a b d] by (simp add: ac_simps)

end

context unique_euclidean_ring
begin

lemma cong_diff:
  "[b = c] (mod a) \<Longrightarrow> [d = e] (mod a) \<Longrightarrow> [b - d = c - e] (mod a)"
  by (auto simp add: cong_def intro: mod_diff_cong)

lemma cong_diff_iff_cong_0:
  "[b - c = 0] (mod a) \<longleftrightarrow> [b = c] (mod a)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then have "[b - c + c = 0 + c] (mod a)"
    by (rule cong_add) simp
  then show ?Q
    by simp
next
  assume ?Q
  with cong_diff [of b c a c c] show ?P
    by simp
qed

lemma cong_minus_minus_iff:
  "[- b = - c] (mod a) \<longleftrightarrow> [b = c] (mod a)"
  using cong_diff_iff_cong_0 [of b c a] cong_diff_iff_cong_0 [of "- b" "- c" a]
  by (simp add: cong_0_iff dvd_diff_commute)

lemma cong_modulus_minus_iff: "[b = c] (mod - a) \<longleftrightarrow> [b = c] (mod a)"
  using cong_diff_iff_cong_0 [of b c a] cong_diff_iff_cong_0 [of b c " -a"]
  by (simp add: cong_0_iff)

end


subsection \<open>Congruences on @{typ nat} and @{typ int}\<close>

lemma cong_int_iff:
  "[int m = int q] (mod int n) \<longleftrightarrow> [m = q] (mod n)"
  by (simp add: cong_def of_nat_mod [symmetric])

lemma cong_Suc_0 [simp, presburger]:
  "[m = n] (mod Suc 0)"
  using cong_1 [of m n] by simp

lemma cong_diff_nat:
  "[a - c = b - d] (mod m)" if "[a = b] (mod m)" "[c = d] (mod m)"
    and "a \<ge> c" "b \<ge> d" for a b c d m :: nat
proof -
  have "[c + (a - c) = d + (b - d)] (mod m)"
    using that by simp
  with \<open>[c = d] (mod m)\<close> have "[c + (a - c) = c + (b - d)] (mod m)"
    using mod_add_cong by (auto simp add: cong_def) fastforce
  then show ?thesis
    by (simp add: cong_def nat_mod_eq_iff)
qed

lemma cong_diff_iff_cong_0_nat:
  "[a - b = 0] (mod m) \<longleftrightarrow> [a = b] (mod m)" if "a \<ge> b" for a b :: nat
  using that by (auto simp add: cong_def le_imp_diff_is_add dest: nat_mod_eq_lemma)

lemma cong_diff_iff_cong_0_nat':
  "[nat \<bar>int a - int b\<bar> = 0] (mod m) \<longleftrightarrow> [a = b] (mod m)"
proof (cases "b \<le> a")
  case True
  then show ?thesis
    by (simp add: nat_diff_distrib' cong_diff_iff_cong_0_nat [of b a m])
next
  case False
  then have "a \<le> b"
    by simp
  then show ?thesis
    by (simp add: nat_diff_distrib' cong_diff_iff_cong_0_nat [of a b m])
      (auto simp add: cong_def)
qed

lemma cong_altdef_nat:
  "a \<ge> b \<Longrightarrow> [a = b] (mod m) \<longleftrightarrow> m dvd (a - b)"
  for a b :: nat
  by (simp add: cong_0_iff [symmetric] cong_diff_iff_cong_0_nat)

lemma cong_altdef_nat':
  "[a = b] (mod m) \<longleftrightarrow> m dvd nat \<bar>int a - int b\<bar>"
  by (simp add: cong_0_iff [symmetric] cong_diff_iff_cong_0_nat')

lemma cong_altdef_int:
  "[a = b] (mod m) \<longleftrightarrow> m dvd (a - b)"
  for a b :: int
  by (simp add: cong_0_iff [symmetric] cong_diff_iff_cong_0)

lemma cong_abs_int [simp]: "[x = y] (mod abs m) \<longleftrightarrow> [x = y] (mod m)"
  for x y :: int
  by (simp add: cong_altdef_int)

lemma cong_square_int:
  "prime p \<Longrightarrow> 0 < a \<Longrightarrow> [a * a = 1] (mod p) \<Longrightarrow> [a = 1] (mod p) \<or> [a = - 1] (mod p)"
  for a :: int
  apply (simp only: cong_altdef_int)
  apply (subst prime_dvd_mult_eq_int [symmetric], assumption)
  apply (auto simp add: field_simps)
  done

lemma cong_mult_rcancel_int:
  "[a * k = b * k] (mod m) \<longleftrightarrow> [a = b] (mod m)"
  if "coprime k m" for a k m :: int
  using that by (simp add: cong_altdef_int)
    (metis coprime_commute coprime_dvd_mult_right_iff mult.commute right_diff_distrib') 

lemma cong_mult_rcancel_nat:
  "[a * k = b * k] (mod m) \<longleftrightarrow> [a = b] (mod m)"
  if "coprime k m" for a k m :: nat
proof -
  have "[a * k = b * k] (mod m) \<longleftrightarrow> m dvd nat \<bar>int (a * k) - int (b * k)\<bar>"
    by (simp add: cong_altdef_nat')
  also have "\<dots> \<longleftrightarrow> m dvd nat \<bar>(int a - int b) * int k\<bar>"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> m dvd nat \<bar>int a - int b\<bar> * k"
    by (simp add: abs_mult nat_times_as_int)
  also have "\<dots> \<longleftrightarrow> m dvd nat \<bar>int a - int b\<bar>"
    by (rule coprime_dvd_mult_left_iff) (use \<open>coprime k m\<close> in \<open>simp add: ac_simps\<close>)
  also have "\<dots> \<longleftrightarrow> [a = b] (mod m)"
    by (simp add: cong_altdef_nat')
  finally show ?thesis .
qed

lemma cong_mult_lcancel_int:
  "[k * a = k * b] (mod m) = [a = b] (mod m)"
  if "coprime k m" for a k m :: int
  using that by (simp add: cong_mult_rcancel_int ac_simps)

lemma cong_mult_lcancel_nat:
  "[k * a = k * b] (mod m) = [a = b] (mod m)"
  if "coprime k m" for a k m :: nat
  using that by (simp add: cong_mult_rcancel_nat ac_simps)

lemma coprime_cong_mult_int:
  "[a = b] (mod m) \<Longrightarrow> [a = b] (mod n) \<Longrightarrow> coprime m n \<Longrightarrow> [a = b] (mod m * n)"
  for a b :: int
  by (simp add: cong_altdef_int divides_mult)

lemma coprime_cong_mult_nat:
  "[a = b] (mod m) \<Longrightarrow> [a = b] (mod n) \<Longrightarrow> coprime m n \<Longrightarrow> [a = b] (mod m * n)"
  for a b :: nat
  by (simp add: cong_altdef_nat' divides_mult)

lemma cong_less_imp_eq_nat: "0 \<le> a \<Longrightarrow> a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  for a b :: nat
  by (auto simp add: cong_def)

lemma cong_less_imp_eq_int: "0 \<le> a \<Longrightarrow> a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  for a b :: int
  by (auto simp add: cong_def)

lemma cong_less_unique_nat: "0 < m \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  for a m :: nat
  by (auto simp: cong_def) (metis mod_less_divisor mod_mod_trivial)

lemma cong_less_unique_int: "0 < m \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  for a m :: int
  by (auto simp: cong_def)  (metis mod_mod_trivial pos_mod_conj)

lemma cong_iff_lin_int: "[a = b] (mod m) \<longleftrightarrow> (\<exists>k. b = a + m * k)"
  for a b :: int
  by (auto simp add: cong_altdef_int algebra_simps elim!: dvdE)
    (simp add: distrib_right [symmetric] add_eq_0_iff)

lemma cong_iff_lin_nat: "([a = b] (mod m)) \<longleftrightarrow> (\<exists>k1 k2. b + k1 * m = a + k2 * m)"
  (is "?lhs = ?rhs")
  for a b :: nat
proof
  assume ?lhs
  show ?rhs
  proof (cases "b \<le> a")
    case True
    with \<open>?lhs\<close> show ?rhs
      by (metis cong_altdef_nat dvd_def le_add_diff_inverse add_0_right mult_0 mult.commute)
  next
    case False
    with \<open>?lhs\<close> show ?rhs
      by (metis cong_def mult.commute nat_le_linear nat_mod_eq_lemma)
  qed
next
  assume ?rhs
  then show ?lhs
    by (metis cong_def mult.commute nat_mod_eq_iff) 
qed

lemma cong_gcd_eq_nat: "[a = b] (mod m) \<Longrightarrow> gcd a m = gcd b m"
  for a b :: nat
  by (auto simp add: cong_def) (metis gcd_red_nat)

lemma cong_gcd_eq_int: "[a = b] (mod m) \<Longrightarrow> gcd a m = gcd b m"
  for a b :: int
  by (auto simp add: cong_def) (metis gcd_red_int)

lemma cong_imp_coprime_nat: "[a = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> coprime b m"
  for a b :: nat
  by (auto simp add: cong_gcd_eq_nat coprime_iff_gcd_eq_1)

lemma cong_imp_coprime_int: "[a = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> coprime b m"
  for a b :: int
  by (auto simp add: cong_gcd_eq_int coprime_iff_gcd_eq_1)

lemma cong_cong_mod_nat: "[a = b] (mod m) \<longleftrightarrow> [a mod m = b mod m] (mod m)"
  for a b :: nat
  by simp

lemma cong_cong_mod_int: "[a = b] (mod m) \<longleftrightarrow> [a mod m = b mod m] (mod m)"
  for a b :: int
  by simp

lemma cong_minus_int [iff]: "[a = b] (mod - m) \<longleftrightarrow> [a = b] (mod m)"
  for a b :: int
  by (metis cong_iff_lin_int minus_equation_iff mult_minus_left mult_minus_right)

(*
lemma mod_dvd_mod_int:
    "0 < (m::int) \<Longrightarrow> m dvd b \<Longrightarrow> (a mod b mod m) = (a mod m)"
  apply (unfold dvd_def, auto)
  apply (rule mod_mod_cancel)
  apply auto
  done

lemma mod_dvd_mod:
  assumes "0 < (m::nat)" and "m dvd b"
  shows "(a mod b mod m) = (a mod m)"

  apply (rule mod_dvd_mod_int [transferred])
  using assms apply auto
  done
*)

lemma cong_add_lcancel_nat: "[a + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  for a x y :: nat
  by (simp add: cong_iff_lin_nat)

lemma cong_add_lcancel_int: "[a + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  for a x y :: int
  by (simp add: cong_iff_lin_int)

lemma cong_add_rcancel_nat: "[x + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  for a x y :: nat
  by (simp add: cong_iff_lin_nat)

lemma cong_add_rcancel_int: "[x + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  for a x y :: int
  by (simp add: cong_iff_lin_int)

lemma cong_add_lcancel_0_nat: "[a + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  for a x :: nat
  by (simp add: cong_iff_lin_nat)

lemma cong_add_lcancel_0_int: "[a + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  for a x :: int
  by (simp add: cong_iff_lin_int)

lemma cong_add_rcancel_0_nat: "[x + a = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  for a x :: nat
  by (simp add: cong_iff_lin_nat)

lemma cong_add_rcancel_0_int: "[x + a = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  for a x :: int
  by (simp add: cong_iff_lin_int)

lemma cong_dvd_modulus_nat: "[x = y] (mod m) \<Longrightarrow> n dvd m \<Longrightarrow> [x = y] (mod n)"
  for x y :: nat
  apply (auto simp add: cong_iff_lin_nat dvd_def)
  apply (rule_tac x= "k1 * k" in exI)
  apply (rule_tac x= "k2 * k" in exI)
  apply (simp add: field_simps)
  done

lemma cong_dvd_modulus_int: "[x = y] (mod m) \<Longrightarrow> n dvd m \<Longrightarrow> [x = y] (mod n)"
  for x y :: int
  by (auto simp add: cong_altdef_int dvd_def)

lemma cong_to_1_nat:
  fixes a :: nat
  assumes "[a = 1] (mod n)"
  shows "n dvd (a - 1)"
proof (cases "a = 0")
  case True
  then show ?thesis by force
next
  case False
  with assms show ?thesis by (metis cong_altdef_nat leI less_one)
qed

lemma cong_0_1_nat': "[0 = Suc 0] (mod n) \<longleftrightarrow> n = Suc 0"
  by (auto simp: cong_def)

lemma cong_0_1_nat: "[0 = 1] (mod n) \<longleftrightarrow> n = 1"
  for n :: nat
  by (auto simp: cong_def)

lemma cong_0_1_int: "[0 = 1] (mod n) \<longleftrightarrow> n = 1 \<or> n = - 1"
  for n :: int
  by (auto simp: cong_def zmult_eq_1_iff)

lemma cong_to_1'_nat: "[a = 1] (mod n) \<longleftrightarrow> a = 0 \<and> n = 1 \<or> (\<exists>m. a = 1 + m * n)"
  for a :: nat
  by (metis add.right_neutral cong_0_1_nat cong_iff_lin_nat cong_to_1_nat
      dvd_div_mult_self leI le_add_diff_inverse less_one mult_eq_if)

lemma cong_le_nat: "y \<le> x \<Longrightarrow> [x = y] (mod n) \<longleftrightarrow> (\<exists>q. x = q * n + y)"
  for x y :: nat
  by (auto simp add: cong_altdef_nat le_imp_diff_is_add elim!: dvdE)

lemma cong_solve_nat:
  fixes a :: nat
  assumes "a \<noteq> 0"
  shows "\<exists>x. [a * x = gcd a n] (mod n)"
proof (cases "n = 0")
  case True
  then show ?thesis by force
next
  case False
  then show ?thesis
    using bezout_nat [of a n, OF \<open>a \<noteq> 0\<close>]
    by auto (metis cong_add_rcancel_0_nat cong_mult_self_left)
qed

lemma cong_solve_int: "a \<noteq> 0 \<Longrightarrow> \<exists>x. [a * x = gcd a n] (mod n)"
  for a :: int
  apply (cases "n = 0")
   apply (cases "a \<ge> 0")
    apply auto
   apply (rule_tac x = "-1" in exI)
   apply auto
  apply (insert bezout_int [of a n], auto)
  apply (metis cong_iff_lin_int mult.commute)
  done

lemma cong_solve_dvd_nat:
  fixes a :: nat
  assumes a: "a \<noteq> 0" and b: "gcd a n dvd d"
  shows "\<exists>x. [a * x = d] (mod n)"
proof -
  from cong_solve_nat [OF a] obtain x where "[a * x = gcd a n](mod n)"
    by auto
  then have "[(d div gcd a n) * (a * x) = (d div gcd a n) * gcd a n] (mod n)"
    using cong_scalar_left by blast
  also from b have "(d div gcd a n) * gcd a n = d"
    by (rule dvd_div_mult_self)
  also have "(d div gcd a n) * (a * x) = a * (d div gcd a n * x)"
    by auto
  finally show ?thesis
    by auto
qed

lemma cong_solve_dvd_int:
  assumes a: "(a::int) \<noteq> 0" and b: "gcd a n dvd d"
  shows "\<exists>x. [a * x = d] (mod n)"
proof -
  from cong_solve_int [OF a] obtain x where "[a * x = gcd a n](mod n)"
    by auto
  then have "[(d div gcd a n) * (a * x) = (d div gcd a n) * gcd a n] (mod n)"
    using cong_scalar_left by blast
  also from b have "(d div gcd a n) * gcd a n = d"
    by (rule dvd_div_mult_self)
  also have "(d div gcd a n) * (a * x) = a * (d div gcd a n * x)"
    by auto
  finally show ?thesis
    by auto
qed

lemma cong_solve_coprime_nat:
  "\<exists>x. [a * x = Suc 0] (mod n)" if "coprime a n"
  using that cong_solve_nat [of a n] by (cases "a = 0") simp_all

lemma cong_solve_coprime_int:
  "\<exists>x. [a * x = 1] (mod n)" if "coprime a n" for a n x :: int
  using that cong_solve_int [of a n] by (cases "a = 0")
    (auto simp add: zabs_def split: if_splits)

lemma coprime_iff_invertible_nat:
  "m > 0 \<Longrightarrow> coprime a m \<longleftrightarrow> (\<exists>x. [a * x = Suc 0] (mod m))"
  by (auto intro: cong_solve_coprime_nat)
    (use cong_imp_coprime_nat cong_sym coprime_Suc_0_left coprime_mult_left_iff in blast)

lemma coprime_iff_invertible_int:
  "m > 0 \<Longrightarrow> coprime a m \<longleftrightarrow> (\<exists>x. [a * x = 1] (mod m))"
  for m :: int
  by (auto intro: cong_solve_coprime_int)
    (meson cong_imp_coprime_int cong_sym coprime_1_left coprime_mult_left_iff)

lemma coprime_iff_invertible'_nat:
  "m > 0 \<Longrightarrow> coprime a m \<longleftrightarrow> (\<exists>x. 0 \<le> x \<and> x < m \<and> [a * x = Suc 0] (mod m))"
  apply (subst coprime_iff_invertible_nat)
   apply auto
  apply (auto simp add: cong_def)
  apply (metis mod_less_divisor mod_mult_right_eq)
  done

lemma coprime_iff_invertible'_int:
  "m > 0 \<Longrightarrow> coprime a m \<longleftrightarrow> (\<exists>x. 0 \<le> x \<and> x < m \<and> [a * x = 1] (mod m))"
  for m :: int
  apply (subst coprime_iff_invertible_int)
   apply (auto simp add: cong_def)
  apply (metis mod_mult_right_eq pos_mod_conj)
  done

lemma cong_cong_lcm_nat: "[x = y] (mod a) \<Longrightarrow> [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  for x y :: nat
  apply (cases "y \<le> x")
   apply (simp add: cong_altdef_nat)
  apply (meson cong_altdef_nat cong_sym lcm_least_iff nat_le_linear)
  done

lemma cong_cong_lcm_int: "[x = y] (mod a) \<Longrightarrow> [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  for x y :: int
  by (auto simp add: cong_altdef_int lcm_least)

lemma cong_cong_prod_coprime_nat:
  "[x = y] (mod (\<Prod>i\<in>A. m i))" if
    "(\<forall>i\<in>A. [(x::nat) = y] (mod m i))"
    and "(\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j)))"
  using that apply (induct A rule: infinite_finite_induct)
    apply auto
  apply (metis coprime_cong_mult_nat prod_coprime_right)
  done

lemma cong_cong_prod_coprime_int:
  "[x = y] (mod (\<Prod>i\<in>A. m i))" if
    "(\<forall>i\<in>A. [(x::int) = y] (mod m i))"
    "(\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j)))"
  using that apply (induct A rule: infinite_finite_induct)
    apply auto
  apply (metis coprime_cong_mult_int prod_coprime_right)
  done

lemma binary_chinese_remainder_aux_nat:
  fixes m1 m2 :: nat
  assumes a: "coprime m1 m2"
  shows "\<exists>b1 b2. [b1 = 1] (mod m1) \<and> [b1 = 0] (mod m2) \<and> [b2 = 0] (mod m1) \<and> [b2 = 1] (mod m2)"
proof -
  from cong_solve_coprime_nat [OF a] obtain x1 where 1: "[m1 * x1 = 1] (mod m2)"
    by auto
  from a have b: "coprime m2 m1"
    by (simp add: ac_simps)
  from cong_solve_coprime_nat [OF b] obtain x2 where 2: "[m2 * x2 = 1] (mod m1)"
    by auto
  have "[m1 * x1 = 0] (mod m1)"
    by (simp add: cong_mult_self_left)
  moreover have "[m2 * x2 = 0] (mod m2)"
    by (simp add: cong_mult_self_left)
  ultimately show ?thesis
    using 1 2 by blast
qed

lemma binary_chinese_remainder_aux_int:
  fixes m1 m2 :: int
  assumes a: "coprime m1 m2"
  shows "\<exists>b1 b2. [b1 = 1] (mod m1) \<and> [b1 = 0] (mod m2) \<and> [b2 = 0] (mod m1) \<and> [b2 = 1] (mod m2)"
proof -
  from cong_solve_coprime_int [OF a] obtain x1 where 1: "[m1 * x1 = 1] (mod m2)"
    by auto
  from a have b: "coprime m2 m1"
    by (simp add: ac_simps)
  from cong_solve_coprime_int [OF b] obtain x2 where 2: "[m2 * x2 = 1] (mod m1)"
    by auto
  have "[m1 * x1 = 0] (mod m1)"
    by (simp add: cong_mult_self_left)
  moreover have "[m2 * x2 = 0] (mod m2)"
    by (simp add: cong_mult_self_left)
  ultimately show ?thesis
    using 1 2 by blast
qed

lemma binary_chinese_remainder_nat:
  fixes m1 m2 :: nat
  assumes a: "coprime m1 m2"
  shows "\<exists>x. [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from binary_chinese_remainder_aux_nat [OF a] obtain b1 b2
    where "[b1 = 1] (mod m1)" and "[b1 = 0] (mod m2)"
      and "[b2 = 0] (mod m1)" and "[b2 = 1] (mod m2)"
    by blast
  let ?x = "u1 * b1 + u2 * b2"
  have "[?x = u1 * 1 + u2 * 0] (mod m1)"
    using \<open>[b1 = 1] (mod m1)\<close> \<open>[b2 = 0] (mod m1)\<close> cong_add cong_scalar_left by blast
  then have "[?x = u1] (mod m1)" by simp
  have "[?x = u1 * 0 + u2 * 1] (mod m2)"
    using \<open>[b1 = 0] (mod m2)\<close> \<open>[b2 = 1] (mod m2)\<close> cong_add cong_scalar_left by blast
  then have "[?x = u2] (mod m2)"
    by simp
  with \<open>[?x = u1] (mod m1)\<close> show ?thesis
    by blast
qed

lemma binary_chinese_remainder_int:
  fixes m1 m2 :: int
  assumes a: "coprime m1 m2"
  shows "\<exists>x. [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from binary_chinese_remainder_aux_int [OF a] obtain b1 b2
    where "[b1 = 1] (mod m1)" and "[b1 = 0] (mod m2)"
      and "[b2 = 0] (mod m1)" and "[b2 = 1] (mod m2)"
    by blast
  let ?x = "u1 * b1 + u2 * b2"
  have "[?x = u1 * 1 + u2 * 0] (mod m1)"
    using \<open>[b1 = 1] (mod m1)\<close> \<open>[b2 = 0] (mod m1)\<close> cong_add cong_scalar_left by blast
  then have "[?x = u1] (mod m1)" by simp
  have "[?x = u1 * 0 + u2 * 1] (mod m2)"
    using \<open>[b1 = 0] (mod m2)\<close> \<open>[b2 = 1] (mod m2)\<close> cong_add cong_scalar_left by blast
  then have "[?x = u2] (mod m2)" by simp
  with \<open>[?x = u1] (mod m1)\<close> show ?thesis
    by blast
qed

lemma cong_modulus_mult_nat: "[x = y] (mod m * n) \<Longrightarrow> [x = y] (mod m)"
  for x y :: nat
  apply (cases "y \<le> x")
   apply (simp add: cong_altdef_nat)
   apply (erule dvd_mult_left)
  apply (rule cong_sym)
  apply (subst (asm) cong_sym_eq)
  apply (simp add: cong_altdef_nat)
  apply (erule dvd_mult_left)
  done

lemma cong_modulus_mult_int: "[x = y] (mod m * n) \<Longrightarrow> [x = y] (mod m)"
  for x y :: int
  apply (simp add: cong_altdef_int)
  apply (erule dvd_mult_left)
  done

lemma cong_less_modulus_unique_nat: "[x = y] (mod m) \<Longrightarrow> x < m \<Longrightarrow> y < m \<Longrightarrow> x = y"
  for x y :: nat
  by (simp add: cong_def)

lemma binary_chinese_remainder_unique_nat:
  fixes m1 m2 :: nat
  assumes a: "coprime m1 m2"
    and nz: "m1 \<noteq> 0" "m2 \<noteq> 0"
  shows "\<exists>!x. x < m1 * m2 \<and> [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from binary_chinese_remainder_nat [OF a] obtain y
    where "[y = u1] (mod m1)" and "[y = u2] (mod m2)"
    by blast
  let ?x = "y mod (m1 * m2)"
  from nz have less: "?x < m1 * m2"
    by auto
  have 1: "[?x = u1] (mod m1)"
    apply (rule cong_trans)
     prefer 2
     apply (rule \<open>[y = u1] (mod m1)\<close>)
    apply (rule cong_modulus_mult_nat [of _ _ _ m2])
    apply simp
    done
  have 2: "[?x = u2] (mod m2)"
    apply (rule cong_trans)
     prefer 2
     apply (rule \<open>[y = u2] (mod m2)\<close>)
    apply (subst mult.commute)
    apply (rule cong_modulus_mult_nat [of _ _ _ m1])
    apply simp
    done
  have "\<forall>z. z < m1 * m2 \<and> [z = u1] (mod m1) \<and> [z = u2] (mod m2) \<longrightarrow> z = ?x"
  proof clarify
    fix z
    assume "z < m1 * m2"
    assume "[z = u1] (mod m1)" and  "[z = u2] (mod m2)"
    have "[?x = z] (mod m1)"
      apply (rule cong_trans)
       apply (rule \<open>[?x = u1] (mod m1)\<close>)
      apply (rule cong_sym)
      apply (rule \<open>[z = u1] (mod m1)\<close>)
      done
    moreover have "[?x = z] (mod m2)"
      apply (rule cong_trans)
       apply (rule \<open>[?x = u2] (mod m2)\<close>)
      apply (rule cong_sym)
      apply (rule \<open>[z = u2] (mod m2)\<close>)
      done
    ultimately have "[?x = z] (mod m1 * m2)"
      using a by (auto intro: coprime_cong_mult_nat simp add: mod_mult_cong_left mod_mult_cong_right)
    with \<open>z < m1 * m2\<close> \<open>?x < m1 * m2\<close> show "z = ?x"
      apply (intro cong_less_modulus_unique_nat)
        apply (auto, erule cong_sym)
      done
  qed
  with less 1 2 show ?thesis by auto
 qed

lemma chinese_remainder_aux_nat:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> nat"
  assumes fin: "finite A"
    and cop: "\<forall>i \<in> A. (\<forall>j \<in> A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "\<exists>b. (\<forall>i \<in> A. [b i = 1] (mod m i) \<and> [b i = 0] (mod (\<Prod>j \<in> A - {i}. m j)))"
proof (rule finite_set_choice, rule fin, rule ballI)
  fix i
  assume "i \<in> A"
  with cop have "coprime (\<Prod>j \<in> A - {i}. m j) (m i)"
    by (intro prod_coprime_left) auto
  then have "\<exists>x. [(\<Prod>j \<in> A - {i}. m j) * x = Suc 0] (mod m i)"
    by (elim cong_solve_coprime_nat)
  then obtain x where "[(\<Prod>j \<in> A - {i}. m j) * x = 1] (mod m i)"
    by auto
  moreover have "[(\<Prod>j \<in> A - {i}. m j) * x = 0] (mod (\<Prod>j \<in> A - {i}. m j))"
    by (simp add: cong_0_iff)
  ultimately show "\<exists>a. [a = 1] (mod m i) \<and> [a = 0] (mod prod m (A - {i}))"
    by blast
qed

lemma chinese_remainder_nat:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> nat"
    and u :: "'a \<Rightarrow> nat"
  assumes fin: "finite A"
    and cop: "\<forall>i \<in> A. \<forall>j \<in> A. i \<noteq> j \<longrightarrow> coprime (m i) (m j)"
  shows "\<exists>x. \<forall>i \<in> A. [x = u i] (mod m i)"
proof -
  from chinese_remainder_aux_nat [OF fin cop]
  obtain b where b: "\<forall>i \<in> A. [b i = 1] (mod m i) \<and> [b i = 0] (mod (\<Prod>j \<in> A - {i}. m j))"
    by blast
  let ?x = "\<Sum>i\<in>A. (u i) * (b i)"
  show ?thesis
  proof (rule exI, clarify)
    fix i
    assume a: "i \<in> A"
    show "[?x = u i] (mod m i)"
    proof -
      from fin a have "?x = (\<Sum>j \<in> {i}. u j * b j) + (\<Sum>j \<in> A - {i}. u j * b j)"
        by (subst sum.union_disjoint [symmetric]) (auto intro: sum.cong)
      then have "[?x = u i * b i + (\<Sum>j \<in> A - {i}. u j * b j)] (mod m i)"
        by auto
      also have "[u i * b i + (\<Sum>j \<in> A - {i}. u j * b j) =
                  u i * 1 + (\<Sum>j \<in> A - {i}. u j * 0)] (mod m i)"
        apply (rule cong_add)
         apply (rule cong_scalar_left)
        using b a apply blast
        apply (rule cong_sum)
        apply (rule cong_scalar_left)
        using b apply auto
        apply (rule cong_dvd_modulus_nat)
         apply (drule (1) bspec)
         apply (erule conjE)
         apply assumption
        apply rule
        using fin a apply auto
        done
      finally show ?thesis
        by simp
    qed
  qed
qed

lemma coprime_cong_prod_nat:
  "[x = y] (mod (\<Prod>i\<in>A. m i))"
  if "\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
    and "\<forall>i\<in>A. [x = y] (mod m i)" for x y :: nat
  using that apply (induct A rule: infinite_finite_induct)
    apply auto
  apply (metis coprime_cong_mult_nat prod_coprime_right)
  done

lemma chinese_remainder_unique_nat:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> nat"
    and u :: "'a \<Rightarrow> nat"
  assumes fin: "finite A"
    and nz: "\<forall>i\<in>A. m i \<noteq> 0"
    and cop: "\<forall>i\<in>A. \<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j)"
  shows "\<exists>!x. x < (\<Prod>i\<in>A. m i) \<and> (\<forall>i\<in>A. [x = u i] (mod m i))"
proof -
  from chinese_remainder_nat [OF fin cop]
  obtain y where one: "(\<forall>i\<in>A. [y = u i] (mod m i))"
    by blast
  let ?x = "y mod (\<Prod>i\<in>A. m i)"
  from fin nz have prodnz: "(\<Prod>i\<in>A. m i) \<noteq> 0"
    by auto
  then have less: "?x < (\<Prod>i\<in>A. m i)"
    by auto
  have cong: "\<forall>i\<in>A. [?x = u i] (mod m i)"
    apply auto
    apply (rule cong_trans)
     prefer 2
    using one apply auto
    apply (rule cong_dvd_modulus_nat [of _ _ "prod m A"])
     apply simp
    using fin apply auto
    done
  have unique: "\<forall>z. z < (\<Prod>i\<in>A. m i) \<and> (\<forall>i\<in>A. [z = u i] (mod m i)) \<longrightarrow> z = ?x"
  proof clarify
    fix z
    assume zless: "z < (\<Prod>i\<in>A. m i)"
    assume zcong: "(\<forall>i\<in>A. [z = u i] (mod m i))"
    have "\<forall>i\<in>A. [?x = z] (mod m i)"
      apply clarify
      apply (rule cong_trans)
      using cong apply (erule bspec)
      apply (rule cong_sym)
      using zcong apply auto
      done
    with fin cop have "[?x = z] (mod (\<Prod>i\<in>A. m i))"
      apply (intro coprime_cong_prod_nat)
        apply auto
      done
    with zless less show "z = ?x"
      apply (intro cong_less_modulus_unique_nat)
        apply auto
      apply (erule cong_sym)
      done
  qed
  from less cong unique show ?thesis
    by blast
qed

end
