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

subsection \<open>Turn off \<open>One_nat_def\<close>\<close>

lemma power_eq_one_eq_nat [simp]: "x^m = 1 \<longleftrightarrow> m = 0 \<or> x = 1"
  for x m :: nat
  by (induct m) auto

declare mod_pos_pos_trivial [simp]


subsection \<open>Main definitions\<close>

class cong =
  fixes cong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  ("(1[_ = _] '(()mod _'))")
begin

abbreviation notcong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  ("(1[_ \<noteq> _] '(()mod _'))")
  where "notcong x y m \<equiv> \<not> cong x y m"

end


subsubsection \<open>Definitions for the natural numbers\<close>

instantiation nat :: cong
begin

definition cong_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "cong_nat x y m \<longleftrightarrow> x mod m = y mod m"

instance ..

end


subsubsection \<open>Definitions for the integers\<close>

instantiation int :: cong
begin

definition cong_int :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  where "cong_int x y m \<longleftrightarrow> x mod m = y mod m"

instance ..

end


subsection \<open>Set up Transfer\<close>


lemma transfer_nat_int_cong:
  "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> m \<ge> 0 \<Longrightarrow> [nat x = nat y] (mod (nat m)) \<longleftrightarrow> [x = y] (mod m)"
  for x y m :: int
  unfolding cong_int_def cong_nat_def
  by (metis int_nat_eq nat_mod_distrib zmod_int)

declare transfer_morphism_nat_int [transfer add return: transfer_nat_int_cong]

lemma transfer_int_nat_cong: "[int x = int y] (mod (int m)) = [x = y] (mod m)"
  by (auto simp add: cong_int_def cong_nat_def) (auto simp add: zmod_int [symmetric])

declare transfer_morphism_int_nat [transfer add return: transfer_int_nat_cong]


subsection \<open>Congruence\<close>

(* was zcong_0, etc. *)
lemma cong_0_nat [simp, presburger]: "[a = b] (mod 0) \<longleftrightarrow> a = b"
  for a b :: nat
  by (auto simp: cong_nat_def)

lemma cong_0_int [simp, presburger]: "[a = b] (mod 0) \<longleftrightarrow> a = b"
  for a b :: int
  by (auto simp: cong_int_def)

lemma cong_1_nat [simp, presburger]: "[a = b] (mod 1)"
  for a b :: nat
  by (auto simp: cong_nat_def)

lemma cong_Suc_0_nat [simp, presburger]: "[a = b] (mod Suc 0)"
  for a b :: nat
  by (auto simp: cong_nat_def)

lemma cong_1_int [simp, presburger]: "[a = b] (mod 1)"
  for a b :: int
  by (auto simp: cong_int_def)

lemma cong_refl_nat [simp]: "[k = k] (mod m)"
  for k :: nat
  by (auto simp: cong_nat_def)

lemma cong_refl_int [simp]: "[k = k] (mod m)"
  for k :: int
  by (auto simp: cong_int_def)

lemma cong_sym_nat: "[a = b] (mod m) \<Longrightarrow> [b = a] (mod m)"
  for a b :: nat
  by (auto simp: cong_nat_def)

lemma cong_sym_int: "[a = b] (mod m) \<Longrightarrow> [b = a] (mod m)"
  for a b :: int
  by (auto simp: cong_int_def)

lemma cong_sym_eq_nat: "[a = b] (mod m) = [b = a] (mod m)"
  for a b :: nat
  by (auto simp: cong_nat_def)

lemma cong_sym_eq_int: "[a = b] (mod m) = [b = a] (mod m)"
  for a b :: int
  by (auto simp: cong_int_def)

lemma cong_trans_nat [trans]: "[a = b] (mod m) \<Longrightarrow> [b = c] (mod m) \<Longrightarrow> [a = c] (mod m)"
  for a b c :: nat
  by (auto simp: cong_nat_def)

lemma cong_trans_int [trans]: "[a = b] (mod m) \<Longrightarrow> [b = c] (mod m) \<Longrightarrow> [a = c] (mod m)"
  for a b c :: int
  by (auto simp: cong_int_def)

lemma cong_add_nat: "[a = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a + c = b + d] (mod m)"
  for a b c :: nat
  unfolding cong_nat_def by (metis mod_add_cong)

lemma cong_add_int: "[a = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a + c = b + d] (mod m)"
  for a b c :: int
  unfolding cong_int_def by (metis mod_add_cong)

lemma cong_diff_int: "[a = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a - c = b - d] (mod m)"
  for a b c :: int
  unfolding cong_int_def by (metis mod_diff_cong)

lemma cong_diff_aux_int:
  "[a = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow>
    a \<ge> c \<Longrightarrow> b \<ge> d \<Longrightarrow> [tsub a c = tsub b d] (mod m)"
  for a b c d :: int
  by (metis cong_diff_int tsub_eq)

lemma cong_diff_nat:
  fixes a b c d :: nat
  assumes "[a = b] (mod m)" "[c = d] (mod m)" "a \<ge> c" "b \<ge> d"
  shows "[a - c = b - d] (mod m)"
  using assms by (rule cong_diff_aux_int [transferred])

lemma cong_mult_nat: "[a = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a * c = b * d] (mod m)"
  for a b c d :: nat
  unfolding cong_nat_def  by (metis mod_mult_cong)

lemma cong_mult_int: "[a = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a * c = b * d] (mod m)"
  for a b c d :: int
  unfolding cong_int_def  by (metis mod_mult_cong)

lemma cong_exp_nat: "[x = y] (mod n) \<Longrightarrow> [x^k = y^k] (mod n)"
  for x y :: nat
  by (induct k) (auto simp: cong_mult_nat)

lemma cong_exp_int: "[x = y] (mod n) \<Longrightarrow> [x^k = y^k] (mod n)"
  for x y :: int
  by (induct k) (auto simp: cong_mult_int)

lemma cong_sum_nat: "(\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (mod m)) \<Longrightarrow> [(\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. g x)] (mod m)"
  for f g :: "'a \<Rightarrow> nat"
  by (induct A rule: infinite_finite_induct) (auto intro: cong_add_nat)

lemma cong_sum_int: "(\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (mod m)) \<Longrightarrow> [(\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. g x)] (mod m)"
  for f g :: "'a \<Rightarrow> int"
  by (induct A rule: infinite_finite_induct) (auto intro: cong_add_int)

lemma cong_prod_nat: "(\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (mod m)) \<Longrightarrow> [(\<Prod>x\<in>A. f x) = (\<Prod>x\<in>A. g x)] (mod m)"
  for f g :: "'a \<Rightarrow> nat"
  by (induct A rule: infinite_finite_induct) (auto intro: cong_mult_nat)

lemma cong_prod_int: "(\<And>x. x \<in> A \<Longrightarrow> [f x = g x] (mod m)) \<Longrightarrow> [(\<Prod>x\<in>A. f x) = (\<Prod>x\<in>A. g x)] (mod m)"
  for f g :: "'a \<Rightarrow> int"
  by (induct A rule: infinite_finite_induct) (auto intro: cong_mult_int)

lemma cong_scalar_nat: "[a = b] (mod m) \<Longrightarrow> [a * k = b * k] (mod m)"
  for a b k :: nat
  by (rule cong_mult_nat) simp_all

lemma cong_scalar_int: "[a = b] (mod m) \<Longrightarrow> [a * k = b * k] (mod m)"
  for a b k :: int
  by (rule cong_mult_int) simp_all

lemma cong_scalar2_nat: "[a = b] (mod m) \<Longrightarrow> [k * a = k * b] (mod m)"
  for a b k :: nat
  by (rule cong_mult_nat) simp_all

lemma cong_scalar2_int: "[a = b] (mod m) \<Longrightarrow> [k * a = k * b] (mod m)"
  for a b k :: int
  by (rule cong_mult_int) simp_all

lemma cong_mult_self_nat: "[a * m = 0] (mod m)"
  for a m :: nat
  by (auto simp: cong_nat_def)

lemma cong_mult_self_int: "[a * m = 0] (mod m)"
  for a m :: int
  by (auto simp: cong_int_def)

lemma cong_eq_diff_cong_0_int: "[a = b] (mod m) = [a - b = 0] (mod m)"
  for a b :: int
  by (metis cong_add_int cong_diff_int cong_refl_int diff_add_cancel diff_self)

lemma cong_eq_diff_cong_0_aux_int: "a \<ge> b \<Longrightarrow> [a = b] (mod m) = [tsub a b = 0] (mod m)"
  for a b :: int
  by (subst tsub_eq, assumption, rule cong_eq_diff_cong_0_int)

lemma cong_eq_diff_cong_0_nat:
  fixes a b :: nat
  assumes "a \<ge> b"
  shows "[a = b] (mod m) = [a - b = 0] (mod m)"
  using assms by (rule cong_eq_diff_cong_0_aux_int [transferred])

lemma cong_diff_cong_0'_nat:
  "[x = y] (mod n) \<longleftrightarrow> (if x \<le> y then [y - x = 0] (mod n) else [x - y = 0] (mod n))"
  for x y :: nat
  by (metis cong_eq_diff_cong_0_nat cong_sym_nat nat_le_linear)

lemma cong_altdef_nat: "a \<ge> b \<Longrightarrow> [a = b] (mod m) \<longleftrightarrow> m dvd (a - b)"
  for a b :: nat
  apply (subst cong_eq_diff_cong_0_nat, assumption)
  apply (unfold cong_nat_def)
  apply (simp add: dvd_eq_mod_eq_0 [symmetric])
  done

lemma cong_altdef_int: "[a = b] (mod m) \<longleftrightarrow> m dvd (a - b)"
  for a b :: int
  by (metis cong_int_def mod_eq_dvd_iff)

lemma cong_abs_int: "[x = y] (mod abs m) \<longleftrightarrow> [x = y] (mod m)"
  for x y :: int
  by (simp add: cong_altdef_int)

lemma cong_square_int:
  "prime p \<Longrightarrow> 0 < a \<Longrightarrow> [a * a = 1] (mod p) \<Longrightarrow> [a = 1] (mod p) \<or> [a = - 1] (mod p)"
  for a :: int
  apply (simp only: cong_altdef_int)
  apply (subst prime_dvd_mult_eq_int [symmetric], assumption)
  apply (auto simp add: field_simps)
  done

lemma cong_mult_rcancel_int: "coprime k m \<Longrightarrow> [a * k = b * k] (mod m) = [a = b] (mod m)"
  for a k m :: int
  by (metis cong_altdef_int left_diff_distrib coprime_dvd_mult_iff gcd.commute)

lemma cong_mult_rcancel_nat: "coprime k m \<Longrightarrow> [a * k = b * k] (mod m) = [a = b] (mod m)"
  for a k m :: nat
  by (metis cong_mult_rcancel_int [transferred])

lemma cong_mult_lcancel_nat: "coprime k m \<Longrightarrow> [k * a = k * b ] (mod m) = [a = b] (mod m)"
  for a k m :: nat
  by (simp add: mult.commute cong_mult_rcancel_nat)

lemma cong_mult_lcancel_int: "coprime k m \<Longrightarrow> [k * a = k * b] (mod m) = [a = b] (mod m)"
  for a k m :: int
  by (simp add: mult.commute cong_mult_rcancel_int)

(* was zcong_zgcd_zmult_zmod *)
lemma coprime_cong_mult_int:
  "[a = b] (mod m) \<Longrightarrow> [a = b] (mod n) \<Longrightarrow> coprime m n \<Longrightarrow> [a = b] (mod m * n)"
  for a b :: int
  by (metis divides_mult cong_altdef_int)

lemma coprime_cong_mult_nat:
  "[a = b] (mod m) \<Longrightarrow> [a = b] (mod n) \<Longrightarrow> coprime m n \<Longrightarrow> [a = b] (mod m * n)"
  for a b :: nat
  by (metis coprime_cong_mult_int [transferred])

lemma cong_less_imp_eq_nat: "0 \<le> a \<Longrightarrow> a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  for a b :: nat
  by (auto simp add: cong_nat_def)

lemma cong_less_imp_eq_int: "0 \<le> a \<Longrightarrow> a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  for a b :: int
  by (auto simp add: cong_int_def)

lemma cong_less_unique_nat: "0 < m \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  for a m :: nat
  by (auto simp: cong_nat_def) (metis mod_less_divisor mod_mod_trivial)

lemma cong_less_unique_int: "0 < m \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  for a m :: int
  by (auto simp: cong_int_def)  (metis mod_mod_trivial pos_mod_conj)

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
      apply (subst (asm) cong_sym_eq_nat)
      apply (auto simp: cong_altdef_nat)
      apply (metis add_0_right add_diff_inverse dvd_div_mult_self less_or_eq_imp_le mult_0)
      done
  qed
next
  assume ?rhs
  then show ?lhs
    by (metis cong_nat_def mod_mult_self2 mult.commute)
qed

lemma cong_gcd_eq_int: "[a = b] (mod m) \<Longrightarrow> gcd a m = gcd b m"
  for a b :: int
  by (metis cong_int_def gcd_red_int)

lemma cong_gcd_eq_nat: "[a = b] (mod m) \<Longrightarrow> gcd a m = gcd b m"
  for a b :: nat
  by (metis cong_gcd_eq_int [transferred])

lemma cong_imp_coprime_nat: "[a = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> coprime b m"
  for a b :: nat
  by (auto simp add: cong_gcd_eq_nat)

lemma cong_imp_coprime_int: "[a = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> coprime b m"
  for a b :: int
  by (auto simp add: cong_gcd_eq_int)

lemma cong_cong_mod_nat: "[a = b] (mod m) \<longleftrightarrow> [a mod m = b mod m] (mod m)"
  for a b :: nat
  by (auto simp add: cong_nat_def)

lemma cong_cong_mod_int: "[a = b] (mod m) \<longleftrightarrow> [a mod m = b mod m] (mod m)"
  for a b :: int
  by (auto simp add: cong_int_def)

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

lemma cong_dvd_eq_nat: "[x = y] (mod n) \<Longrightarrow> n dvd x \<longleftrightarrow> n dvd y"
  for x y :: nat
  by (auto simp: cong_nat_def dvd_eq_mod_eq_0)

lemma cong_dvd_eq_int: "[x = y] (mod n) \<Longrightarrow> n dvd x \<longleftrightarrow> n dvd y"
  for x y :: int
  by (auto simp: cong_int_def dvd_eq_mod_eq_0)

lemma cong_mod_nat: "n \<noteq> 0 \<Longrightarrow> [a mod n = a] (mod n)"
  for a n :: nat
  by (simp add: cong_nat_def)

lemma cong_mod_int: "n \<noteq> 0 \<Longrightarrow> [a mod n = a] (mod n)"
  for a n :: int
  by (simp add: cong_int_def)

lemma mod_mult_cong_nat: "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> [x mod (a * b) = y] (mod a) \<longleftrightarrow> [x = y] (mod a)"
  for a b :: nat
  by (simp add: cong_nat_def mod_mult2_eq  mod_add_left_eq)

lemma neg_cong_int: "[a = b] (mod m) \<longleftrightarrow> [- a = - b] (mod m)"
  for a b :: int
  by (metis cong_int_def minus_minus mod_minus_cong)

lemma cong_modulus_neg_int: "[a = b] (mod m) \<longleftrightarrow> [a = b] (mod - m)"
  for a b :: int
  by (auto simp add: cong_altdef_int)

lemma mod_mult_cong_int: "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> [x mod (a * b) = y] (mod a) \<longleftrightarrow> [x = y] (mod a)"
  for a b :: int
proof (cases "b > 0")
  case True
  then show ?thesis
    by (simp add: cong_int_def mod_mod_cancel mod_add_left_eq)
next
  case False
  then show ?thesis
    apply (subst (1 2) cong_modulus_neg_int)
    apply (unfold cong_int_def)
    apply (subgoal_tac "a * b = (- a * - b)")
     apply (erule ssubst)
     apply (subst zmod_zmult2_eq)
      apply (auto simp add: mod_add_left_eq mod_minus_right div_minus_right)
     apply (metis mod_diff_left_eq mod_diff_right_eq mod_mult_self1_is_0 diff_zero)+
    done
qed

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
  by (auto simp: cong_nat_def)

lemma cong_0_1_nat: "[0 = 1] (mod n) \<longleftrightarrow> n = 1"
  for n :: nat
  by (auto simp: cong_nat_def)

lemma cong_0_1_int: "[0 = 1] (mod n) \<longleftrightarrow> n = 1 \<or> n = - 1"
  for n :: int
  by (auto simp: cong_int_def zmult_eq_1_iff)

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
    by auto (metis cong_add_rcancel_0_nat cong_mult_self_nat mult.commute)
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
    by (elim cong_scalar2_nat)
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
    by (elim cong_scalar2_int)
  also from b have "(d div gcd a n) * gcd a n = d"
    by (rule dvd_div_mult_self)
  also have "(d div gcd a n) * (a * x) = a * (d div gcd a n * x)"
    by auto
  finally show ?thesis
    by auto
qed

lemma cong_solve_coprime_nat:
  fixes a :: nat
  assumes "coprime a n"
  shows "\<exists>x. [a * x = 1] (mod n)"
proof (cases "a = 0")
  case True
  with assms show ?thesis by force
next
  case False
  with assms show ?thesis by (metis cong_solve_nat)
qed

lemma cong_solve_coprime_int: "coprime (a::int) n \<Longrightarrow> \<exists>x. [a * x = 1] (mod n)"
  apply (cases "a = 0")
   apply auto
   apply (cases "n \<ge> 0")
    apply auto
  apply (metis cong_solve_int)
  done

lemma coprime_iff_invertible_nat:
  "m > 0 \<Longrightarrow> coprime a m = (\<exists>x. [a * x = Suc 0] (mod m))"
  by (metis One_nat_def cong_gcd_eq_nat cong_solve_coprime_nat coprime_lmult gcd.commute gcd_Suc_0)

lemma coprime_iff_invertible_int: "m > 0 \<Longrightarrow> coprime a m \<longleftrightarrow> (\<exists>x. [a * x = 1] (mod m))"
  for m :: int
  apply (auto intro: cong_solve_coprime_int)
  apply (metis cong_int_def coprime_mul_eq gcd_1_int gcd.commute gcd_red_int)
  done

lemma coprime_iff_invertible'_nat:
  "m > 0 \<Longrightarrow> coprime a m \<longleftrightarrow> (\<exists>x. 0 \<le> x \<and> x < m \<and> [a * x = Suc 0] (mod m))"
  apply (subst coprime_iff_invertible_nat)
   apply auto
  apply (auto simp add: cong_nat_def)
  apply (metis mod_less_divisor mod_mult_right_eq)
  done

lemma coprime_iff_invertible'_int:
  "m > 0 \<Longrightarrow> coprime a m \<longleftrightarrow> (\<exists>x. 0 \<le> x \<and> x < m \<and> [a * x = 1] (mod m))"
  for m :: int
  apply (subst coprime_iff_invertible_int)
   apply (auto simp add: cong_int_def)
  apply (metis mod_mult_right_eq pos_mod_conj)
  done

lemma cong_cong_lcm_nat: "[x = y] (mod a) \<Longrightarrow> [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  for x y :: nat
  apply (cases "y \<le> x")
  apply (metis cong_altdef_nat lcm_least)
  apply (meson cong_altdef_nat cong_sym_nat lcm_least_iff nat_le_linear)
  done

lemma cong_cong_lcm_int: "[x = y] (mod a) \<Longrightarrow> [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  for x y :: int
  by (auto simp add: cong_altdef_int lcm_least)

lemma cong_cong_prod_coprime_nat [rule_format]: "finite A \<Longrightarrow>
    (\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
    (\<forall>i\<in>A. [(x::nat) = y] (mod m i)) \<longrightarrow>
      [x = y] (mod (\<Prod>i\<in>A. m i))"
  apply (induct set: finite)
  apply auto
  apply (metis One_nat_def coprime_cong_mult_nat gcd.commute prod_coprime)
  done

lemma cong_cong_prod_coprime_int [rule_format]: "finite A \<Longrightarrow>
    (\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
    (\<forall>i\<in>A. [(x::int) = y] (mod m i)) \<longrightarrow>
      [x = y] (mod (\<Prod>i\<in>A. m i))"
  apply (induct set: finite)
  apply auto
  apply (metis coprime_cong_mult_int gcd.commute prod_coprime)
  done

lemma binary_chinese_remainder_aux_nat:
  fixes m1 m2 :: nat
  assumes a: "coprime m1 m2"
  shows "\<exists>b1 b2. [b1 = 1] (mod m1) \<and> [b1 = 0] (mod m2) \<and> [b2 = 0] (mod m1) \<and> [b2 = 1] (mod m2)"
proof -
  from cong_solve_coprime_nat [OF a] obtain x1 where 1: "[m1 * x1 = 1] (mod m2)"
    by auto
  from a have b: "coprime m2 m1"
    by (subst gcd.commute)
  from cong_solve_coprime_nat [OF b] obtain x2 where 2: "[m2 * x2 = 1] (mod m1)"
    by auto
  have "[m1 * x1 = 0] (mod m1)"
    by (subst mult.commute) (rule cong_mult_self_nat)
  moreover have "[m2 * x2 = 0] (mod m2)"
    by (subst mult.commute) (rule cong_mult_self_nat)
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
    by (subst gcd.commute)
  from cong_solve_coprime_int [OF b] obtain x2 where 2: "[m2 * x2 = 1] (mod m1)"
    by auto
  have "[m1 * x1 = 0] (mod m1)"
    by (subst mult.commute) (rule cong_mult_self_int)
  moreover have "[m2 * x2 = 0] (mod m2)"
    by (subst mult.commute) (rule cong_mult_self_int)
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
    apply (rule cong_add_nat)
     apply (rule cong_scalar2_nat)
     apply (rule \<open>[b1 = 1] (mod m1)\<close>)
    apply (rule cong_scalar2_nat)
    apply (rule \<open>[b2 = 0] (mod m1)\<close>)
    done
  then have "[?x = u1] (mod m1)" by simp
  have "[?x = u1 * 0 + u2 * 1] (mod m2)"
    apply (rule cong_add_nat)
     apply (rule cong_scalar2_nat)
     apply (rule \<open>[b1 = 0] (mod m2)\<close>)
    apply (rule cong_scalar2_nat)
    apply (rule \<open>[b2 = 1] (mod m2)\<close>)
    done
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
    apply (rule cong_add_int)
     apply (rule cong_scalar2_int)
     apply (rule \<open>[b1 = 1] (mod m1)\<close>)
    apply (rule cong_scalar2_int)
    apply (rule \<open>[b2 = 0] (mod m1)\<close>)
    done
  then have "[?x = u1] (mod m1)" by simp
  have "[?x = u1 * 0 + u2 * 1] (mod m2)"
    apply (rule cong_add_int)
     apply (rule cong_scalar2_int)
     apply (rule \<open>[b1 = 0] (mod m2)\<close>)
    apply (rule cong_scalar2_int)
    apply (rule \<open>[b2 = 1] (mod m2)\<close>)
    done
  then have "[?x = u2] (mod m2)" by simp
  with \<open>[?x = u1] (mod m1)\<close> show ?thesis
    by blast
qed

lemma cong_modulus_mult_nat: "[x = y] (mod m * n) \<Longrightarrow> [x = y] (mod m)"
  for x y :: nat
  apply (cases "y \<le> x")
   apply (simp add: cong_altdef_nat)
   apply (erule dvd_mult_left)
  apply (rule cong_sym_nat)
  apply (subst (asm) cong_sym_eq_nat)
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
  by (simp add: cong_nat_def)

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
    apply (rule cong_trans_nat)
     prefer 2
     apply (rule \<open>[y = u1] (mod m1)\<close>)
    apply (rule cong_modulus_mult_nat)
    apply (rule cong_mod_nat)
    using nz apply auto
    done
  have 2: "[?x = u2] (mod m2)"
    apply (rule cong_trans_nat)
     prefer 2
     apply (rule \<open>[y = u2] (mod m2)\<close>)
    apply (subst mult.commute)
    apply (rule cong_modulus_mult_nat)
    apply (rule cong_mod_nat)
    using nz apply auto
    done
  have "\<forall>z. z < m1 * m2 \<and> [z = u1] (mod m1) \<and> [z = u2] (mod m2) \<longrightarrow> z = ?x"
  proof clarify
    fix z
    assume "z < m1 * m2"
    assume "[z = u1] (mod m1)" and  "[z = u2] (mod m2)"
    have "[?x = z] (mod m1)"
      apply (rule cong_trans_nat)
       apply (rule \<open>[?x = u1] (mod m1)\<close>)
      apply (rule cong_sym_nat)
      apply (rule \<open>[z = u1] (mod m1)\<close>)
      done
    moreover have "[?x = z] (mod m2)"
      apply (rule cong_trans_nat)
       apply (rule \<open>[?x = u2] (mod m2)\<close>)
      apply (rule cong_sym_nat)
      apply (rule \<open>[z = u2] (mod m2)\<close>)
      done
    ultimately have "[?x = z] (mod m1 * m2)"
      by (auto intro: coprime_cong_mult_nat a)
    with \<open>z < m1 * m2\<close> \<open>?x < m1 * m2\<close> show "z = ?x"
      apply (intro cong_less_modulus_unique_nat)
        apply (auto, erule cong_sym_nat)
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
    by (intro prod_coprime) auto
  then have "\<exists>x. [(\<Prod>j \<in> A - {i}. m j) * x = 1] (mod m i)"
    by (elim cong_solve_coprime_nat)
  then obtain x where "[(\<Prod>j \<in> A - {i}. m j) * x = 1] (mod m i)"
    by auto
  moreover have "[(\<Prod>j \<in> A - {i}. m j) * x = 0] (mod (\<Prod>j \<in> A - {i}. m j))"
    by (subst mult.commute, rule cong_mult_self_nat)
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
        apply (rule cong_add_nat)
         apply (rule cong_scalar2_nat)
        using b a apply blast
        apply (rule cong_sum_nat)
        apply (rule cong_scalar2_nat)
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

lemma coprime_cong_prod_nat [rule_format]: "finite A \<Longrightarrow>
    (\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
      (\<forall>i\<in>A. [(x::nat) = y] (mod m i)) \<longrightarrow>
         [x = y] (mod (\<Prod>i\<in>A. m i))"
  apply (induct set: finite)
  apply auto
  apply (metis One_nat_def coprime_cong_mult_nat gcd.commute prod_coprime)
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
    apply (rule cong_trans_nat)
     prefer 2
    using one apply auto
    apply (rule cong_dvd_modulus_nat)
     apply (rule cong_mod_nat)
    using prodnz apply auto
    apply rule
     apply (rule fin)
    apply assumption
    done
  have unique: "\<forall>z. z < (\<Prod>i\<in>A. m i) \<and> (\<forall>i\<in>A. [z = u i] (mod m i)) \<longrightarrow> z = ?x"
  proof clarify
    fix z
    assume zless: "z < (\<Prod>i\<in>A. m i)"
    assume zcong: "(\<forall>i\<in>A. [z = u i] (mod m i))"
    have "\<forall>i\<in>A. [?x = z] (mod m i)"
      apply clarify
      apply (rule cong_trans_nat)
      using cong apply (erule bspec)
      apply (rule cong_sym_nat)
      using zcong apply auto
      done
    with fin cop have "[?x = z] (mod (\<Prod>i\<in>A. m i))"
      apply (intro coprime_cong_prod_nat)
        apply auto
      done
    with zless less show "z = ?x"
      apply (intro cong_less_modulus_unique_nat)
        apply auto
      apply (erule cong_sym_nat)
      done
  qed
  from less cong unique show ?thesis
    by blast
qed

end
