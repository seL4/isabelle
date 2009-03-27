(*  Title:      HOL/Library/Parity.thy
    Author:     Jeremy Avigad, Jacques D. Fleuriot
*)

header {* Even and Odd for int and nat *}

theory Parity
imports Main
begin

class even_odd = 
  fixes even :: "'a \<Rightarrow> bool"

abbreviation
  odd :: "'a\<Colon>even_odd \<Rightarrow> bool" where
  "odd x \<equiv> \<not> even x"

instantiation nat and int  :: even_odd
begin

definition
  even_def [presburger]: "even x \<longleftrightarrow> (x\<Colon>int) mod 2 = 0"

definition
  even_nat_def [presburger]: "even x \<longleftrightarrow> even (int x)"

instance ..

end


subsection {* Even and odd are mutually exclusive *}

lemma int_pos_lt_two_imp_zero_or_one:
    "0 <= x ==> (x::int) < 2 ==> x = 0 | x = 1"
  by presburger

lemma neq_one_mod_two [simp, presburger]: 
  "((x::int) mod 2 ~= 0) = (x mod 2 = 1)" by presburger


subsection {* Behavior under integer arithmetic operations *}
declare dvd_def[algebra]
lemma nat_even_iff_2_dvd[algebra]: "even (x::nat) \<longleftrightarrow> 2 dvd x"
  by (presburger add: even_nat_def even_def)
lemma int_even_iff_2_dvd[algebra]: "even (x::int) \<longleftrightarrow> 2 dvd x"
  by presburger

lemma even_times_anything: "even (x::int) ==> even (x * y)"
  by algebra

lemma anything_times_even: "even (y::int) ==> even (x * y)" by algebra

lemma odd_times_odd: "odd (x::int) ==> odd y ==> odd (x * y)" 
  by (simp add: even_def zmod_zmult1_eq)

lemma even_product[presburger]: "even((x::int) * y) = (even x | even y)"
  apply (auto simp add: even_times_anything anything_times_even)
  apply (rule ccontr)
  apply (auto simp add: odd_times_odd)
  done

lemma even_plus_even: "even (x::int) ==> even y ==> even (x + y)"
  by presburger

lemma even_plus_odd: "even (x::int) ==> odd y ==> odd (x + y)"
  by presburger

lemma odd_plus_even: "odd (x::int) ==> even y ==> odd (x + y)"
  by presburger

lemma odd_plus_odd: "odd (x::int) ==> odd y ==> even (x + y)" by presburger

lemma even_sum[presburger]: "even ((x::int) + y) = ((even x & even y) | (odd x & odd y))"
  by presburger

lemma even_neg[presburger, algebra]: "even (-(x::int)) = even x" by presburger

lemma even_difference:
    "even ((x::int) - y) = ((even x & even y) | (odd x & odd y))" by presburger

lemma even_pow_gt_zero:
    "even (x::int) ==> 0 < n ==> even (x^n)"
  by (induct n) (auto simp add: even_product)

lemma odd_pow_iff[presburger, algebra]: 
  "odd ((x::int) ^ n) \<longleftrightarrow> (n = 0 \<or> odd x)"
  apply (induct n, simp_all)
  apply presburger
  apply (case_tac n, auto)
  apply (simp_all add: even_product)
  done

lemma odd_pow: "odd x ==> odd((x::int)^n)" by (simp add: odd_pow_iff)

lemma even_power[presburger]: "even ((x::int)^n) = (even x & 0 < n)"
  apply (auto simp add: even_pow_gt_zero)
  apply (erule contrapos_pp, erule odd_pow)
  apply (erule contrapos_pp, simp add: even_def)
  done

lemma even_zero[presburger]: "even (0::int)" by presburger

lemma odd_one[presburger]: "odd (1::int)" by presburger

lemmas even_odd_simps [simp] = even_def[of "number_of v",standard] even_zero
  odd_one even_product even_sum even_neg even_difference even_power


subsection {* Equivalent definitions *}

lemma two_times_even_div_two: "even (x::int) ==> 2 * (x div 2) = x" 
  by presburger

lemma two_times_odd_div_two_plus_one: "odd (x::int) ==>
    2 * (x div 2) + 1 = x" by presburger

lemma even_equiv_def: "even (x::int) = (EX y. x = 2 * y)" by presburger

lemma odd_equiv_def: "odd (x::int) = (EX y. x = 2 * y + 1)" by presburger

subsection {* even and odd for nats *}

lemma pos_int_even_equiv_nat_even: "0 \<le> x ==> even x = even (nat x)"
  by (simp add: even_nat_def)

lemma even_nat_product[presburger, algebra]: "even((x::nat) * y) = (even x | even y)"
  by (simp add: even_nat_def int_mult)

lemma even_nat_sum[presburger, algebra]: "even ((x::nat) + y) =
    ((even x & even y) | (odd x & odd y))" by presburger

lemma even_nat_difference[presburger, algebra]:
    "even ((x::nat) - y) = (x < y | (even x & even y) | (odd x & odd y))"
by presburger

lemma even_nat_Suc[presburger, algebra]: "even (Suc x) = odd x" by presburger

lemma even_nat_power[presburger, algebra]: "even ((x::nat)^y) = (even x & 0 < y)"
  by (simp add: even_nat_def int_power)

lemma even_nat_zero[presburger]: "even (0::nat)" by presburger

lemmas even_odd_nat_simps [simp] = even_nat_def[of "number_of v",standard]
  even_nat_zero even_nat_Suc even_nat_product even_nat_sum even_nat_power


subsection {* Equivalent definitions *}

lemma nat_lt_two_imp_zero_or_one: "(x::nat) < Suc (Suc 0) ==>
    x = 0 | x = Suc 0" by presburger

lemma even_nat_mod_two_eq_zero: "even (x::nat) ==> x mod (Suc (Suc 0)) = 0"
  by presburger

lemma odd_nat_mod_two_eq_one: "odd (x::nat) ==> x mod (Suc (Suc 0)) = Suc 0"
by presburger

lemma even_nat_equiv_def: "even (x::nat) = (x mod Suc (Suc 0) = 0)"
  by presburger

lemma odd_nat_equiv_def: "odd (x::nat) = (x mod Suc (Suc 0) = Suc 0)"
  by presburger

lemma even_nat_div_two_times_two: "even (x::nat) ==>
    Suc (Suc 0) * (x div Suc (Suc 0)) = x" by presburger

lemma odd_nat_div_two_times_two_plus_one: "odd (x::nat) ==>
    Suc( Suc (Suc 0) * (x div Suc (Suc 0))) = x" by presburger

lemma even_nat_equiv_def2: "even (x::nat) = (EX y. x = Suc (Suc 0) * y)"
  by presburger

lemma odd_nat_equiv_def2: "odd (x::nat) = (EX y. x = Suc(Suc (Suc 0) * y))"
  by presburger


subsection {* Parity and powers *}

lemma  minus_one_even_odd_power:
     "(even x --> (- 1::'a::{comm_ring_1,recpower})^x = 1) &
      (odd x --> (- 1::'a)^x = - 1)"
  apply (induct x)
  apply (rule conjI)
  apply simp
  apply (insert even_nat_zero, blast)
  apply (simp add: power_Suc)
  done

lemma minus_one_even_power [simp]:
    "even x ==> (- 1::'a::{comm_ring_1,recpower})^x = 1"
  using minus_one_even_odd_power by blast

lemma minus_one_odd_power [simp]:
    "odd x ==> (- 1::'a::{comm_ring_1,recpower})^x = - 1"
  using minus_one_even_odd_power by blast

lemma neg_one_even_odd_power:
     "(even x --> (-1::'a::{number_ring,recpower})^x = 1) &
      (odd x --> (-1::'a)^x = -1)"
  apply (induct x)
  apply (simp, simp add: power_Suc)
  done

lemma neg_one_even_power [simp]:
    "even x ==> (-1::'a::{number_ring,recpower})^x = 1"
  using neg_one_even_odd_power by blast

lemma neg_one_odd_power [simp]:
    "odd x ==> (-1::'a::{number_ring,recpower})^x = -1"
  using neg_one_even_odd_power by blast

lemma neg_power_if:
     "(-x::'a::{comm_ring_1,recpower}) ^ n =
      (if even n then (x ^ n) else -(x ^ n))"
  apply (induct n)
  apply (simp_all split: split_if_asm add: power_Suc)
  done

lemma zero_le_even_power: "even n ==>
    0 <= (x::'a::{recpower,ordered_ring_strict}) ^ n"
  apply (simp add: even_nat_equiv_def2)
  apply (erule exE)
  apply (erule ssubst)
  apply (subst power_add)
  apply (rule zero_le_square)
  done

lemma zero_le_odd_power: "odd n ==>
    (0 <= (x::'a::{recpower,ordered_idom}) ^ n) = (0 <= x)"
apply (auto simp: odd_nat_equiv_def2 power_Suc power_add zero_le_mult_iff)
apply (metis field_power_not_zero no_zero_divirors_neq0 order_antisym_conv zero_le_square)
done

lemma zero_le_power_eq[presburger]: "(0 <= (x::'a::{recpower,ordered_idom}) ^ n) =
    (even n | (odd n & 0 <= x))"
  apply auto
  apply (subst zero_le_odd_power [symmetric])
  apply assumption+
  apply (erule zero_le_even_power)
  done

lemma zero_less_power_eq[presburger]: "(0 < (x::'a::{recpower,ordered_idom}) ^ n) =
    (n = 0 | (even n & x ~= 0) | (odd n & 0 < x))"

  unfolding order_less_le zero_le_power_eq by auto

lemma power_less_zero_eq[presburger]: "((x::'a::{recpower,ordered_idom}) ^ n < 0) =
    (odd n & x < 0)"
  apply (subst linorder_not_le [symmetric])+
  apply (subst zero_le_power_eq)
  apply auto
  done

lemma power_le_zero_eq[presburger]: "((x::'a::{recpower,ordered_idom}) ^ n <= 0) =
    (n ~= 0 & ((odd n & x <= 0) | (even n & x = 0)))"
  apply (subst linorder_not_less [symmetric])+
  apply (subst zero_less_power_eq)
  apply auto
  done

lemma power_even_abs: "even n ==>
    (abs (x::'a::{recpower,ordered_idom}))^n = x^n"
  apply (subst power_abs [symmetric])
  apply (simp add: zero_le_even_power)
  done

lemma zero_less_power_nat_eq[presburger]: "(0 < (x::nat) ^ n) = (n = 0 | 0 < x)"
  by (induct n) auto

lemma power_minus_even [simp]: "even n ==>
    (- x)^n = (x^n::'a::{recpower,comm_ring_1})"
  apply (subst power_minus)
  apply simp
  done

lemma power_minus_odd [simp]: "odd n ==>
    (- x)^n = - (x^n::'a::{recpower,comm_ring_1})"
  apply (subst power_minus)
  apply simp
  done

lemma power_mono_even: fixes x y :: "'a :: {recpower, ordered_idom}"
  assumes "even n" and "\<bar>x\<bar> \<le> \<bar>y\<bar>"
  shows "x^n \<le> y^n"
proof -
  have "0 \<le> \<bar>x\<bar>" by auto
  with `\<bar>x\<bar> \<le> \<bar>y\<bar>`
  have "\<bar>x\<bar>^n \<le> \<bar>y\<bar>^n" by (rule power_mono)
  thus ?thesis unfolding power_even_abs[OF `even n`] .
qed

lemma odd_pos: "odd (n::nat) \<Longrightarrow> 0 < n" by presburger

lemma power_mono_odd: fixes x y :: "'a :: {recpower, ordered_idom}"
  assumes "odd n" and "x \<le> y"
  shows "x^n \<le> y^n"
proof (cases "y < 0")
  case True with `x \<le> y` have "-y \<le> -x" and "0 \<le> -y" by auto
  hence "(-y)^n \<le> (-x)^n" by (rule power_mono)
  thus ?thesis unfolding power_minus_odd[OF `odd n`] by auto
next
  case False
  show ?thesis
  proof (cases "x < 0")
    case True hence "n \<noteq> 0" and "x \<le> 0" using `odd n`[THEN odd_pos] by auto
    hence "x^n \<le> 0" unfolding power_le_zero_eq using `odd n` by auto
    moreover
    from `\<not> y < 0` have "0 \<le> y" by auto
    hence "0 \<le> y^n" by auto
    ultimately show ?thesis by auto
  next
    case False hence "0 \<le> x" by auto
    with `x \<le> y` show ?thesis using power_mono by auto
  qed
qed

subsection {* General Lemmas About Division *}

lemma Suc_times_mod_eq: "1<k ==> Suc (k * m) mod k = 1" 
apply (induct "m")
apply (simp_all add: mod_Suc)
done

declare Suc_times_mod_eq [of "number_of w", standard, simp]

lemma [simp]: "n div k \<le> (Suc n) div k"
by (simp add: div_le_mono) 

lemma Suc_n_div_2_gt_zero [simp]: "(0::nat) < n ==> 0 < (n + 1) div 2"
by arith

lemma div_2_gt_zero [simp]: "(1::nat) < n ==> 0 < n div 2" 
by arith

  (* Potential use of algebra : Equality modulo n*)
lemma mod_mult_self3 [simp]: "(k*n + m) mod n = m mod (n::nat)"
by (simp add: mult_ac add_ac)

lemma mod_mult_self4 [simp]: "Suc (k*n + m) mod n = Suc m mod n"
proof -
  have "Suc (k * n + m) mod n = (k * n + Suc m) mod n" by simp
  also have "... = Suc m mod n" by (rule mod_mult_self3) 
  finally show ?thesis .
qed

lemma mod_Suc_eq_Suc_mod: "Suc m mod n = Suc (m mod n) mod n"
apply (subst mod_Suc [of m]) 
apply (subst mod_Suc [of "m mod n"], simp) 
done


subsection {* More Even/Odd Results *}
 
lemma even_mult_two_ex: "even(n) = (\<exists>m::nat. n = 2*m)" by presburger
lemma odd_Suc_mult_two_ex: "odd(n) = (\<exists>m. n = Suc (2*m))" by presburger
lemma even_add [simp]: "even(m + n::nat) = (even m = even n)"  by presburger

lemma odd_add [simp]: "odd(m + n::nat) = (odd m \<noteq> odd n)" by presburger

lemma div_Suc: "Suc a div c = a div c + Suc 0 div c +
    (a mod c + Suc 0 mod c) div c" 
  apply (subgoal_tac "Suc a = a + Suc 0")
  apply (erule ssubst)
  apply (rule div_add1_eq, simp)
  done

lemma lemma_even_div2 [simp]: "even (n::nat) ==> (n + 1) div 2 = n div 2" by presburger

lemma lemma_not_even_div2 [simp]: "~even n ==> (n + 1) div 2 = Suc (n div 2)"
by presburger

lemma even_num_iff: "0 < n ==> even n = (~ even(n - 1 :: nat))"  by presburger
lemma even_even_mod_4_iff: "even (n::nat) = even (n mod 4)" by presburger

lemma lemma_odd_mod_4_div_2: "n mod 4 = (3::nat) ==> odd((n - 1) div 2)" by presburger

lemma lemma_even_mod_4_div_2: "n mod 4 = (1::nat) ==> even ((n - 1) div 2)"
  by presburger

text {* Simplify, when the exponent is a numeral *}

lemmas power_0_left_number_of = power_0_left [of "number_of w", standard]
declare power_0_left_number_of [simp]

lemmas zero_le_power_eq_number_of [simp] =
    zero_le_power_eq [of _ "number_of w", standard]

lemmas zero_less_power_eq_number_of [simp] =
    zero_less_power_eq [of _ "number_of w", standard]

lemmas power_le_zero_eq_number_of [simp] =
    power_le_zero_eq [of _ "number_of w", standard]

lemmas power_less_zero_eq_number_of [simp] =
    power_less_zero_eq [of _ "number_of w", standard]

lemmas zero_less_power_nat_eq_number_of [simp] =
    zero_less_power_nat_eq [of _ "number_of w", standard]

lemmas power_eq_0_iff_number_of [simp] = power_eq_0_iff [of _ "number_of w", standard]

lemmas power_even_abs_number_of [simp] = power_even_abs [of "number_of w" _, standard]


subsection {* An Equivalence for @{term [source] "0 \<le> a^n"} *}

lemma even_power_le_0_imp_0:
    "a ^ (2*k) \<le> (0::'a::{ordered_idom,recpower}) ==> a=0"
  by (induct k) (auto simp add: zero_le_mult_iff mult_le_0_iff power_Suc)

lemma zero_le_power_iff[presburger]:
  "(0 \<le> a^n) = (0 \<le> (a::'a::{ordered_idom,recpower}) | even n)"
proof cases
  assume even: "even n"
  then obtain k where "n = 2*k"
    by (auto simp add: even_nat_equiv_def2 numeral_2_eq_2)
  thus ?thesis by (simp add: zero_le_even_power even)
next
  assume odd: "odd n"
  then obtain k where "n = Suc(2*k)"
    by (auto simp add: odd_nat_equiv_def2 numeral_2_eq_2)
  thus ?thesis
    by (auto simp add: power_Suc zero_le_mult_iff zero_le_even_power
             dest!: even_power_le_0_imp_0)
qed


subsection {* Miscellaneous *}

lemma [presburger]:"(x + 1) div 2 = x div 2 \<longleftrightarrow> even (x::int)" by presburger
lemma [presburger]: "(x + 1) div 2 = x div 2 + 1 \<longleftrightarrow> odd (x::int)" by presburger
lemma even_plus_one_div_two: "even (x::int) ==> (x + 1) div 2 = x div 2"  by presburger
lemma odd_plus_one_div_two: "odd (x::int) ==> (x + 1) div 2 = x div 2 + 1" by presburger

lemma [presburger]: "(Suc x) div Suc (Suc 0) = x div Suc (Suc 0) \<longleftrightarrow> even x" by presburger
lemma [presburger]: "(Suc x) div Suc (Suc 0) = x div Suc (Suc 0) \<longleftrightarrow> even x" by presburger
lemma even_nat_plus_one_div_two: "even (x::nat) ==>
    (Suc x) div Suc (Suc 0) = x div Suc (Suc 0)" by presburger

lemma odd_nat_plus_one_div_two: "odd (x::nat) ==>
    (Suc x) div Suc (Suc 0) = Suc (x div Suc (Suc 0))" by presburger

end
