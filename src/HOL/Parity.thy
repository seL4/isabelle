(*  Title:      HOL/Parity.thy
    Author:     Jeremy Avigad
    Author:     Jacques D. Fleuriot
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

lemma transfer_int_nat_relations:
  "even (int x) \<longleftrightarrow> even x"
  by (simp add: even_nat_def)

declare transfer_morphism_int_nat[transfer add return:
  transfer_int_nat_relations
]

lemma even_zero_int[simp]: "even (0::int)" by presburger

lemma odd_one_int[simp]: "odd (1::int)" by presburger

lemma even_zero_nat[simp]: "even (0::nat)" by presburger

lemma odd_1_nat [simp]: "odd (1::nat)" by presburger

lemma even_numeral_int [simp]: "even (numeral (Num.Bit0 k) :: int)"
  unfolding even_def by simp

lemma odd_numeral_int [simp]: "odd (numeral (Num.Bit1 k) :: int)"
  unfolding even_def by simp

(* TODO: proper simp rules for Num.Bit0, Num.Bit1 *)
declare even_def[of "neg_numeral v", simp] for v

lemma even_numeral_nat [simp]: "even (numeral (Num.Bit0 k) :: nat)"
  unfolding even_nat_def by simp

lemma odd_numeral_nat [simp]: "odd (numeral (Num.Bit1 k) :: nat)"
  unfolding even_nat_def by simp

subsection {* Even and odd are mutually exclusive *}

lemma int_pos_lt_two_imp_zero_or_one:
    "0 <= x ==> (x::int) < 2 ==> x = 0 | x = 1"
  by presburger

lemma neq_one_mod_two [simp, presburger]: 
  "((x::int) mod 2 ~= 0) = (x mod 2 = 1)" by presburger


subsection {* Behavior under integer arithmetic operations *}
declare dvd_def[algebra]
lemma nat_even_iff_2_dvd[algebra]: "even (x::nat) \<longleftrightarrow> 2 dvd x"
  by presburger
lemma int_even_iff_2_dvd[algebra]: "even (x::int) \<longleftrightarrow> 2 dvd x"
  by presburger

lemma even_times_anything: "even (x::int) ==> even (x * y)"
  by algebra

lemma anything_times_even: "even (y::int) ==> even (x * y)" by algebra

lemma odd_times_odd: "odd (x::int) ==> odd y ==> odd (x * y)" 
  by (simp add: even_def mod_mult_right_eq)

lemma even_product[simp,presburger]: "even((x::int) * y) = (even x | even y)"
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

lemma even_sum[simp,presburger]:
  "even ((x::int) + y) = ((even x & even y) | (odd x & odd y))"
by presburger

lemma even_neg[simp,presburger,algebra]: "even (-(x::int)) = even x"
by presburger

lemma even_difference[simp]:
    "even ((x::int) - y) = ((even x & even y) | (odd x & odd y))" by presburger

lemma even_power[simp,presburger]: "even ((x::int)^n) = (even x & n \<noteq> 0)"
by (induct n) auto

lemma odd_pow: "odd x ==> odd((x::int)^n)" by simp


subsection {* Equivalent definitions *}

lemma two_times_even_div_two: "even (x::int) ==> 2 * (x div 2) = x" 
by presburger

lemma two_times_odd_div_two_plus_one:
  "odd (x::int) ==> 2 * (x div 2) + 1 = x"
by presburger

lemma even_equiv_def: "even (x::int) = (EX y. x = 2 * y)" by presburger

lemma odd_equiv_def: "odd (x::int) = (EX y. x = 2 * y + 1)" by presburger

subsection {* even and odd for nats *}

lemma pos_int_even_equiv_nat_even: "0 \<le> x ==> even x = even (nat x)"
by (simp add: even_nat_def)

lemma even_product_nat[simp,presburger,algebra]:
  "even((x::nat) * y) = (even x | even y)"
by (simp add: even_nat_def int_mult)

lemma even_sum_nat[simp,presburger,algebra]:
  "even ((x::nat) + y) = ((even x & even y) | (odd x & odd y))"
by presburger

lemma even_difference_nat[simp,presburger,algebra]:
  "even ((x::nat) - y) = (x < y | (even x & even y) | (odd x & odd y))"
by presburger

lemma even_Suc[simp,presburger,algebra]: "even (Suc x) = odd x"
by presburger

lemma even_power_nat[simp,presburger,algebra]:
  "even ((x::nat)^y) = (even x & 0 < y)"
by (simp add: even_nat_def int_power)


subsection {* Equivalent definitions *}

lemma nat_lt_two_imp_zero_or_one:
  "(x::nat) < Suc (Suc 0) ==> x = 0 | x = Suc 0"
by presburger

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
     "(even x --> (- 1::'a::{comm_ring_1})^x = 1) &
      (odd x --> (- 1::'a)^x = - 1)"
  apply (induct x)
  apply (rule conjI)
  apply simp
  apply (insert even_zero_nat, blast)
  apply simp
  done

lemma minus_one_even_power [simp]:
    "even x ==> (- 1::'a::{comm_ring_1})^x = 1"
  using minus_one_even_odd_power by blast

lemma minus_one_odd_power [simp]:
    "odd x ==> (- 1::'a::{comm_ring_1})^x = - 1"
  using minus_one_even_odd_power by blast

lemma neg_one_even_odd_power:
     "(even x --> (-1::'a::{comm_ring_1})^x = 1) &
      (odd x --> (-1::'a)^x = -1)"
  apply (induct x)
  apply (simp, simp)
  done

lemma neg_one_even_power [simp]:
    "even x ==> (-1::'a::{comm_ring_1})^x = 1"
  using neg_one_even_odd_power by blast

lemma neg_one_odd_power [simp]:
    "odd x ==> (-1::'a::{comm_ring_1})^x = -1"
  using neg_one_even_odd_power by blast

lemma neg_power_if:
     "(-x::'a::{comm_ring_1}) ^ n =
      (if even n then (x ^ n) else -(x ^ n))"
  apply (induct n)
  apply simp_all
  done

lemma zero_le_even_power: "even n ==>
    0 <= (x::'a::{linordered_ring,monoid_mult}) ^ n"
  apply (simp add: even_nat_equiv_def2)
  apply (erule exE)
  apply (erule ssubst)
  apply (subst power_add)
  apply (rule zero_le_square)
  done

lemma zero_le_odd_power: "odd n ==>
    (0 <= (x::'a::{linordered_idom}) ^ n) = (0 <= x)"
apply (auto simp: odd_nat_equiv_def2 power_add zero_le_mult_iff)
apply (metis field_power_not_zero divisors_zero order_antisym_conv zero_le_square)
done

lemma zero_le_power_eq[presburger]: "(0 <= (x::'a::{linordered_idom}) ^ n) =
    (even n | (odd n & 0 <= x))"
  apply auto
  apply (subst zero_le_odd_power [symmetric])
  apply assumption+
  apply (erule zero_le_even_power)
  done

lemma zero_less_power_eq[presburger]: "(0 < (x::'a::{linordered_idom}) ^ n) =
    (n = 0 | (even n & x ~= 0) | (odd n & 0 < x))"

  unfolding order_less_le zero_le_power_eq by auto

lemma power_less_zero_eq[presburger]: "((x::'a::{linordered_idom}) ^ n < 0) =
    (odd n & x < 0)"
  apply (subst linorder_not_le [symmetric])+
  apply (subst zero_le_power_eq)
  apply auto
  done

lemma power_le_zero_eq[presburger]: "((x::'a::{linordered_idom}) ^ n <= 0) =
    (n ~= 0 & ((odd n & x <= 0) | (even n & x = 0)))"
  apply (subst linorder_not_less [symmetric])+
  apply (subst zero_less_power_eq)
  apply auto
  done

lemma power_even_abs: "even n ==>
    (abs (x::'a::{linordered_idom}))^n = x^n"
  apply (subst power_abs [symmetric])
  apply (simp add: zero_le_even_power)
  done

lemma zero_less_power_nat_eq[presburger]: "(0 < (x::nat) ^ n) = (n = 0 | 0 < x)"
  by (induct n) auto

lemma power_minus_even [simp]: "even n ==>
    (- x)^n = (x^n::'a::{comm_ring_1})"
  apply (subst power_minus)
  apply simp
  done

lemma power_minus_odd [simp]: "odd n ==>
    (- x)^n = - (x^n::'a::{comm_ring_1})"
  apply (subst power_minus)
  apply simp
  done

lemma power_mono_even: fixes x y :: "'a :: {linordered_idom}"
  assumes "even n" and "\<bar>x\<bar> \<le> \<bar>y\<bar>"
  shows "x^n \<le> y^n"
proof -
  have "0 \<le> \<bar>x\<bar>" by auto
  with `\<bar>x\<bar> \<le> \<bar>y\<bar>`
  have "\<bar>x\<bar>^n \<le> \<bar>y\<bar>^n" by (rule power_mono)
  thus ?thesis unfolding power_even_abs[OF `even n`] .
qed

lemma odd_pos: "odd (n::nat) \<Longrightarrow> 0 < n" by presburger

lemma power_mono_odd: fixes x y :: "'a :: {linordered_idom}"
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

lemma power_0_left_numeral [simp]:
  "0 ^ numeral w = (0::'a::{power,semiring_0})"
by (simp add: power_0_left)

lemmas zero_le_power_eq_numeral [simp] =
    zero_le_power_eq [of _ "numeral w"] for w

lemmas zero_less_power_eq_numeral [simp] =
    zero_less_power_eq [of _ "numeral w"] for w

lemmas power_le_zero_eq_numeral [simp] =
    power_le_zero_eq [of _ "numeral w"] for w

lemmas power_less_zero_eq_numeral [simp] =
    power_less_zero_eq [of _ "numeral w"] for w

lemmas zero_less_power_nat_eq_numeral [simp] =
    zero_less_power_nat_eq [of _ "numeral w"] for w

lemmas power_eq_0_iff_numeral [simp] = power_eq_0_iff [of _ "numeral w"] for w

lemmas power_even_abs_numeral [simp] = power_even_abs [of "numeral w" _] for w


subsection {* An Equivalence for @{term [source] "0 \<le> a^n"} *}

lemma even_power_le_0_imp_0:
    "a ^ (2*k) \<le> (0::'a::{linordered_idom}) ==> a=0"
  by (induct k) (auto simp add: zero_le_mult_iff mult_le_0_iff)

lemma zero_le_power_iff[presburger]:
  "(0 \<le> a^n) = (0 \<le> (a::'a::{linordered_idom}) | even n)"
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
    by (auto simp add: zero_le_mult_iff zero_le_even_power
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
