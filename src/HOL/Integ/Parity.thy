(*  Title:      Parity.thy
    Author:     Jeremy Avigad
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

    Last modified 2 March 2004
*)

header {* Parity: Even and Odd for ints and nats*}

theory Parity = Divides + IntDiv + NatSimprocs:

axclass even_odd < type

instance int :: even_odd ..
instance nat :: even_odd ..

consts
  even :: "'a::even_odd => bool"

syntax 
  odd :: "'a::even_odd => bool"

translations 
  "odd x" == "~even x" 

defs (overloaded)
  even_def: "even (x::int) == x mod 2 = 0"
  even_nat_def: "even (x::nat) == even (int x)"


subsection {* Casting a nat power to an integer *}

lemma zpow_int: "int (x^y) = (int x)^y"
  apply (induct_tac y)
  apply (simp, simp add: zmult_int [THEN sym])
  done

subsection {* Even and odd are mutually exclusive *}

lemma int_pos_lt_two_imp_zero_or_one: 
    "0 <= x ==> (x::int) < 2 ==> x = 0 | x = 1"
  by auto

lemma neq_one_mod_two [simp]: "((x::int) mod 2 ~= 0) = (x mod 2 = 1)"
  apply (subgoal_tac "x mod 2 = 0 | x mod 2 = 1", force)
  apply (rule int_pos_lt_two_imp_zero_or_one, auto)
  done

subsection {* Behavior under integer arithmetic operations *}

lemma even_times_anything: "even (x::int) ==> even (x * y)"
  by (simp add: even_def zmod_zmult1_eq')

lemma anything_times_even: "even (y::int) ==> even (x * y)"
  by (simp add: even_def zmod_zmult1_eq)

lemma odd_times_odd: "odd (x::int) ==> odd y ==> odd (x * y)"
  by (simp add: even_def zmod_zmult1_eq)

lemma even_product: "even((x::int) * y) = (even x | even y)"
  apply (auto simp add: even_times_anything anything_times_even) 
  apply (rule ccontr)
  apply (auto simp add: odd_times_odd)
  done

lemma even_plus_even: "even (x::int) ==> even y ==> even (x + y)"
  by (simp add: even_def zmod_zadd1_eq)

lemma even_plus_odd: "even (x::int) ==> odd y ==> odd (x + y)"
  by (simp add: even_def zmod_zadd1_eq)

lemma odd_plus_even: "odd (x::int) ==> even y ==> odd (x + y)"
  by (simp add: even_def zmod_zadd1_eq)

lemma odd_plus_odd: "odd (x::int) ==> odd y ==> even (x + y)"
  by (simp add: even_def zmod_zadd1_eq)

lemma even_sum: "even ((x::int) + y) = ((even x & even y) | (odd x & odd y))"
  apply (auto intro: even_plus_even odd_plus_odd)
  apply (rule ccontr, simp add: even_plus_odd)
  apply (rule ccontr, simp add: odd_plus_even)
  done

lemma even_neg: "even (-(x::int)) = even x"
  by (auto simp add: even_def zmod_zminus1_eq_if)

lemma even_difference: 
  "even ((x::int) - y) = ((even x & even y) | (odd x & odd y))"
  by (simp only: diff_minus even_sum even_neg)

lemma even_pow_gt_zero [rule_format]: 
    "even (x::int) ==> 0 < n --> even (x^n)"
  apply (induct_tac n)
  apply (auto simp add: even_product)
  done

lemma odd_pow: "odd x ==> odd((x::int)^n)"
  apply (induct_tac n)
  apply (simp add: even_def)
  apply (simp add: even_product)
  done

lemma even_power: "even ((x::int)^n) = (even x & 0 < n)"
  apply (auto simp add: even_pow_gt_zero) 
  apply (erule contrapos_pp, erule odd_pow)
  apply (erule contrapos_pp, simp add: even_def)
  done

lemma even_zero: "even (0::int)"
  by (simp add: even_def)

lemma odd_one: "odd (1::int)"
  by (simp add: even_def)

lemmas even_odd_simps [simp] = even_def[of "number_of v",standard] even_zero 
  odd_one even_product even_sum even_neg even_difference even_power


subsection {* Equivalent definitions *}

lemma two_times_even_div_two: "even (x::int) ==> 2 * (x div 2) = x" 
  by (auto simp add: even_def)

lemma two_times_odd_div_two_plus_one: "odd (x::int) ==> 
    2 * (x div 2) + 1 = x"
  apply (insert zmod_zdiv_equality [of x 2, THEN sym])
  by (simp add: even_def)

lemma even_equiv_def: "even (x::int) = (EX y. x = 2 * y)"
  apply auto
  apply (rule exI)
  by (erule two_times_even_div_two [THEN sym])

lemma odd_equiv_def: "odd (x::int) = (EX y. x = 2 * y + 1)"
  apply auto
  apply (rule exI)
  by (erule two_times_odd_div_two_plus_one [THEN sym])


subsection {* even and odd for nats *}

lemma pos_int_even_equiv_nat_even: "0 \<le> x ==> even x = even (nat x)"
  by (simp add: even_nat_def)

lemma even_nat_product: "even((x::nat) * y) = (even x | even y)"
  by (simp add: even_nat_def zmult_int [THEN sym])

lemma even_nat_sum: "even ((x::nat) + y) = 
    ((even x & even y) | (odd x & odd y))"
  by (unfold even_nat_def, simp)

lemma even_nat_difference: 
    "even ((x::nat) - y) = (x < y | (even x & even y) | (odd x & odd y))"
  apply (auto simp add: even_nat_def zdiff_int [THEN sym])
  apply (case_tac "x < y", auto simp add: zdiff_int [THEN sym])
  apply (case_tac "x < y", auto simp add: zdiff_int [THEN sym])
  done

lemma even_nat_suc: "even (Suc x) = odd x"
  by (simp add: even_nat_def)

lemma even_nat_power: "even ((x::nat)^y) = (even x & 0 < y)"
  by (simp add: even_nat_def zpow_int)

lemma even_nat_zero: "even (0::nat)"
  by (simp add: even_nat_def)

lemmas even_odd_nat_simps [simp] = even_nat_def[of "number_of v",standard] 
  even_nat_zero even_nat_suc even_nat_product even_nat_sum even_nat_power


subsection {* Equivalent definitions *}

lemma nat_lt_two_imp_zero_or_one: "(x::nat) < Suc (Suc 0) ==> 
    x = 0 | x = Suc 0"
  by auto

lemma even_nat_mod_two_eq_zero: "even (x::nat) ==> x mod (Suc (Suc 0)) = 0"
  apply (insert mod_div_equality [of x "Suc (Suc 0)", THEN sym])
  apply (drule subst, assumption)
  apply (subgoal_tac "x mod Suc (Suc 0) = 0 | x mod Suc (Suc 0) = Suc 0")
  apply force
  apply (subgoal_tac "0 < Suc (Suc 0)")
  apply (frule mod_less_divisor [of "Suc (Suc 0)" x])
  apply (erule nat_lt_two_imp_zero_or_one, auto)
  done

lemma odd_nat_mod_two_eq_one: "odd (x::nat) ==> x mod (Suc (Suc 0)) = Suc 0"
  apply (insert mod_div_equality [of x "Suc (Suc 0)", THEN sym])
  apply (drule subst, assumption)
  apply (subgoal_tac "x mod Suc (Suc 0) = 0 | x mod Suc (Suc 0) = Suc 0")
  apply force 
  apply (subgoal_tac "0 < Suc (Suc 0)")
  apply (frule mod_less_divisor [of "Suc (Suc 0)" x])
  apply (erule nat_lt_two_imp_zero_or_one, auto)
  done

lemma even_nat_equiv_def: "even (x::nat) = (x mod Suc (Suc 0) = 0)" 
  apply (rule iffI)
  apply (erule even_nat_mod_two_eq_zero)
  apply (insert odd_nat_mod_two_eq_one [of x], auto)
  done

lemma odd_nat_equiv_def: "odd (x::nat) = (x mod Suc (Suc 0) = Suc 0)"
  apply (auto simp add: even_nat_equiv_def)
  apply (subgoal_tac "x mod (Suc (Suc 0)) < Suc (Suc 0)")
  apply (frule nat_lt_two_imp_zero_or_one, auto)
  done

lemma even_nat_div_two_times_two: "even (x::nat) ==> 
    Suc (Suc 0) * (x div Suc (Suc 0)) = x"
  apply (insert mod_div_equality [of x "Suc (Suc 0)", THEN sym])
  apply (drule even_nat_mod_two_eq_zero, simp)
  done

lemma odd_nat_div_two_times_two_plus_one: "odd (x::nat) ==> 
    Suc( Suc (Suc 0) * (x div Suc (Suc 0))) = x"  
  apply (insert mod_div_equality [of x "Suc (Suc 0)", THEN sym])
  apply (drule odd_nat_mod_two_eq_one, simp)
  done

lemma even_nat_equiv_def2: "even (x::nat) = (EX y. x = Suc (Suc 0) * y)"
  apply (rule iffI, rule exI)
  apply (erule even_nat_div_two_times_two [THEN sym], auto)
  done

lemma odd_nat_equiv_def2: "odd (x::nat) = (EX y. x = Suc(Suc (Suc 0) * y))"
  apply (rule iffI, rule exI)
  apply (erule odd_nat_div_two_times_two_plus_one [THEN sym], auto)
  done

subsection {* Powers of negative one *}

lemma neg_one_even_odd_power:
     "(even x --> (-1::'a::{number_ring,ringpower})^x = 1) & 
      (odd x --> (-1::'a)^x = -1)"
  apply (induct_tac x)
  apply (simp, simp add: power_Suc)
  done

lemma neg_one_even_power: "even x ==> (-1::'a::{number_ring,ringpower})^x = 1"
  by (rule neg_one_even_odd_power [THEN conjunct1, THEN mp], assumption)

lemma neg_one_odd_power: "odd x ==> (-1::'a::{number_ring,ringpower})^x = -1"
  by (rule neg_one_even_odd_power [THEN conjunct2, THEN mp], assumption)


subsection {* Miscellaneous *}

lemma even_plus_one_div_two: "even (x::int) ==> (x + 1) div 2 = x div 2"
  apply (subst zdiv_zadd1_eq)
  apply (simp add: even_def)
  done

lemma odd_plus_one_div_two: "odd (x::int) ==> (x + 1) div 2 = x div 2 + 1"
  apply (subst zdiv_zadd1_eq)
  apply (simp add: even_def)
  done

lemma div_Suc: "Suc a div c = a div c + Suc 0 div c + 
    (a mod c + Suc 0 mod c) div c"
  apply (subgoal_tac "Suc a = a + Suc 0")
  apply (erule ssubst)
  apply (rule div_add1_eq, simp)
  done

lemma even_nat_plus_one_div_two: "even (x::nat) ==> 
   (Suc x) div Suc (Suc 0) = x div Suc (Suc 0)"
  apply (subst div_Suc)
  apply (simp add: even_nat_equiv_def)
  done

lemma odd_nat_plus_one_div_two: "odd (x::nat) ==> 
    (Suc x) div Suc (Suc 0) = Suc (x div Suc (Suc 0))"
  apply (subst div_Suc)
  apply (simp add: odd_nat_equiv_def)
  done

end
