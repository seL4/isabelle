(*  Title       : HOL/Real/RealPow.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural powers theory

*)

theory RealPow = RealAbs:

(*belongs to theory RealAbs*)
lemmas [arith_split] = abs_split

instance real :: power ..

primrec (realpow)
     realpow_0:   "r ^ 0       = 1"
     realpow_Suc: "r ^ (Suc n) = (r::real) * (r ^ n)"


(*FIXME: most of the theorems for Suc (Suc 0) are redundant!
*)

lemma realpow_zero: "(0::real) ^ (Suc n) = 0"
apply auto
done
declare realpow_zero [simp]

lemma realpow_not_zero [rule_format (no_asm)]: "r \<noteq> (0::real) --> r ^ n \<noteq> 0"
apply (induct_tac "n")
apply auto
done

lemma realpow_zero_zero: "r ^ n = (0::real) ==> r = 0"
apply (rule ccontr)
apply (auto dest: realpow_not_zero)
done

lemma realpow_inverse: "inverse ((r::real) ^ n) = (inverse r) ^ n"
apply (induct_tac "n")
apply (auto simp add: real_inverse_distrib)
done

lemma realpow_abs: "abs(r ^ n) = abs(r::real) ^ n"
apply (induct_tac "n")
apply (auto simp add: abs_mult)
done

lemma realpow_add: "(r::real) ^ (n + m) = (r ^ n) * (r ^ m)"
apply (induct_tac "n")
apply (auto simp add: real_mult_ac)
done

lemma realpow_one: "(r::real) ^ 1 = r"
apply (simp (no_asm))
done
declare realpow_one [simp]

lemma realpow_two: "(r::real)^ (Suc (Suc 0)) = r * r"
apply (simp (no_asm))
done

lemma realpow_gt_zero [rule_format (no_asm)]: "(0::real) < r --> 0 < r ^ n"
apply (induct_tac "n")
apply (auto intro: real_mult_order simp add: real_zero_less_one)
done

lemma realpow_ge_zero [rule_format (no_asm)]: "(0::real) \<le> r --> 0 \<le> r ^ n"
apply (induct_tac "n")
apply (auto simp add: real_0_le_mult_iff)
done

lemma realpow_le [rule_format (no_asm)]: "(0::real) \<le> x & x \<le> y --> x ^ n \<le> y ^ n"
apply (induct_tac "n")
apply (auto intro!: real_mult_le_mono)
apply (simp (no_asm_simp) add: realpow_ge_zero)
done

lemma realpow_0_left [rule_format, simp]:
     "0 < n --> 0 ^ n = (0::real)"
apply (induct_tac "n")
apply (auto ); 
done

lemma realpow_less' [rule_format]:
     "[|(0::real) \<le> x; x < y |] ==> 0 < n --> x ^ n < y ^ n"
apply (induct n) 
apply (auto simp add: real_mult_less_mono' realpow_ge_zero); 
done

text{*Legacy: weaker version of the theorem above*}
lemma realpow_less [rule_format]:
     "[|(0::real) < x; x < y; 0 < n|] ==> x ^ n < y ^ n"
apply (rule realpow_less') 
apply (auto ); 
done

lemma realpow_eq_one: "1 ^ n = (1::real)"
apply (induct_tac "n")
apply auto
done
declare realpow_eq_one [simp]

lemma abs_realpow_minus_one: "abs((-1) ^ n) = (1::real)"
apply (induct_tac "n")
apply (auto simp add: abs_mult)
done
declare abs_realpow_minus_one [simp]

lemma realpow_mult: "((r::real) * s) ^ n = (r ^ n) * (s ^ n)"
apply (induct_tac "n")
apply (auto simp add: real_mult_ac)
done

lemma realpow_two_le: "(0::real) \<le> r^ Suc (Suc 0)"
apply (simp (no_asm) add: real_le_square)
done
declare realpow_two_le [simp]

lemma abs_realpow_two: "abs((x::real)^Suc (Suc 0)) = x^Suc (Suc 0)"
apply (simp (no_asm) add: abs_eqI1 real_le_square)
done
declare abs_realpow_two [simp]

lemma realpow_two_abs: "abs(x::real)^Suc (Suc 0) = x^Suc (Suc 0)"
apply (simp (no_asm) add: realpow_abs [symmetric] abs_eqI1 del: realpow_Suc)
done
declare realpow_two_abs [simp]

lemma realpow_two_gt_one: "(1::real) < r ==> 1 < r^ (Suc (Suc 0))"
apply auto
apply (cut_tac real_zero_less_one)
apply (frule_tac x = "0" in order_less_trans)
apply assumption
apply (drule_tac  z = "r" and x = "1" in real_mult_less_mono1)
apply (auto intro: order_less_trans)
done

lemma realpow_ge_one [rule_format (no_asm)]: "(1::real) < r --> 1 \<le> r ^ n"
apply (induct_tac "n")
apply auto
apply (subgoal_tac "1*1 \<le> r * r^n")
apply (rule_tac [2] real_mult_le_mono)
apply auto
done

lemma realpow_ge_one2: "(1::real) \<le> r ==> 1 \<le> r ^ n"
apply (drule order_le_imp_less_or_eq)
apply (auto dest: realpow_ge_one)
done

lemma two_realpow_ge_one: "(1::real) \<le> 2 ^ n"
apply (rule_tac y = "1 ^ n" in order_trans)
apply (rule_tac [2] realpow_le)
apply (auto intro: order_less_imp_le)
done

lemma two_realpow_gt: "real (n::nat) < 2 ^ n"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_Suc)
apply (subst real_mult_2)
apply (rule real_add_less_le_mono)
apply (auto simp add: two_realpow_ge_one)
done
declare two_realpow_gt [simp] two_realpow_ge_one [simp]

lemma realpow_minus_one: "(-1) ^ (2*n) = (1::real)"
apply (induct_tac "n")
apply auto
done
declare realpow_minus_one [simp]

lemma realpow_minus_one_odd: "(-1) ^ Suc (2*n) = -(1::real)"
apply auto
done
declare realpow_minus_one_odd [simp]

lemma realpow_minus_one_even: "(-1) ^ Suc (Suc (2*n)) = (1::real)"
apply auto
done
declare realpow_minus_one_even [simp]

lemma realpow_Suc_less [rule_format (no_asm)]: "(0::real) < r & r < (1::real) --> r ^ Suc n < r ^ n"
apply (induct_tac "n")
apply auto
done

lemma realpow_Suc_le [rule_format (no_asm)]: "0 \<le> r & r < (1::real) --> r ^ Suc n \<le> r ^ n"
apply (induct_tac "n")
apply (auto intro: order_less_imp_le dest!: order_le_imp_less_or_eq)
done

lemma realpow_zero_le: "(0::real) \<le> 0 ^ n"
apply (case_tac "n")
apply auto
done
declare realpow_zero_le [simp]

lemma realpow_Suc_le2 [rule_format (no_asm)]: "0 < r & r < (1::real) --> r ^ Suc n \<le> r ^ n"
apply (blast intro!: order_less_imp_le realpow_Suc_less)
done

lemma realpow_Suc_le3: "[| 0 \<le> r; r < (1::real) |] ==> r ^ Suc n \<le> r ^ n"
apply (erule order_le_imp_less_or_eq [THEN disjE])
apply (rule realpow_Suc_le2)
apply auto
done

lemma realpow_less_le [rule_format (no_asm)]: "0 \<le> r & r < (1::real) & n < N --> r ^ N \<le> r ^ n"
apply (induct_tac "N")
apply (simp_all (no_asm_simp))
apply clarify
apply (subgoal_tac "r * r ^ na \<le> 1 * r ^ n")
apply simp
apply (rule real_mult_le_mono)
apply (auto simp add: realpow_ge_zero less_Suc_eq)
done

lemma realpow_le_le: "[| 0 \<le> r; r < (1::real); n \<le> N |] ==> r ^ N \<le> r ^ n"
apply (drule_tac n = "N" in le_imp_less_or_eq)
apply (auto intro: realpow_less_le)
done

lemma realpow_Suc_le_self: "[| 0 < r; r < (1::real) |] ==> r ^ Suc n \<le> r"
apply (drule_tac n = "1" and N = "Suc n" in order_less_imp_le [THEN realpow_le_le])
apply auto
done

lemma realpow_Suc_less_one: "[| 0 < r; r < (1::real) |] ==> r ^ Suc n < 1"
apply (blast intro: realpow_Suc_le_self order_le_less_trans)
done

lemma realpow_le_Suc [rule_format (no_asm)]: "(1::real) \<le> r --> r ^ n \<le> r ^ Suc n"
apply (induct_tac "n")
apply auto
done

lemma realpow_less_Suc [rule_format (no_asm)]: "(1::real) < r --> r ^ n < r ^ Suc n"
apply (induct_tac "n")
apply auto
done

lemma realpow_le_Suc2 [rule_format (no_asm)]: "(1::real) < r --> r ^ n \<le> r ^ Suc n"
apply (blast intro!: order_less_imp_le realpow_less_Suc)
done

lemma realpow_gt_ge [rule_format (no_asm)]: "(1::real) < r & n < N --> r ^ n \<le> r ^ N"
apply (induct_tac "N")
apply auto
apply (frule_tac [!] n = "na" in realpow_ge_one)
apply (drule_tac [!] real_mult_self_le)
apply assumption
prefer 2 apply (assumption)
apply (auto intro: order_trans simp add: less_Suc_eq)
done

lemma realpow_gt_ge2 [rule_format (no_asm)]: "(1::real) \<le> r & n < N --> r ^ n \<le> r ^ N"
apply (induct_tac "N")
apply auto
apply (frule_tac [!] n = "na" in realpow_ge_one2)
apply (drule_tac [!] real_mult_self_le2)
apply assumption
prefer 2 apply (assumption)
apply (auto intro: order_trans simp add: less_Suc_eq)
done

lemma realpow_ge_ge: "[| (1::real) < r; n \<le> N |] ==> r ^ n \<le> r ^ N"
apply (drule_tac n = "N" in le_imp_less_or_eq)
apply (auto intro: realpow_gt_ge)
done

lemma realpow_ge_ge2: "[| (1::real) \<le> r; n \<le> N |] ==> r ^ n \<le> r ^ N"
apply (drule_tac n = "N" in le_imp_less_or_eq)
apply (auto intro: realpow_gt_ge2)
done

lemma realpow_Suc_ge_self [rule_format (no_asm)]: "(1::real) < r ==> r \<le> r ^ Suc n"
apply (drule_tac n = "1" and N = "Suc n" in realpow_ge_ge)
apply auto
done

lemma realpow_Suc_ge_self2 [rule_format (no_asm)]: "(1::real) \<le> r ==> r \<le> r ^ Suc n"
apply (drule_tac n = "1" and N = "Suc n" in realpow_ge_ge2)
apply auto
done

lemma realpow_ge_self: "[| (1::real) < r; 0 < n |] ==> r \<le> r ^ n"
apply (drule less_not_refl2 [THEN not0_implies_Suc])
apply (auto intro!: realpow_Suc_ge_self)
done

lemma realpow_ge_self2: "[| (1::real) \<le> r; 0 < n |] ==> r \<le> r ^ n"
apply (drule less_not_refl2 [THEN not0_implies_Suc])
apply (auto intro!: realpow_Suc_ge_self2)
done

lemma realpow_minus_mult [rule_format (no_asm)]: "0 < n --> (x::real) ^ (n - 1) * x = x ^ n"
apply (induct_tac "n")
apply (auto simp add: real_mult_commute)
done
declare realpow_minus_mult [simp]

lemma realpow_two_mult_inverse: "r \<noteq> 0 ==> r * inverse r ^Suc (Suc 0) = inverse (r::real)"
apply (simp (no_asm_simp) add: realpow_two real_mult_assoc [symmetric])
done
declare realpow_two_mult_inverse [simp]

(* 05/00 *)
lemma realpow_two_minus: "(-x)^Suc (Suc 0) = (x::real)^Suc (Suc 0)"
apply (simp (no_asm))
done
declare realpow_two_minus [simp]

lemma realpow_two_diff: "(x::real)^Suc (Suc 0) - y^Suc (Suc 0) = (x - y) * (x + y)"
apply (unfold real_diff_def)
apply (simp add: real_add_mult_distrib2 real_add_mult_distrib real_mult_ac)
done

lemma realpow_two_disj: "((x::real)^Suc (Suc 0) = y^Suc (Suc 0)) = (x = y | x = -y)"
apply (cut_tac x = "x" and y = "y" in realpow_two_diff)
apply (auto simp del: realpow_Suc)
done

(* used in Transc *)
lemma realpow_diff: "[|(x::real) \<noteq> 0; m \<le> n |] ==> x ^ (n - m) = x ^ n * inverse (x ^ m)"
apply (auto simp add: le_eq_less_or_eq less_iff_Suc_add realpow_add realpow_not_zero real_mult_ac)
done

lemma realpow_real_of_nat: "real (m::nat) ^ n = real (m ^ n)"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_one real_of_nat_mult)
done

lemma realpow_real_of_nat_two_pos: "0 < real (Suc (Suc 0) ^ n)"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_mult real_0_less_mult_iff)
done
declare realpow_real_of_nat_two_pos [simp] 

lemma realpow_increasing:
  assumes xnonneg: "(0::real) \<le> x"
      and ynonneg: "0 \<le> y"
      and le: "x ^ Suc n \<le> y ^ Suc n"
  shows "x \<le> y"
 proof (rule ccontr)
   assume "~ x \<le> y"
   then have "y<x" by simp
   then have "y ^ Suc n < x ^ Suc n"
     by (simp only: prems realpow_less') 
   from le and this show "False"
     by simp
 qed
  
lemma realpow_Suc_cancel_eq: "[| (0::real) \<le> x; 0 \<le> y; x ^ Suc n = y ^ Suc n |] ==> x = y"
apply (blast intro: realpow_increasing order_antisym order_eq_refl sym)
done


(*** Logical equivalences for inequalities ***)

lemma realpow_eq_0_iff: "(x^n = 0) = (x = (0::real) & 0<n)"
apply (induct_tac "n")
apply auto
done
declare realpow_eq_0_iff [simp]

lemma zero_less_realpow_abs_iff: "(0 < (abs x)^n) = (x \<noteq> (0::real) | n=0)"
apply (induct_tac "n")
apply (auto simp add: real_0_less_mult_iff)
done
declare zero_less_realpow_abs_iff [simp]

lemma zero_le_realpow_abs: "(0::real) \<le> (abs x)^n"
apply (induct_tac "n")
apply (auto simp add: real_0_le_mult_iff)
done
declare zero_le_realpow_abs [simp]


(*** Literal arithmetic involving powers, type real ***)

lemma real_of_int_power: "real (x::int) ^ n = real (x ^ n)"
apply (induct_tac "n")
apply (simp_all (no_asm_simp) add: nat_mult_distrib)
done
declare real_of_int_power [symmetric, simp]

lemma power_real_number_of: "(number_of v :: real) ^ n = real ((number_of v :: int) ^ n)"
apply (simp only: real_number_of_def real_of_int_power)
done

declare power_real_number_of [of _ "number_of w", standard, simp]


lemma real_power_two: "(r::real)\<twosuperior> = r * r"
  by (simp add: numeral_2_eq_2)

lemma real_sqr_ge_zero [iff]: "0 \<le> (r::real)\<twosuperior>"
  by (simp add: real_power_two)

lemma real_sqr_gt_zero: "(r::real) \<noteq> 0 ==> 0 < r\<twosuperior>"
proof -
  assume "r \<noteq> 0"
  hence "0 \<noteq> r\<twosuperior>" by simp
  also have "0 \<le> r\<twosuperior>" by (simp add: real_sqr_ge_zero)
  finally show ?thesis .
qed

lemma real_sqr_not_zero: "r \<noteq> 0 ==> (r::real)\<twosuperior> \<noteq> 0"
  by simp


ML
{*
val realpow_0 = thm "realpow_0";
val realpow_Suc = thm "realpow_Suc";

val realpow_zero = thm "realpow_zero";
val realpow_not_zero = thm "realpow_not_zero";
val realpow_zero_zero = thm "realpow_zero_zero";
val realpow_inverse = thm "realpow_inverse";
val realpow_abs = thm "realpow_abs";
val realpow_add = thm "realpow_add";
val realpow_one = thm "realpow_one";
val realpow_two = thm "realpow_two";
val realpow_gt_zero = thm "realpow_gt_zero";
val realpow_ge_zero = thm "realpow_ge_zero";
val realpow_le = thm "realpow_le";
val realpow_0_left = thm "realpow_0_left";
val realpow_less = thm "realpow_less";
val realpow_eq_one = thm "realpow_eq_one";
val abs_realpow_minus_one = thm "abs_realpow_minus_one";
val realpow_mult = thm "realpow_mult";
val realpow_two_le = thm "realpow_two_le";
val abs_realpow_two = thm "abs_realpow_two";
val realpow_two_abs = thm "realpow_two_abs";
val realpow_two_gt_one = thm "realpow_two_gt_one";
val realpow_ge_one = thm "realpow_ge_one";
val realpow_ge_one2 = thm "realpow_ge_one2";
val two_realpow_ge_one = thm "two_realpow_ge_one";
val two_realpow_gt = thm "two_realpow_gt";
val realpow_minus_one = thm "realpow_minus_one";
val realpow_minus_one_odd = thm "realpow_minus_one_odd";
val realpow_minus_one_even = thm "realpow_minus_one_even";
val realpow_Suc_less = thm "realpow_Suc_less";
val realpow_Suc_le = thm "realpow_Suc_le";
val realpow_zero_le = thm "realpow_zero_le";
val realpow_Suc_le2 = thm "realpow_Suc_le2";
val realpow_Suc_le3 = thm "realpow_Suc_le3";
val realpow_less_le = thm "realpow_less_le";
val realpow_le_le = thm "realpow_le_le";
val realpow_Suc_le_self = thm "realpow_Suc_le_self";
val realpow_Suc_less_one = thm "realpow_Suc_less_one";
val realpow_le_Suc = thm "realpow_le_Suc";
val realpow_less_Suc = thm "realpow_less_Suc";
val realpow_le_Suc2 = thm "realpow_le_Suc2";
val realpow_gt_ge = thm "realpow_gt_ge";
val realpow_gt_ge2 = thm "realpow_gt_ge2";
val realpow_ge_ge = thm "realpow_ge_ge";
val realpow_ge_ge2 = thm "realpow_ge_ge2";
val realpow_Suc_ge_self = thm "realpow_Suc_ge_self";
val realpow_Suc_ge_self2 = thm "realpow_Suc_ge_self2";
val realpow_ge_self = thm "realpow_ge_self";
val realpow_ge_self2 = thm "realpow_ge_self2";
val realpow_minus_mult = thm "realpow_minus_mult";
val realpow_two_mult_inverse = thm "realpow_two_mult_inverse";
val realpow_two_minus = thm "realpow_two_minus";
val realpow_two_diff = thm "realpow_two_diff";
val realpow_two_disj = thm "realpow_two_disj";
val realpow_diff = thm "realpow_diff";
val realpow_real_of_nat = thm "realpow_real_of_nat";
val realpow_real_of_nat_two_pos = thm "realpow_real_of_nat_two_pos";
val realpow_increasing = thm "realpow_increasing";
val realpow_Suc_cancel_eq = thm "realpow_Suc_cancel_eq";
val realpow_eq_0_iff = thm "realpow_eq_0_iff";
val zero_less_realpow_abs_iff = thm "zero_less_realpow_abs_iff";
val zero_le_realpow_abs = thm "zero_le_realpow_abs";
val real_of_int_power = thm "real_of_int_power";
val power_real_number_of = thm "power_real_number_of";
val real_power_two = thm "real_power_two";
val real_sqr_ge_zero = thm "real_sqr_ge_zero";
val real_sqr_gt_zero = thm "real_sqr_gt_zero";
val real_sqr_not_zero = thm "real_sqr_not_zero";
*}


end
