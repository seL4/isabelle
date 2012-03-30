(*  Title:      HOL/Nat_Numeral.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Binary numerals for the natural numbers *}

theory Nat_Numeral
imports Int
begin

subsection{*Comparisons*}

text{*Simprules for comparisons where common factors can be cancelled.*}
lemmas zero_compare_simps =
    add_strict_increasing add_strict_increasing2 add_increasing
    zero_le_mult_iff zero_le_divide_iff 
    zero_less_mult_iff zero_less_divide_iff 
    mult_le_0_iff divide_le_0_iff 
    mult_less_0_iff divide_less_0_iff 
    zero_le_power2 power2_less_0

subsubsection{*Nat *}

lemma Suc_pred': "0 < n ==> n = Suc(n - 1)"
by simp

(*Expresses a natural number constant as the Suc of another one.
  NOT suitable for rewriting because n recurs on the right-hand side.*)
lemmas expand_Suc = Suc_pred' [of "numeral v", OF zero_less_numeral] for v

subsubsection{*Arith *}

(* These two can be useful when m = numeral... *)

lemma add_eq_if: "(m::nat) + n = (if m=0 then n else Suc ((m - 1) + n))"
  unfolding One_nat_def by (cases m) simp_all

lemma mult_eq_if: "(m::nat) * n = (if m=0 then 0 else n + ((m - 1) * n))"
  unfolding One_nat_def by (cases m) simp_all

lemma power_eq_if: "(p ^ m :: nat) = (if m=0 then 1 else p * (p ^ (m - 1)))"
  unfolding One_nat_def by (cases m) simp_all

 
subsection{*Literal arithmetic involving powers*}

text{*For arbitrary rings*}

lemma power_numeral_even:
  fixes z :: "'a::monoid_mult"
  shows "z ^ numeral (Num.Bit0 w) = (let w = z ^ (numeral w) in w * w)"
  unfolding numeral_Bit0 power_add Let_def ..

lemma power_numeral_odd:
  fixes z :: "'a::monoid_mult"
  shows "z ^ numeral (Num.Bit1 w) = (let w = z ^ (numeral w) in z * w * w)"
  unfolding numeral_Bit1 One_nat_def add_Suc_right add_0_right
  unfolding power_Suc power_add Let_def mult_assoc ..

lemmas zpower_numeral_even = power_numeral_even [where 'a=int]
lemmas zpower_numeral_odd = power_numeral_odd [where 'a=int]

lemma nat_numeral_Bit0:
  "numeral (Num.Bit0 w) = (let n::nat = numeral w in n + n)"
  unfolding numeral_Bit0 Let_def ..

lemma nat_numeral_Bit1:
  "numeral (Num.Bit1 w) = (let n = numeral w in Suc (n + n))"
  unfolding numeral_Bit1 Let_def by simp

lemmas eval_nat_numeral =
  nat_numeral_Bit0 nat_numeral_Bit1

lemmas nat_arith =
  diff_nat_numeral

lemmas semiring_norm =
  Let_def arith_simps nat_arith rel_simps
  if_False if_True
  add_0 add_Suc add_numeral_left
  add_neg_numeral_left mult_numeral_left
  numeral_1_eq_1 [symmetric] Suc_eq_plus1
  eq_numeral_iff_iszero not_iszero_Numeral1

lemma Let_Suc [simp]: "Let (Suc n) f == f (Suc n)"
  by (fact Let_def)


subsection{*Literal arithmetic and @{term of_nat}*}

lemma of_nat_double:
     "0 \<le> x ==> of_nat (nat (2 * x)) = of_nat (nat x) + of_nat (nat x)"
by (simp only: mult_2 nat_add_distrib of_nat_add) 


subsubsection{*For simplifying @{term "Suc m - K"} and  @{term "K - Suc m"}*}

text{*Where K above is a literal*}

lemma Suc_diff_eq_diff_pred: "0 < n ==> Suc m - n = m - (n - Numeral1)"
by (simp split: nat_diff_split)

text{*No longer required as a simprule because of the @{text inverse_fold}
   simproc*}
lemma Suc_diff_numeral: "Suc m - (numeral v) = m - (numeral v - 1)"
  by (subst expand_Suc, simp only: diff_Suc_Suc)

lemma diff_Suc_eq_diff_pred: "m - Suc n = (m - 1) - n"
by (simp split: nat_diff_split)


subsubsection{*Various Other Lemmas*}

text {*Evens and Odds, for Mutilated Chess Board*}

text{*Lemmas for specialist use, NOT as default simprules*}
lemma nat_mult_2: "2 * z = (z+z::nat)"
by (rule mult_2) (* FIXME: duplicate *)

lemma nat_mult_2_right: "z * 2 = (z+z::nat)"
by (rule mult_2_right) (* FIXME: duplicate *)

text{*Case analysis on @{term "n<2"}*}
lemma less_2_cases: "(n::nat) < 2 ==> n = 0 | n = Suc 0"
by (auto simp add: numeral_2_eq_2)

text{*Removal of Small Numerals: 0, 1 and (in additive positions) 2*}

lemma add_2_eq_Suc [simp]: "2 + n = Suc (Suc n)"
by simp

lemma add_2_eq_Suc' [simp]: "n + 2 = Suc (Suc n)"
by simp

text{*Can be used to eliminate long strings of Sucs, but not by default*}
lemma Suc3_eq_add_3: "Suc (Suc (Suc n)) = 3 + n"
by simp

text{*Legacy theorems*}

lemmas nat_1_add_1 = one_add_one [where 'a=nat]

end
