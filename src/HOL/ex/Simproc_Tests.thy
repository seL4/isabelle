(*  Title:      HOL/ex/Simproc_Tests.thy
    Author:     Brian Huffman
*)

header {* Testing of arithmetic simprocs *}

theory Simproc_Tests
imports Rat
begin

text {*
  This theory tests the various simprocs defined in
  @{file "~~/src/HOL/Numeral_Simprocs.thy"}. Many of the tests
  are derived from commented-out code originally found in
  @{file "~~/src/HOL/Tools/numeral_simprocs.ML"}.
*}

subsection {* ML bindings *}

ML {*
  val semiring_assoc_fold = Numeral_Simprocs.assoc_fold_simproc
  val int_combine_numerals = Numeral_Simprocs.combine_numerals
  val field_combine_numerals = Numeral_Simprocs.field_combine_numerals
  val [inteq_cancel_numerals, intless_cancel_numerals, intle_cancel_numerals]
    = Numeral_Simprocs.cancel_numerals
  val [ring_eq_cancel_factor, linordered_ring_le_cancel_factor,
      linordered_ring_less_cancel_factor, int_div_cancel_factor,
      int_mod_cancel_factor, dvd_cancel_factor, divide_cancel_factor]
    = Numeral_Simprocs.cancel_factors
  val [ring_eq_cancel_numeral_factor, ring_less_cancel_numeral_factor,
      ring_le_cancel_numeral_factor, int_div_cancel_numeral_factors,
      divide_cancel_numeral_factor]
    = Numeral_Simprocs.cancel_numeral_factors
  val field_combine_numerals = Numeral_Simprocs.field_combine_numerals
  val [field_eq_cancel_numeral_factor, field_cancel_numeral_factor]
    = Numeral_Simprocs.field_cancel_numeral_factors

  fun test ps = CHANGED (asm_simp_tac (HOL_basic_ss addsimprocs ps) 1)
*}


subsection {* @{text int_combine_numerals} *}

lemma assumes "10 + (2 * l + oo) = uu"
  shows "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = (uu::int)"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "-3 + (i + (j + k)) = y"
  shows "(i + j + 12 + (k::int)) - 15 = y"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "7 + (i + (j + k)) = y"
  shows "(i + j + 12 + (k::int)) - 5 = y"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "-4 * (u * v) + (2 * x + y) = w"
  shows "(2*x - (u*v) + y) - v*3*u = (w::int)"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "Numeral0 * (u*v) + (2 * x * u * v + y) = w"
  shows "(2*x*u*v + (u*v)*4 + y) - v*u*4 = (w::int)"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "3 * (u * v) + (2 * x * u * v + y) = w"
  shows "(2*x*u*v + (u*v)*4 + y) - v*u = (w::int)"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "-3 * (u * v) + (- (x * u * v) + - y) = w"
  shows "u*v - (x*u*v + (u*v)*4 + y) = (w::int)"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "Numeral0 * b + (a + - c) = d"
  shows "a + -(b+c) + b = (d::int)"
apply (simp only: minus_add_distrib)
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "-2 * b + (a + - c) = d"
  shows "a + -(b+c) - b = (d::int)"
apply (simp only: minus_add_distrib)
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "-7 + (i + (j + (k + (- u + - y)))) = zz"
  shows "(i + j + -2 + (k::int)) - (u + 5 + y) = zz"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "-27 + (i + (j + k)) = y"
  shows "(i + j + -12 + (k::int)) - 15 = y"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "27 + (i + (j + k)) = y"
  shows "(i + j + 12 + (k::int)) - -15 = y"
by (tactic {* test [int_combine_numerals] *}) fact

lemma assumes "3 + (i + (j + k)) = y"
  shows "(i + j + -12 + (k::int)) - -15 = y"
by (tactic {* test [int_combine_numerals] *}) fact


subsection {* @{text inteq_cancel_numerals} *}

lemma assumes "u = Numeral0" shows "2*u = (u::int)"
by (tactic {* test [inteq_cancel_numerals] *}) fact
(* conclusion matches Rings.ring_1_no_zero_divisors_class.mult_cancel_right2 *)

lemma assumes "i + (j + k) = 3 + (u + y)"
  shows "(i + j + 12 + (k::int)) = u + 15 + y"
by (tactic {* test [inteq_cancel_numerals] *}) fact

lemma assumes "7 + (j + (i + k)) = y"
  shows "(i + j*2 + 12 + (k::int)) = j + 5 + y"
by (tactic {* test [inteq_cancel_numerals] *}) fact

lemma assumes "u + (6*z + (4*y + 6*w)) = 6*z' + (4*y' + (6*w' + vv))"
  shows "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + (vv::int)"
by (tactic {* test [int_combine_numerals, inteq_cancel_numerals] *}) fact


subsection {* @{text intless_cancel_numerals} *}

lemma assumes "y < 2 * b" shows "y - b < (b::int)"
by (tactic {* test [intless_cancel_numerals] *}) fact

lemma assumes "c + y < 4 * b" shows "y - (3*b + c) < (b::int) - 2*c"
by (tactic {* test [intless_cancel_numerals] *}) fact

lemma assumes "i + (j + k) < 8 + (u + y)"
  shows "(i + j + -3 + (k::int)) < u + 5 + y"
by (tactic {* test [intless_cancel_numerals] *}) fact

lemma assumes "9 + (i + (j + k)) < u + y"
  shows "(i + j + 3 + (k::int)) < u + -6 + y"
by (tactic {* test [intless_cancel_numerals] *}) fact


subsection {* @{text ring_eq_cancel_numeral_factor} *}

lemma assumes "3*x = 4*y" shows "9*x = 12 * (y::int)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "-3*x = 4*y" shows "-99*x = 132 * (y::int)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact


subsection {* @{text int_div_cancel_numeral_factors} *}

lemma assumes "(3*x) div (4*y) = z" shows "(9*x) div (12*y) = (z::int)"
by (tactic {* test [int_div_cancel_numeral_factors] *}) fact

lemma assumes "(-3*x) div (4*y) = z" shows "(-99*x) div (132*y) = (z::int)"
by (tactic {* test [int_div_cancel_numeral_factors] *}) fact

lemma assumes "(111*x) div (-44*y) = z" shows "(999*x) div (-396*y) = (z::int)"
by (tactic {* test [int_div_cancel_numeral_factors] *}) fact

lemma assumes "(11*x) div (9*y) = z" shows "(-99*x) div (-81*y) = (z::int)"
by (tactic {* test [int_div_cancel_numeral_factors] *}) fact

lemma assumes "(2*x) div (Numeral1*y) = z"
  shows "(-2 * x) div (-1 * (y::int)) = z"
by (tactic {* test [int_div_cancel_numeral_factors] *}) fact


subsection {* @{text ring_less_cancel_numeral_factor} *}

lemma assumes "3*x < 4*y" shows "9*x < 12 * (y::int)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "-3*x < 4*y" shows "-99*x < 132 * (y::int)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "111*x < -44*y" shows "999*x < -396 * (y::int)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "9*y < 11*x" shows "-99*x < -81 * (y::int)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "Numeral1*y < 2*x" shows "-2 * x < -(y::int)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "23*y < Numeral1*x" shows "-x < -23 * (y::int)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "3*x < 4*y" shows "9*x < 12 * (y::rat)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "-3*x < 4*y" shows "-99*x < 132 * (y::rat)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "111*x < -44*y" shows "999*x < -396 * (y::rat)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "9*y < 11*x" shows "-99*x < -81 * (y::rat)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "Numeral1*y < 2*x" shows "-2 * x < -(y::rat)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact

lemma assumes "23*y < Numeral1*x" shows "-x < -23 * (y::rat)"
by (tactic {* test [ring_less_cancel_numeral_factor] *}) fact


subsection {* @{text ring_le_cancel_numeral_factor} *}

lemma assumes "3*x \<le> 4*y" shows "9*x \<le> 12 * (y::int)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "-3*x \<le> 4*y" shows "-99*x \<le> 132 * (y::int)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "111*x \<le> -44*y" shows "999*x \<le> -396 * (y::int)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "9*y \<le> 11*x" shows "-99*x \<le> -81 * (y::int)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "Numeral1*y \<le> 2*x" shows "-2 * x \<le> -1 * (y::int)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "23*y \<le> Numeral1*x" shows "-x \<le> -23 * (y::int)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "Numeral1*y \<le> Numeral0" shows "0 \<le> (y::rat) * -2"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "3*x \<le> 4*y" shows "9*x \<le> 12 * (y::rat)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "-3*x \<le> 4*y" shows "-99*x \<le> 132 * (y::rat)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "111*x \<le> -44*y" shows "999*x \<le> -396 * (y::rat)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "-1*x \<le> Numeral1*y" shows "- ((2::rat) * x) \<le> 2*y"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "9*y \<le> 11*x" shows "-99*x \<le> -81 * (y::rat)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "Numeral1*y \<le> 2*x" shows "-2 * x \<le> -1 * (y::rat)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact

lemma assumes "23*y \<le> Numeral1*x" shows "-x \<le> -23 * (y::rat)"
by (tactic {* test [ring_le_cancel_numeral_factor] *}) fact


subsection {* @{text ring_eq_cancel_numeral_factor} *}

lemma assumes "111*x = -44*y" shows "999*x = -396 * (y::int)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "11*x = 9*y" shows "-99*x = -81 * (y::int)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "2*x = Numeral1*y" shows "-2 * x = -1 * (y::int)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "2*x = Numeral1*y" shows "-2 * x = -(y::int)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "3*x = 4*y" shows "9*x = 12 * (y::rat)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "-3*x = 4*y" shows "-99*x = 132 * (y::rat)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "111*x = -44*y" shows "999*x = -396 * (y::rat)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "11*x = 9*y" shows "-99*x = -81 * (y::rat)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "2*x = Numeral1*y" shows "-2 * x = -1 * (y::rat)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact

lemma assumes "2*x = Numeral1*y" shows "-2 * x = -(y::rat)"
by (tactic {* test [ring_eq_cancel_numeral_factor] *}) fact


subsection {* @{text field_cancel_numeral_factor} *}

lemma assumes "(3*x) / (4*y) = z" shows "(9*x) / (12 * (y::rat)) = z"
by (tactic {* test [field_cancel_numeral_factor] *}) fact

lemma assumes "(-3*x) / (4*y) = z" shows "(-99*x) / (132 * (y::rat)) = z"
by (tactic {* test [field_cancel_numeral_factor] *}) fact

lemma assumes "(111*x) / (-44*y) = z" shows "(999*x) / (-396 * (y::rat)) = z"
by (tactic {* test [field_cancel_numeral_factor] *}) fact

lemma assumes "(11*x) / (9*y) = z" shows "(-99*x) / (-81 * (y::rat)) = z"
by (tactic {* test [field_cancel_numeral_factor] *}) fact

lemma assumes "(2*x) / (Numeral1*y) = z" shows "(-2 * x) / (-1 * (y::rat)) = z"
by (tactic {* test [field_cancel_numeral_factor] *}) fact


subsection {* @{text ring_eq_cancel_factor} *}

lemma assumes "k = 0 \<or> x = y" shows "x*k = k*(y::int)"
by (tactic {* test [ring_eq_cancel_factor] *}) fact

lemma assumes "k = 0 \<or> 1 = y" shows "k = k*(y::int)"
by (tactic {* test [ring_eq_cancel_factor] *}) fact

lemma assumes "b = 0 \<or> a*c = 1" shows "a*(b*c) = (b::int)"
by (tactic {* test [ring_eq_cancel_factor] *}) fact

lemma assumes "a = 0 \<or> b = 0 \<or> c = d*x" shows "a*(b*c) = d*(b::int)*(x*a)"
by (tactic {* test [ring_eq_cancel_factor] *}) fact

lemma assumes "k = 0 \<or> x = y" shows "x*k = k*(y::rat)"
by (tactic {* test [ring_eq_cancel_factor] *}) fact

lemma assumes "k = 0 \<or> 1 = y" shows "k = k*(y::rat)"
by (tactic {* test [ring_eq_cancel_factor] *}) fact

lemma assumes "b = 0 \<or> a*c = 1" shows "a*(b*c) = (b::rat)"
by (tactic {* test [ring_eq_cancel_factor] *}) fact

lemma assumes "a = 0 \<or> b = 0 \<or> c = d*x" shows "a*(b*c) = d*(b::rat)*(x*a)"
by (tactic {* test [ring_eq_cancel_factor] *}) fact


subsection {* @{text int_div_cancel_factor} *}

lemma assumes "(if k = 0 then 0 else x div y) = uu"
  shows "(x*k) div (k*(y::int)) = (uu::int)"
by (tactic {* test [int_div_cancel_factor] *}) fact

lemma assumes "(if k = 0 then 0 else 1 div y) = uu"
  shows "(k) div (k*(y::int)) = (uu::int)"
by (tactic {* test [int_div_cancel_factor] *}) fact

lemma assumes "(if b = 0 then 0 else a * c) = uu"
  shows "(a*(b*c)) div ((b::int)) = (uu::int)"
by (tactic {* test [int_div_cancel_factor] *}) fact

lemma assumes "(if a = 0 then 0 else if b = 0 then 0 else c div (d * x)) = uu"
  shows "(a*(b*c)) div (d*(b::int)*(x*a)) = (uu::int)"
by (tactic {* test [int_div_cancel_factor] *}) fact


subsection {* @{text divide_cancel_factor} *}

lemma assumes "(if k = 0 then 0 else x / y) = uu"
  shows "(x*k) / (k*(y::rat)) = (uu::rat)"
by (tactic {* test [divide_cancel_factor] *}) fact

lemma assumes "(if k = 0 then 0 else 1 / y) = uu"
  shows "(k) / (k*(y::rat)) = (uu::rat)"
by (tactic {* test [divide_cancel_factor] *}) fact

lemma assumes "(if b = 0 then 0 else a * c / 1) = uu"
  shows "(a*(b*c)) / ((b::rat)) = (uu::rat)"
by (tactic {* test [divide_cancel_factor] *}) fact

lemma assumes "(if a = 0 then 0 else if b = 0 then 0 else c / (d * x)) = uu"
  shows "(a*(b*c)) / (d*(b::rat)*(x*a)) = (uu::rat)"
by (tactic {* test [divide_cancel_factor] *}) fact

lemma shows "a*(b*c)/(y*z) = d*(b::rat)*(x*a)/z"
oops -- "FIXME: need simproc to cover this case"


subsection {* @{text linordered_ring_less_cancel_factor} *}

lemma assumes "0 < z \<Longrightarrow> x < y" shows "(0::rat) < z \<Longrightarrow> x*z < y*z"
by (tactic {* test [linordered_ring_less_cancel_factor] *}) fact

lemma assumes "0 < z \<Longrightarrow> x < y" shows "(0::rat) < z \<Longrightarrow> x*z < z*y"
by (tactic {* test [linordered_ring_less_cancel_factor] *}) fact

lemma assumes "0 < z \<Longrightarrow> x < y" shows "(0::rat) < z \<Longrightarrow> z*x < y*z"
by (tactic {* test [linordered_ring_less_cancel_factor] *}) fact

lemma assumes "0 < z \<Longrightarrow> x < y" shows "(0::rat) < z \<Longrightarrow> z*x < z*y"
by (tactic {* test [linordered_ring_less_cancel_factor] *}) fact


subsection {* @{text linordered_ring_le_cancel_factor} *}

lemma assumes "0 < z \<Longrightarrow> x \<le> y" shows "(0::rat) < z \<Longrightarrow> x*z \<le> y*z"
by (tactic {* test [linordered_ring_le_cancel_factor] *}) fact

lemma assumes "0 < z \<Longrightarrow> x \<le> y" shows "(0::rat) < z \<Longrightarrow> z*x \<le> z*y"
by (tactic {* test [linordered_ring_le_cancel_factor] *}) fact


subsection {* @{text field_combine_numerals} *}

lemma assumes "5 / 6 * x = uu" shows "(x::rat) / 2 + x / 3 = uu"
by (tactic {* test [field_combine_numerals] *}) fact

lemma assumes "6 / 9 * x + y = uu" shows "(x::rat) / 3 + y + x / 3 = uu"
by (tactic {* test [field_combine_numerals] *}) fact

lemma assumes "9 / 9 * x = uu" shows "2 * (x::rat) / 3 + x / 3 = uu"
by (tactic {* test [field_combine_numerals] *}) fact

lemma "2/3 * (x::rat) + x / 3 = uu"
apply (tactic {* test [field_combine_numerals] *})?
oops -- "FIXME: test fails"


subsection {* @{text field_eq_cancel_numeral_factor} *}

text {* TODO: tests for @{text field_eq_cancel_numeral_factor} simproc *}


subsection {* @{text field_cancel_numeral_factor} *}

text {* TODO: tests for @{text field_cancel_numeral_factor} simproc *}

end
