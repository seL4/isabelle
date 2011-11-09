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
  fun test ps = CHANGED (asm_simp_tac (HOL_basic_ss addsimprocs ps) 1)
*}


subsection {* @{text int_combine_numerals} *}

notepad begin
  fix a b c d oo uu i j k l u v w x y z :: "'a::number_ring"
  {
    assume "10 + (2 * l + oo) = uu"
    have "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = uu"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "-3 + (i + (j + k)) = y"
    have "(i + j + 12 + k) - 15 = y"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "7 + (i + (j + k)) = y"
    have "(i + j + 12 + k) - 5 = y"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "-4 * (u * v) + (2 * x + y) = w"
    have "(2*x - (u*v) + y) - v*3*u = w"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "Numeral0 * (u*v) + (2 * x * u * v + y) = w"
    have "(2*x*u*v + (u*v)*4 + y) - v*u*4 = w"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "3 * (u * v) + (2 * x * u * v + y) = w"
    have "(2*x*u*v + (u*v)*4 + y) - v*u = w"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "-3 * (u * v) + (- (x * u * v) + - y) = w"
    have "u*v - (x*u*v + (u*v)*4 + y) = w"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "Numeral0 * b + (a + - c) = d"
    have "a + -(b+c) + b = d"
      apply (simp only: minus_add_distrib)
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "-2 * b + (a + - c) = d"
    have "a + -(b+c) - b = d"
      apply (simp only: minus_add_distrib)
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "-7 + (i + (j + (k + (- u + - y)))) = z"
    have "(i + j + -2 + k) - (u + 5 + y) = z"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "-27 + (i + (j + k)) = y"
    have "(i + j + -12 + k) - 15 = y"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "27 + (i + (j + k)) = y"
    have "(i + j + 12 + k) - -15 = y"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  next
    assume "3 + (i + (j + k)) = y"
    have "(i + j + -12 + k) - -15 = y"
      by (tactic {* test [@{simproc int_combine_numerals}] *}) fact
  }
end

subsection {* @{text inteq_cancel_numerals} *}

notepad begin
  fix i j k u vv w y z w' y' z' :: "'a::number_ring"
  {
    assume "u = Numeral0" have "2*u = u"
      by (tactic {* test [@{simproc inteq_cancel_numerals}] *}) fact
(* conclusion matches Rings.ring_1_no_zero_divisors_class.mult_cancel_right2 *)
  next
    assume "i + (j + k) = 3 + (u + y)"
    have "(i + j + 12 + k) = u + 15 + y"
      by (tactic {* test [@{simproc inteq_cancel_numerals}] *}) fact
  next
    assume "7 + (j + (i + k)) = y"
    have "(i + j*2 + 12 + k) = j + 5 + y"
      by (tactic {* test [@{simproc inteq_cancel_numerals}] *}) fact
  next
    assume "u + (6*z + (4*y + 6*w)) = 6*z' + (4*y' + (6*w' + vv))"
    have "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + vv"
      by (tactic {* test [@{simproc int_combine_numerals}, @{simproc inteq_cancel_numerals}] *}) fact
  }
end

subsection {* @{text intless_cancel_numerals} *}

notepad begin
  fix b c i j k u y :: "'a::{linordered_idom,number_ring}"
  {
    assume "y < 2 * b" have "y - b < b"
      by (tactic {* test [@{simproc intless_cancel_numerals}] *}) fact
  next
    assume "c + y < 4 * b" have "y - (3*b + c) < b - 2*c"
      by (tactic {* test [@{simproc intless_cancel_numerals}] *}) fact
  next
    assume "i + (j + k) < 8 + (u + y)"
    have "(i + j + -3 + k) < u + 5 + y"
      by (tactic {* test [@{simproc intless_cancel_numerals}] *}) fact
  next
    assume "9 + (i + (j + k)) < u + y"
    have "(i + j + 3 + k) < u + -6 + y"
      by (tactic {* test [@{simproc intless_cancel_numerals}] *}) fact
  }
end

subsection {* @{text ring_eq_cancel_numeral_factor} *}

notepad begin
  fix x y :: "'a::{idom,ring_char_0,number_ring}"
  {
    assume "3*x = 4*y" have "9*x = 12 * y"
      by (tactic {* test [@{simproc ring_eq_cancel_numeral_factor}] *}) fact
  next
    assume "-3*x = 4*y" have "-99*x = 132 * y"
      by (tactic {* test [@{simproc ring_eq_cancel_numeral_factor}] *}) fact
  next
    assume "111*x = -44*y" have "999*x = -396 * y"
      by (tactic {* test [@{simproc ring_eq_cancel_numeral_factor}] *}) fact
  next
    assume "11*x = 9*y" have "-99*x = -81 * y"
      by (tactic {* test [@{simproc ring_eq_cancel_numeral_factor}] *}) fact
  next
    assume "2*x = Numeral1*y" have "-2 * x = -1 * y"
      by (tactic {* test [@{simproc ring_eq_cancel_numeral_factor}] *}) fact
  next
    assume "2*x = Numeral1*y" have "-2 * x = -y"
      by (tactic {* test [@{simproc ring_eq_cancel_numeral_factor}] *}) fact
  }
end

subsection {* @{text int_div_cancel_numeral_factors} *}

notepad begin
  fix x y z :: "'a::{semiring_div,ring_char_0,number_ring}"
  {
    assume "(3*x) div (4*y) = z" have "(9*x) div (12*y) = z"
      by (tactic {* test [@{simproc int_div_cancel_numeral_factors}] *}) fact
  next
    assume "(-3*x) div (4*y) = z" have "(-99*x) div (132*y) = z"
      by (tactic {* test [@{simproc int_div_cancel_numeral_factors}] *}) fact
  next
    assume "(111*x) div (-44*y) = z" have "(999*x) div (-396*y) = z"
      by (tactic {* test [@{simproc int_div_cancel_numeral_factors}] *}) fact
  next
    assume "(11*x) div (9*y) = z" have "(-99*x) div (-81*y) = z"
      by (tactic {* test [@{simproc int_div_cancel_numeral_factors}] *}) fact
  next
    assume "(2*x) div (Numeral1*y) = z"
    have "(-2 * x) div (-1 * y) = z"
      by (tactic {* test [@{simproc int_div_cancel_numeral_factors}] *}) fact
  }
end

subsection {* @{text ring_less_cancel_numeral_factor} *}

notepad begin
  fix x y :: "'a::{linordered_idom,number_ring}"
  {
    assume "3*x < 4*y" have "9*x < 12 * y"
      by (tactic {* test [@{simproc ring_less_cancel_numeral_factor}] *}) fact
  next
    assume "-3*x < 4*y" have "-99*x < 132 * y"
      by (tactic {* test [@{simproc ring_less_cancel_numeral_factor}] *}) fact
  next
    assume "111*x < -44*y" have "999*x < -396 * y"
      by (tactic {* test [@{simproc ring_less_cancel_numeral_factor}] *}) fact
  next
    assume "9*y < 11*x" have "-99*x < -81 * y"
      by (tactic {* test [@{simproc ring_less_cancel_numeral_factor}] *}) fact
  next
    assume "Numeral1*y < 2*x" have "-2 * x < -y"
      by (tactic {* test [@{simproc ring_less_cancel_numeral_factor}] *}) fact
  next
    assume "23*y < Numeral1*x" have "-x < -23 * y"
      by (tactic {* test [@{simproc ring_less_cancel_numeral_factor}] *}) fact
  }
end

subsection {* @{text ring_le_cancel_numeral_factor} *}

notepad begin
  fix x y :: "'a::{linordered_idom,number_ring}"
  {
    assume "3*x \<le> 4*y" have "9*x \<le> 12 * y"
      by (tactic {* test [@{simproc ring_le_cancel_numeral_factor}] *}) fact
  next
    assume "-3*x \<le> 4*y" have "-99*x \<le> 132 * y"
      by (tactic {* test [@{simproc ring_le_cancel_numeral_factor}] *}) fact
  next
    assume "111*x \<le> -44*y" have "999*x \<le> -396 * y"
      by (tactic {* test [@{simproc ring_le_cancel_numeral_factor}] *}) fact
  next
    assume "9*y \<le> 11*x" have "-99*x \<le> -81 * y"
      by (tactic {* test [@{simproc ring_le_cancel_numeral_factor}] *}) fact
  next
    assume "Numeral1*y \<le> 2*x" have "-2 * x \<le> -1 * y"
      by (tactic {* test [@{simproc ring_le_cancel_numeral_factor}] *}) fact
  next
    assume "23*y \<le> Numeral1*x" have "-x \<le> -23 * y"
      by (tactic {* test [@{simproc ring_le_cancel_numeral_factor}] *}) fact
  next
    assume "Numeral1*y \<le> Numeral0" have "0 \<le> y * -2"
      by (tactic {* test [@{simproc ring_le_cancel_numeral_factor}] *}) fact
  next
    assume "-1*x \<le> Numeral1*y" have "- (2 * x) \<le> 2*y"
      by (tactic {* test [@{simproc ring_le_cancel_numeral_factor}] *}) fact
  }
end

subsection {* @{text divide_cancel_numeral_factor} *}

notepad begin
  fix x y z :: "'a::{field_inverse_zero,ring_char_0,number_ring}"
  {
    assume "(3*x) / (4*y) = z" have "(9*x) / (12 * y) = z"
      by (tactic {* test [@{simproc divide_cancel_numeral_factor}] *}) fact
  next
    assume "(-3*x) / (4*y) = z" have "(-99*x) / (132 * y) = z"
      by (tactic {* test [@{simproc divide_cancel_numeral_factor}] *}) fact
  next
    assume "(111*x) / (-44*y) = z" have "(999*x) / (-396 * y) = z"
      by (tactic {* test [@{simproc divide_cancel_numeral_factor}] *}) fact
  next
    assume "(11*x) / (9*y) = z" have "(-99*x) / (-81 * y) = z"
      by (tactic {* test [@{simproc divide_cancel_numeral_factor}] *}) fact
  next
    assume "(2*x) / (Numeral1*y) = z" have "(-2 * x) / (-1 * y) = z"
      by (tactic {* test [@{simproc divide_cancel_numeral_factor}] *}) fact
  }
end

subsection {* @{text ring_eq_cancel_factor} *}

notepad begin
  fix a b c d k x y :: "'a::idom"
  {
    assume "k = 0 \<or> x = y" have "x*k = k*y"
      by (tactic {* test [@{simproc ring_eq_cancel_factor}] *}) fact
  next
    assume "k = 0 \<or> 1 = y" have "k = k*y"
      by (tactic {* test [@{simproc ring_eq_cancel_factor}] *}) fact
  next
    assume "b = 0 \<or> a*c = 1" have "a*(b*c) = b"
      by (tactic {* test [@{simproc ring_eq_cancel_factor}] *}) fact
  next
    assume "a = 0 \<or> b = 0 \<or> c = d*x" have "a*(b*c) = d*b*(x*a)"
      by (tactic {* test [@{simproc ring_eq_cancel_factor}] *}) fact
  next
    assume "k = 0 \<or> x = y" have "x*k = k*y"
      by (tactic {* test [@{simproc ring_eq_cancel_factor}] *}) fact
  next
    assume "k = 0 \<or> 1 = y" have "k = k*y"
      by (tactic {* test [@{simproc ring_eq_cancel_factor}] *}) fact
  }
end

subsection {* @{text int_div_cancel_factor} *}

notepad begin
  fix a b c d k uu x y :: "'a::semiring_div"
  {
    assume "(if k = 0 then 0 else x div y) = uu"
    have "(x*k) div (k*y) = uu"
      by (tactic {* test [@{simproc int_div_cancel_factor}] *}) fact
  next
    assume "(if k = 0 then 0 else 1 div y) = uu"
    have "(k) div (k*y) = uu"
      by (tactic {* test [@{simproc int_div_cancel_factor}] *}) fact
  next
    assume "(if b = 0 then 0 else a * c) = uu"
    have "(a*(b*c)) div b = uu"
      by (tactic {* test [@{simproc int_div_cancel_factor}] *}) fact
  next
    assume "(if a = 0 then 0 else if b = 0 then 0 else c div (d * x)) = uu"
    have "(a*(b*c)) div (d*b*(x*a)) = uu"
      by (tactic {* test [@{simproc int_div_cancel_factor}] *}) fact
  }
end

subsection {* @{text divide_cancel_factor} *}

notepad begin
  fix a b c d k uu x y :: "'a::field_inverse_zero"
  {
    assume "(if k = 0 then 0 else x / y) = uu"
    have "(x*k) / (k*y) = uu"
      by (tactic {* test [@{simproc divide_cancel_factor}] *}) fact
  next
    assume "(if k = 0 then 0 else 1 / y) = uu"
    have "(k) / (k*y) = uu"
      by (tactic {* test [@{simproc divide_cancel_factor}] *}) fact
  next
    assume "(if b = 0 then 0 else a * c / 1) = uu"
    have "(a*(b*c)) / b = uu"
      by (tactic {* test [@{simproc divide_cancel_factor}] *}) fact
  next
    assume "(if a = 0 then 0 else if b = 0 then 0 else c / (d * x)) = uu"
    have "(a*(b*c)) / (d*b*(x*a)) = uu"
      by (tactic {* test [@{simproc divide_cancel_factor}] *}) fact
  }
end

lemma shows "a*(b*c)/(y*z) = d*(b::rat)*(x*a)/z"
oops -- "FIXME: need simproc to cover this case"


subsection {* @{text linordered_ring_less_cancel_factor} *}

notepad begin
  fix x y z :: "'a::linordered_idom"
  {
    assume "0 < z \<Longrightarrow> x < y" have "0 < z \<Longrightarrow> x*z < y*z"
      by (tactic {* test [@{simproc linordered_ring_less_cancel_factor}] *}) fact
  next
    assume "0 < z \<Longrightarrow> x < y" have "0 < z \<Longrightarrow> x*z < z*y"
      by (tactic {* test [@{simproc linordered_ring_less_cancel_factor}] *}) fact
  next
    assume "0 < z \<Longrightarrow> x < y" have "0 < z \<Longrightarrow> z*x < y*z"
      by (tactic {* test [@{simproc linordered_ring_less_cancel_factor}] *}) fact
  next
    assume "0 < z \<Longrightarrow> x < y" have "0 < z \<Longrightarrow> z*x < z*y"
      by (tactic {* test [@{simproc linordered_ring_less_cancel_factor}] *}) fact
  }
end

subsection {* @{text linordered_ring_le_cancel_factor} *}

notepad begin
  fix x y z :: "'a::linordered_idom"
  {
    assume "0 < z \<Longrightarrow> x \<le> y" have "0 < z \<Longrightarrow> x*z \<le> y*z"
      by (tactic {* test [@{simproc linordered_ring_le_cancel_factor}] *}) fact
  next
    assume "0 < z \<Longrightarrow> x \<le> y" have "0 < z \<Longrightarrow> z*x \<le> z*y"
      by (tactic {* test [@{simproc linordered_ring_le_cancel_factor}] *}) fact
  }
end

subsection {* @{text field_combine_numerals} *}

notepad begin
  fix x uu :: "'a::{field_inverse_zero,ring_char_0,number_ring}"
  {
    assume "5 / 6 * x = uu" have "x / 2 + x / 3 = uu"
      by (tactic {* test [@{simproc field_combine_numerals}] *}) fact
  next
    assume "6 / 9 * x + y = uu" have "x / 3 + y + x / 3 = uu"
      by (tactic {* test [@{simproc field_combine_numerals}] *}) fact
  next
    assume "9 / 9 * x = uu" have "2 * x / 3 + x / 3 = uu"
      by (tactic {* test [@{simproc field_combine_numerals}] *}) fact
  }
end

lemma "2/3 * (x::rat) + x / 3 = uu"
apply (tactic {* test [@{simproc field_combine_numerals}] *})?
oops -- "FIXME: test fails"

end
