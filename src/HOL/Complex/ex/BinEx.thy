(*  Title:      HOL/Complex/ex/BinEx.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Binary arithmetic examples *}

theory BinEx = Complex_Main:

text {*
  Examples of performing binary arithmetic by simplification.  This time
  we use the reals, though the representation is just of integers.
*}

subsection{*Real Arithmetic*}

subsubsection {*Addition *}

lemma "(1359::real) + -2468 = -1109"
  by simp

lemma "(93746::real) + -46375 = 47371"
  by simp


subsubsection {*Negation *}

lemma "- (65745::real) = -65745"
  by simp

lemma "- (-54321::real) = 54321"
  by simp


subsubsection {*Multiplication *}

lemma "(-84::real) * 51 = -4284"
  by simp

lemma "(255::real) * 255 = 65025"
  by simp

lemma "(1359::real) * -2468 = -3354012"
  by simp


subsubsection {*Inequalities *}

lemma "(89::real) * 10 \<noteq> 889"
  by simp

lemma "(13::real) < 18 - 4"
  by simp

lemma "(-345::real) < -242 + -100"
  by simp

lemma "(13557456::real) < 18678654"
  by simp

lemma "(999999::real) \<le> (1000001 + 1) - 2"
  by simp

lemma "(1234567::real) \<le> 1234567"
  by simp


subsubsection {*Powers *}

lemma "2 ^ 15 = (32768::real)"
  by simp

lemma "-3 ^ 7 = (-2187::real)"
  by simp

lemma "13 ^ 7 = (62748517::real)"
  by simp

lemma "3 ^ 15 = (14348907::real)"
  by simp

lemma "-5 ^ 11 = (-48828125::real)"
  by simp


subsubsection {*Tests *}

lemma "(x + y = x) = (y = (0::real))"
  by arith

lemma "(x + y = y) = (x = (0::real))"
  by arith

lemma "(x + y = (0::real)) = (x = -y)"
  by arith

lemma "(x + y = (0::real)) = (y = -x)"
  by arith

lemma "((x + y) < (x + z)) = (y < (z::real))"
  by arith

lemma "((x + z) < (y + z)) = (x < (y::real))"
  by arith

lemma "(\<not> x < y) = (y \<le> (x::real))"
  by arith

lemma "\<not> (x < y \<and> y < (x::real))"
  by arith

lemma "(x::real) < y ==> \<not> y < x"
  by arith

lemma "((x::real) \<noteq> y) = (x < y \<or> y < x)"
  by arith

lemma "(\<not> x \<le> y) = (y < (x::real))"
  by arith

lemma "x \<le> y \<or> y \<le> (x::real)"
  by arith

lemma "x \<le> y \<or> y < (x::real)"
  by arith

lemma "x < y \<or> y \<le> (x::real)"
  by arith

lemma "x \<le> (x::real)"
  by arith

lemma "((x::real) \<le> y) = (x < y \<or> x = y)"
  by arith

lemma "((x::real) \<le> y \<and> y \<le> x) = (x = y)"
  by arith

lemma "\<not>(x < y \<and> y \<le> (x::real))"
  by arith

lemma "\<not>(x \<le> y \<and> y < (x::real))"
  by arith

lemma "(-x < (0::real)) = (0 < x)"
  by arith

lemma "((0::real) < -x) = (x < 0)"
  by arith

lemma "(-x \<le> (0::real)) = (0 \<le> x)"
  by arith

lemma "((0::real) \<le> -x) = (x \<le> 0)"
  by arith

lemma "(x::real) = y \<or> x < y \<or> y < x"
  by arith

lemma "(x::real) = 0 \<or> 0 < x \<or> 0 < -x"
  by arith

lemma "(0::real) \<le> x \<or> 0 \<le> -x"
  by arith

lemma "((x::real) + y \<le> x + z) = (y \<le> z)"
  by arith

lemma "((x::real) + z \<le> y + z) = (x \<le> y)"
  by arith

lemma "(w::real) < x \<and> y < z ==> w + y < x + z"
  by arith

lemma "(w::real) \<le> x \<and> y \<le> z ==> w + y \<le> x + z"
  by arith

lemma "(0::real) \<le> x \<and> 0 \<le> y ==> 0 \<le> x + y"
  by arith

lemma "(0::real) < x \<and> 0 < y ==> 0 < x + y"
  by arith

lemma "(-x < y) = (0 < x + (y::real))"
  by arith

lemma "(x < -y) = (x + y < (0::real))"
  by arith

lemma "(y < x + -z) = (y + z < (x::real))"
  by arith

lemma "(x + -y < z) = (x < z + (y::real))"
  by arith

lemma "x \<le> y ==> x < y + (1::real)"
  by arith

lemma "(x - y) + y = (x::real)"
  by arith

lemma "y + (x - y) = (x::real)"
  by arith

lemma "x - x = (0::real)"
  by arith

lemma "(x - y = 0) = (x = (y::real))"
  by arith

lemma "((0::real) \<le> x + x) = (0 \<le> x)"
  by arith

lemma "(-x \<le> x) = ((0::real) \<le> x)"
  by arith

lemma "(x \<le> -x) = (x \<le> (0::real))"
  by arith

lemma "(-x = (0::real)) = (x = 0)"
  by arith

lemma "-(x - y) = y - (x::real)"
  by arith

lemma "((0::real) < x - y) = (y < x)"
  by arith

lemma "((0::real) \<le> x - y) = (y \<le> x)"
  by arith

lemma "(x + y) - x = (y::real)"
  by arith

lemma "(-x = y) = (x = (-y::real))"
  by arith

lemma "x < (y::real) ==> \<not>(x = y)"
  by arith

lemma "(x \<le> x + y) = ((0::real) \<le> y)"
  by arith

lemma "(y \<le> x + y) = ((0::real) \<le> x)"
  by arith

lemma "(x < x + y) = ((0::real) < y)"
  by arith

lemma "(y < x + y) = ((0::real) < x)"
  by arith

lemma "(x - y) - x = (-y::real)"
  by arith

lemma "(x + y < z) = (x < z - (y::real))"
  by arith

lemma "(x - y < z) = (x < z + (y::real))"
  by arith

lemma "(x < y - z) = (x + z < (y::real))"
  by arith

lemma "(x \<le> y - z) = (x + z \<le> (y::real))"
  by arith

lemma "(x - y \<le> z) = (x \<le> z + (y::real))"
  by arith

lemma "(-x < -y) = (y < (x::real))"
  by arith

lemma "(-x \<le> -y) = (y \<le> (x::real))"
  by arith

lemma "(a + b) - (c + d) = (a - c) + (b - (d::real))"
  by arith

lemma "(0::real) - x = -x"
  by arith

lemma "x - (0::real) = x"
  by arith

lemma "w \<le> x \<and> y < z ==> w + y < x + (z::real)"
  by arith

lemma "w < x \<and> y \<le> z ==> w + y < x + (z::real)"
  by arith

lemma "(0::real) \<le> x \<and> 0 < y ==> 0 < x + (y::real)"
  by arith

lemma "(0::real) < x \<and> 0 \<le> y ==> 0 < x + y"
  by arith

lemma "-x - y = -(x + (y::real))"
  by arith

lemma "x - (-y) = x + (y::real)"
  by arith

lemma "-x - -y = y - (x::real)"
  by arith

lemma "(a - b) + (b - c) = a - (c::real)"
  by arith

lemma "(x = y - z) = (x + z = (y::real))"
  by arith

lemma "(x - y = z) = (x = z + (y::real))"
  by arith

lemma "x - (x - y) = (y::real)"
  by arith

lemma "x - (x + y) = -(y::real)"
  by arith

lemma "x = y ==> x \<le> (y::real)"
  by arith

lemma "(0::real) < x ==> \<not>(x = 0)"
  by arith

lemma "(x + y) * (x - y) = (x * x) - (y * y)"
  oops

lemma "(-x = -y) = (x = (y::real))"
  by arith

lemma "(-x < -y) = (y < (x::real))"
  by arith

lemma "!!a::real. a \<le> b ==> c \<le> d ==> x + y < z ==> a + c \<le> b + d"
  by (tactic "fast_arith_tac 1")

lemma "!!a::real. a < b ==> c < d ==> a - d \<le> b + (-c)"
  by (tactic "fast_arith_tac 1")

lemma "!!a::real. a \<le> b ==> b + b \<le> c ==> a + a \<le> c"
  by (tactic "fast_arith_tac 1")

lemma "!!a::real. a + b \<le> i + j ==> a \<le> b ==> i \<le> j ==> a + a \<le> j + j"
  by (tactic "fast_arith_tac 1")

lemma "!!a::real. a + b < i + j ==> a < b ==> i < j ==> a + a < j + j"
  by (tactic "fast_arith_tac 1")

lemma "!!a::real. a + b + c \<le> i + j + k \<and> a \<le> b \<and> b \<le> c \<and> i \<le> j \<and> j \<le> k --> a + a + a \<le> k + k + k"
  by arith

lemma "!!a::real. a + b + c + d \<le> i + j + k + l ==> a \<le> b ==> b \<le> c
    ==> c \<le> d ==> i \<le> j ==> j \<le> k ==> k \<le> l ==> a \<le> l"
  by (tactic "fast_arith_tac 1")

lemma "!!a::real. a + b + c + d \<le> i + j + k + l ==> a \<le> b ==> b \<le> c
    ==> c \<le> d ==> i \<le> j ==> j \<le> k ==> k \<le> l ==> a + a + a + a \<le> l + l + l + l"
  by (tactic "fast_arith_tac 1")

lemma "!!a::real. a + b + c + d \<le> i + j + k + l ==> a \<le> b ==> b \<le> c
    ==> c \<le> d ==> i \<le> j ==> j \<le> k ==> k \<le> l ==> a + a + a + a + a \<le> l + l + l + l + i"
  by (tactic "fast_arith_tac 1")

lemma "!!a::real. a + b + c + d \<le> i + j + k + l ==> a \<le> b ==> b \<le> c
    ==> c \<le> d ==> i \<le> j ==> j \<le> k ==> k \<le> l ==> a + a + a + a + a + a \<le> l + l + l + l + i + l"
  by (tactic "fast_arith_tac 1")


subsection{*Complex Arithmetic*}

lemma "(1359 + 93746*ii) - (2468 + 46375*ii) = -1109 + 47371*ii"
  by simp

lemma "- (65745 + -47371*ii) = -65745 + 47371*ii"
  by simp

text{*Multiplication requires distributive laws.  Perhaps versions instantiated
to literal constants should be added to the simpset.*}

lemmas distrib = complex_add_mult_distrib complex_add_mult_distrib2
                 complex_diff_mult_distrib complex_diff_mult_distrib2

lemma "(1 + ii) * (1 - ii) = 2"
by (simp add: distrib)

lemma "(1 + 2*ii) * (1 + 3*ii) = -5 + 5*ii"
by (simp add: distrib)

lemma "(-84 + 255*ii) + (51 * 255*ii) = -84 + 13260 * ii"
by (simp add: distrib)

text{*No inequalities: we have no ordering on the complex numbers.*}

text{*No powers (not supported yet)*}

text{*No linear arithmetic*}

end
