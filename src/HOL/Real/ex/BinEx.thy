(*  Title:      HOL/Real/ex/BinEx.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Binary arithmetic examples *}

theory BinEx = Real:

text {*
  Examples of performing binary arithmetic by simplification This time
  we use the reals, though the representation is just of integers.
*}

text {* \medskip Addition *}

lemma "(# 1359::real) + # -2468 = # -1109"
  by simp

lemma "(# 93746::real) + # -46375 = # 47371"
  by simp


text {* \medskip Negation *}

lemma "- (# 65745::real) = # -65745"
  by simp

lemma "- (# -54321::real) = # 54321"
  by simp


text {* \medskip Multiplication *}

lemma "(# -84::real) * # 51 = # -4284"
  by simp

lemma "(# 255::real) * # 255 = # 65025"
  by simp

lemma "(# 1359::real) * # -2468 = # -3354012"
  by simp


text {* \medskip Inequalities *}

lemma "(# 89::real) * # 10 \<noteq> # 889"
  by simp

lemma "(# 13::real) < # 18 - # 4"
  by simp

lemma "(# -345::real) < # -242 + # -100"
  by simp

lemma "(# 13557456::real) < # 18678654"
  by simp

lemma "(# 999999::real) \<le> (# 1000001 + Numeral1)-# 2"
  by simp

lemma "(# 1234567::real) \<le> # 1234567"
  by simp


text {* \medskip Tests *}

lemma "(x + y = x) = (y = (Numeral0::real))"
  by arith

lemma "(x + y = y) = (x = (Numeral0::real))"
  by arith

lemma "(x + y = (Numeral0::real)) = (x = -y)"
  by arith

lemma "(x + y = (Numeral0::real)) = (y = -x)"
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

lemma "(-x < (Numeral0::real)) = (Numeral0 < x)"
  by arith

lemma "((Numeral0::real) < -x) = (x < Numeral0)"
  by arith

lemma "(-x \<le> (Numeral0::real)) = (Numeral0 \<le> x)"
  by arith

lemma "((Numeral0::real) \<le> -x) = (x \<le> Numeral0)"
  by arith

lemma "(x::real) = y \<or> x < y \<or> y < x"
  by arith

lemma "(x::real) = Numeral0 \<or> Numeral0 < x \<or> Numeral0 < -x"
  by arith

lemma "(Numeral0::real) \<le> x \<or> Numeral0 \<le> -x"
  by arith

lemma "((x::real) + y \<le> x + z) = (y \<le> z)"
  by arith

lemma "((x::real) + z \<le> y + z) = (x \<le> y)"
  by arith

lemma "(w::real) < x \<and> y < z ==> w + y < x + z"
  by arith

lemma "(w::real) \<le> x \<and> y \<le> z ==> w + y \<le> x + z"
  by arith

lemma "(Numeral0::real) \<le> x \<and> Numeral0 \<le> y ==> Numeral0 \<le> x + y"
  by arith

lemma "(Numeral0::real) < x \<and> Numeral0 < y ==> Numeral0 < x + y"
  by arith

lemma "(-x < y) = (Numeral0 < x + (y::real))"
  by arith

lemma "(x < -y) = (x + y < (Numeral0::real))"
  by arith

lemma "(y < x + -z) = (y + z < (x::real))"
  by arith

lemma "(x + -y < z) = (x < z + (y::real))"
  by arith

lemma "x \<le> y ==> x < y + (Numeral1::real)"
  by arith

lemma "(x - y) + y = (x::real)"
  by arith

lemma "y + (x - y) = (x::real)"
  by arith

lemma "x - x = (Numeral0::real)"
  by arith

lemma "(x - y = Numeral0) = (x = (y::real))"
  by arith

lemma "((Numeral0::real) \<le> x + x) = (Numeral0 \<le> x)"
  by arith

lemma "(-x \<le> x) = ((Numeral0::real) \<le> x)"
  by arith

lemma "(x \<le> -x) = (x \<le> (Numeral0::real))"
  by arith

lemma "(-x = (Numeral0::real)) = (x = Numeral0)"
  by arith

lemma "-(x - y) = y - (x::real)"
  by arith

lemma "((Numeral0::real) < x - y) = (y < x)"
  by arith

lemma "((Numeral0::real) \<le> x - y) = (y \<le> x)"
  by arith

lemma "(x + y) - x = (y::real)"
  by arith

lemma "(-x = y) = (x = (-y::real))"
  by arith

lemma "x < (y::real) ==> \<not>(x = y)"
  by arith

lemma "(x \<le> x + y) = ((Numeral0::real) \<le> y)"
  by arith

lemma "(y \<le> x + y) = ((Numeral0::real) \<le> x)"
  by arith

lemma "(x < x + y) = ((Numeral0::real) < y)"
  by arith

lemma "(y < x + y) = ((Numeral0::real) < x)"
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

lemma "(Numeral0::real) - x = -x"
  by arith

lemma "x - (Numeral0::real) = x"
  by arith

lemma "w \<le> x \<and> y < z ==> w + y < x + (z::real)"
  by arith

lemma "w < x \<and> y \<le> z ==> w + y < x + (z::real)"
  by arith

lemma "(Numeral0::real) \<le> x \<and> Numeral0 < y ==> Numeral0 < x + (y::real)"
  by arith

lemma "(Numeral0::real) < x \<and> Numeral0 \<le> y ==> Numeral0 < x + y"
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

lemma "(Numeral0::real) < x ==> \<not>(x = Numeral0)"
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

end
