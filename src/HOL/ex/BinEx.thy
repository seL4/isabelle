(*  Title:      HOL/ex/BinEx.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header {* Binary arithmetic examples *}

theory BinEx
imports Complex_Main
begin

subsection {* Regression Testing for Cancellation Simprocs *}

lemma "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = (uu::int)"
apply simp  oops

lemma "2*u = (u::int)"
apply simp  oops

lemma "(i + j + 12 + (k::int)) - 15 = y"
apply simp  oops

lemma "(i + j + 12 + (k::int)) - 5 = y"
apply simp  oops

lemma "y - b < (b::int)"
apply simp  oops

lemma "y - (3*b + c) < (b::int) - 2*c"
apply simp  oops

lemma "(2*x - (u*v) + y) - v*3*u = (w::int)"
apply simp  oops

lemma "(2*x*u*v + (u*v)*4 + y) - v*u*4 = (w::int)"
apply simp  oops

lemma "(2*x*u*v + (u*v)*4 + y) - v*u = (w::int)"
apply simp  oops

lemma "u*v - (x*u*v + (u*v)*4 + y) = (w::int)"
apply simp  oops

lemma "(i + j + 12 + (k::int)) = u + 15 + y"
apply simp  oops

lemma "(i + j*2 + 12 + (k::int)) = j + 5 + y"
apply simp  oops

lemma "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + (vv::int)"
apply simp  oops

lemma "a + -(b+c) + b = (d::int)"
apply simp  oops

lemma "a + -(b+c) - b = (d::int)"
apply simp  oops

(*negative numerals*)
lemma "(i + j + -2 + (k::int)) - (u + 5 + y) = zz"
apply simp  oops

lemma "(i + j + -3 + (k::int)) < u + 5 + y"
apply simp  oops

lemma "(i + j + 3 + (k::int)) < u + -6 + y"
apply simp  oops

lemma "(i + j + -12 + (k::int)) - 15 = y"
apply simp  oops

lemma "(i + j + 12 + (k::int)) - -15 = y"
apply simp  oops

lemma "(i + j + -12 + (k::int)) - -15 = y"
apply simp  oops

lemma "- (2*i) + 3  + (2*i + 4) = (0::int)"
apply simp  oops



subsection {* Arithmetic Method Tests *}


lemma "!!a::int. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d"
by arith

lemma "!!a::int. [| a < b; c < d |] ==> a-d+ 2 <= b+(-c)"
by arith

lemma "!!a::int. [| a < b; c < d |] ==> a+c+ 1 < b+d"
by arith

lemma "!!a::int. [| a <= b; b+b <= c |] ==> a+a <= c"
by arith

lemma "!!a::int. [| a+b <= i+j; a<=b; i<=j |] ==> a+a <= j+j"
by arith

lemma "!!a::int. [| a+b < i+j; a<b; i<j |] ==> a+a - - -1 < j+j - 3"
by arith

lemma "!!a::int. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k"
by arith

lemma "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |]
      ==> a <= l"
by arith

lemma "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |]
      ==> a+a+a+a <= l+l+l+l"
by arith

lemma "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |]
      ==> a+a+a+a+a <= l+l+l+l+i"
by arith

lemma "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |]
      ==> a+a+a+a+a+a <= l+l+l+l+i+l"
by arith

lemma "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |]
      ==> 6*a <= 5*l+i"
by arith



subsection {* The Integers *}

text {* Addition *}

lemma "(13::int) + 19 = 32"
  by simp

lemma "(1234::int) + 5678 = 6912"
  by simp

lemma "(1359::int) + -2468 = -1109"
  by simp

lemma "(93746::int) + -46375 = 47371"
  by simp


text {* \medskip Negation *}

lemma "- (65745::int) = -65745"
  by simp

lemma "- (-54321::int) = 54321"
  by simp


text {* \medskip Multiplication *}

lemma "(13::int) * 19 = 247"
  by simp

lemma "(-84::int) * 51 = -4284"
  by simp

lemma "(255::int) * 255 = 65025"
  by simp

lemma "(1359::int) * -2468 = -3354012"
  by simp

lemma "(89::int) * 10 \<noteq> 889"
  by simp

lemma "(13::int) < 18 - 4"
  by simp

lemma "(-345::int) < -242 + -100"
  by simp

lemma "(13557456::int) < 18678654"
  by simp

lemma "(999999::int) \<le> (1000001 + 1) - 2"
  by simp

lemma "(1234567::int) \<le> 1234567"
  by simp

text{*No integer overflow!*}
lemma "1234567 * (1234567::int) < 1234567*1234567*1234567"
  by simp


text {* \medskip Quotient and Remainder *}

lemma "(10::int) div 3 = 3"
  by simp

lemma "(10::int) mod 3 = 1"
  by simp

text {* A negative divisor *}

lemma "(10::int) div -3 = -4"
  by simp

lemma "(10::int) mod -3 = -2"
  by simp

text {*
  A negative dividend\footnote{The definition agrees with mathematical
  convention and with ML, but not with the hardware of most computers}
*}

lemma "(-10::int) div 3 = -4"
  by simp

lemma "(-10::int) mod 3 = 2"
  by simp

text {* A negative dividend \emph{and} divisor *}

lemma "(-10::int) div -3 = 3"
  by simp

lemma "(-10::int) mod -3 = -1"
  by simp

text {* A few bigger examples *}

lemma "(8452::int) mod 3 = 1"
  by simp

lemma "(59485::int) div 434 = 137"
  by simp

lemma "(1000006::int) mod 10 = 6"
  by simp


text {* \medskip Division by shifting *}

lemma "10000000 div 2 = (5000000::int)"
  by simp

lemma "10000001 mod 2 = (1::int)"
  by simp

lemma "10000055 div 32 = (312501::int)"
  by simp

lemma "10000055 mod 32 = (23::int)"
  by simp

lemma "100094 div 144 = (695::int)"
  by simp

lemma "100094 mod 144 = (14::int)"
  by simp


text {* \medskip Powers *}

lemma "2 ^ 10 = (1024::int)"
  by simp

lemma "-3 ^ 7 = (-2187::int)"
  by simp

lemma "13 ^ 7 = (62748517::int)"
  by simp

lemma "3 ^ 15 = (14348907::int)"
  by simp

lemma "-5 ^ 11 = (-48828125::int)"
  by simp


subsection {* The Natural Numbers *}

text {* Successor *}

lemma "Suc 99999 = 100000"
  by simp


text {* \medskip Addition *}

lemma "(13::nat) + 19 = 32"
  by simp

lemma "(1234::nat) + 5678 = 6912"
  by simp

lemma "(973646::nat) + 6475 = 980121"
  by simp


text {* \medskip Subtraction *}

lemma "(32::nat) - 14 = 18"
  by simp

lemma "(14::nat) - 15 = 0"
  by simp

lemma "(14::nat) - 1576644 = 0"
  by simp

lemma "(48273776::nat) - 3873737 = 44400039"
  by simp


text {* \medskip Multiplication *}

lemma "(12::nat) * 11 = 132"
  by simp

lemma "(647::nat) * 3643 = 2357021"
  by simp


text {* \medskip Quotient and Remainder *}

lemma "(10::nat) div 3 = 3"
  by simp

lemma "(10::nat) mod 3 = 1"
  by simp

lemma "(10000::nat) div 9 = 1111"
  by simp

lemma "(10000::nat) mod 9 = 1"
  by simp

lemma "(10000::nat) div 16 = 625"
  by simp

lemma "(10000::nat) mod 16 = 0"
  by simp


text {* \medskip Powers *}

lemma "2 ^ 12 = (4096::nat)"
  by simp

lemma "3 ^ 10 = (59049::nat)"
  by simp

lemma "12 ^ 7 = (35831808::nat)"
  by simp

lemma "3 ^ 14 = (4782969::nat)"
  by simp

lemma "5 ^ 11 = (48828125::nat)"
  by simp


text {* \medskip Testing the cancellation of complementary terms *}

lemma "y + (x + -x) = (0::int) + y"
  by simp

lemma "y + (-x + (- y + x)) = (0::int)"
  by simp

lemma "-x + (y + (- y + x)) = (0::int)"
  by simp

lemma "x + (x + (- x + (- x + (- y + - z)))) = (0::int) - y - z"
  by simp

lemma "x + x - x - x - y - z = (0::int) - y - z"
  by simp

lemma "x + y + z - (x + z) = y - (0::int)"
  by simp

lemma "x + (y + (y + (y + (-x + -x)))) = (0::int) + y - x + y + y"
  by simp

lemma "x + (y + (y + (y + (-y + -x)))) = y + (0::int) + y"
  by simp

lemma "x + y - x + z - x - y - z + x < (1::int)"
  by simp


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
by linarith

lemma "!!a::real. a < b ==> c < d ==> a - d \<le> b + (-c)"
by linarith

lemma "!!a::real. a \<le> b ==> b + b \<le> c ==> a + a \<le> c"
by linarith

lemma "!!a::real. a + b \<le> i + j ==> a \<le> b ==> i \<le> j ==> a + a \<le> j + j"
by linarith

lemma "!!a::real. a + b < i + j ==> a < b ==> i < j ==> a + a < j + j"
by linarith

lemma "!!a::real. a + b + c \<le> i + j + k \<and> a \<le> b \<and> b \<le> c \<and> i \<le> j \<and> j \<le> k --> a + a + a \<le> k + k + k"
by arith

lemma "!!a::real. a + b + c + d \<le> i + j + k + l ==> a \<le> b ==> b \<le> c
    ==> c \<le> d ==> i \<le> j ==> j \<le> k ==> k \<le> l ==> a \<le> l"
by linarith

lemma "!!a::real. a + b + c + d \<le> i + j + k + l ==> a \<le> b ==> b \<le> c
    ==> c \<le> d ==> i \<le> j ==> j \<le> k ==> k \<le> l ==> a + a + a + a \<le> l + l + l + l"
by linarith

lemma "!!a::real. a + b + c + d \<le> i + j + k + l ==> a \<le> b ==> b \<le> c
    ==> c \<le> d ==> i \<le> j ==> j \<le> k ==> k \<le> l ==> a + a + a + a + a \<le> l + l + l + l + i"
by linarith

lemma "!!a::real. a + b + c + d \<le> i + j + k + l ==> a \<le> b ==> b \<le> c
    ==> c \<le> d ==> i \<le> j ==> j \<le> k ==> k \<le> l ==> a + a + a + a + a + a \<le> l + l + l + l + i + l"
by linarith


subsection{*Complex Arithmetic*}

lemma "(1359 + 93746*ii) - (2468 + 46375*ii) = -1109 + 47371*ii"
by simp

lemma "- (65745 + -47371*ii) = -65745 + 47371*ii"
by simp

text{*Multiplication requires distributive laws.  Perhaps versions instantiated
to literal constants should be added to the simpset.*}

lemma "(1 + ii) * (1 - ii) = 2"
by (simp add: ring_distribs)

lemma "(1 + 2*ii) * (1 + 3*ii) = -5 + 5*ii"
by (simp add: ring_distribs)

lemma "(-84 + 255*ii) + (51 * 255*ii) = -84 + 13260 * ii"
by (simp add: ring_distribs)

text{*No inequalities or linear arithmetic: the complex numbers are unordered!*}

text{*No powers (not supported yet)*}

end
