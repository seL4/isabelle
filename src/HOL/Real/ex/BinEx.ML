(*  Title:      HOL/Real/ex/BinEx.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Examples of performing binary arithmetic by simplification
This time we use the reals, though the representation is just of integers.
*)

(*** Addition ***)

Goal "(#1359::real)  +  #-2468 = #-1109";
by (Simp_tac 1);
qed "";

Goal "(#93746::real) +  #-46375 = #47371";
by (Simp_tac 1);
qed "";

(*** Negation ***)

Goal "- (#65745::real) = #-65745";
by (Simp_tac 1);
qed "";

Goal "- (#-54321::real) = #54321";
by (Simp_tac 1);
qed "";


(*** Multiplication ***)

Goal "(#-84::real)  *  #51 = #-4284";
by (Simp_tac 1);
qed "";

Goal "(#255::real)  *  #255 = #65025";
by (Simp_tac 1);
qed "";

Goal "(#1359::real)  *  #-2468 = #-3354012";
by (Simp_tac 1);
qed "";

(*** Inequalities ***)

Goal "(#89::real) * #10 ~= #889";  
by (Simp_tac 1); 
qed "";

Goal "(#13::real) < #18 - #4";  
by (Simp_tac 1); 
qed "";

Goal "(#-345::real) < #-242 + #-100";  
by (Simp_tac 1); 
qed "";

Goal "(#13557456::real) < #18678654";  
by (Simp_tac 1); 
qed "";

Goal "(#999999::real) <= (#1000001 + #1)-#2";  
by (Simp_tac 1); 
qed "";

Goal "(#1234567::real) <= #1234567";  
by (Simp_tac 1); 
qed "";

(** Tests **)
Goal "(x + y = x) = (y = (#0::real))";
by(arith_tac 1);

Goal "(x + y = y) = (x = (#0::real))";
by(arith_tac 1);

Goal "(x + y = (#0::real)) = (x = -y)";
by(arith_tac 1);

Goal "(x + y = (#0::real)) = (y = -x)";
by(arith_tac 1);

Goal "((x + y) < (x + z)) = (y < (z::real))";
by(arith_tac 1);

Goal "((x + z) < (y + z)) = (x < (y::real))";
by(arith_tac 1);

Goal "(~ x < y) = (y <= (x::real))";
by(arith_tac 1);

Goal "~(x < y & y < (x::real))";
by(arith_tac 1);

Goal "(x::real) < y ==> ~ y < x";
by(arith_tac 1);

Goal "((x::real) ~= y) = (x < y | y < x)";
by(arith_tac 1);

Goal "(~ x <= y) = (y < (x::real))";
by(arith_tac 1);

Goal "x <= y | y <= (x::real)";
by(arith_tac 1);

Goal "x <= y | y < (x::real)";
by(arith_tac 1);

Goal "x < y | y <= (x::real)";
by(arith_tac 1);

Goal "x <= (x::real)";
by(arith_tac 1);

Goal "((x::real) <= y) = (x < y | x = y)";
by(arith_tac 1);

Goal "((x::real) <= y & y <= x) = (x = y)";
by(arith_tac 1);

Goal "~(x < y & y <= (x::real))";
by(arith_tac 1);

Goal "~(x <= y & y < (x::real))";
by(arith_tac 1);

Goal "(-x < (#0::real)) = (#0 < x)";
by(arith_tac 1);

Goal "((#0::real) < -x) = (x < #0)";
by(arith_tac 1);

Goal "(-x <= (#0::real)) = (#0 <= x)";
by(arith_tac 1);

Goal "((#0::real) <= -x) = (x <= #0)";
by(arith_tac 1);

Goal "(x::real) = y | x < y | y < x";
by(arith_tac 1);

Goal "(x::real) = #0 | #0 < x | #0 < -x";
by(arith_tac 1);

Goal "(#0::real) <= x | #0 <= -x";
by(arith_tac 1);

Goal "((x::real) + y <= x + z) = (y <= z)";
by(arith_tac 1);

Goal "((x::real) + z <= y + z) = (x <= y)";
by(arith_tac 1);

Goal "(w::real) < x & y < z ==> w + y < x + z";
by(arith_tac 1);

Goal "(w::real) <= x & y <= z ==> w + y <= x + z";
by(arith_tac 1);

Goal "(#0::real) <= x & #0 <= y ==> #0 <= x + y";
by(arith_tac 1);

Goal "(#0::real) < x & #0 < y ==> #0 < x + y";
by(arith_tac 1);

Goal "(-x < y) = (#0 < x + (y::real))";
by(arith_tac 1);

Goal "(x < -y) = (x + y < (#0::real))";
by(arith_tac 1);

Goal "(y < x + -z) = (y + z < (x::real))";
by(arith_tac 1);

Goal "(x + -y < z) = (x < z + (y::real))";
by(arith_tac 1);

Goal "x <= y ==> x < y + (#1::real)";
by(arith_tac 1);

Goal "(x - y) + y = (x::real)";
by(arith_tac 1);

Goal "y + (x - y) = (x::real)";
by(arith_tac 1);

Goal "x - x = (#0::real)";
by(arith_tac 1);

Goal "(x - y = #0) = (x = (y::real))";
by(arith_tac 1);

Goal "((#0::real) <= x + x) = (#0 <= x)";
by(arith_tac 1);

Goal "(-x <= x) = ((#0::real) <= x)";
by(arith_tac 1);

Goal "(x <= -x) = (x <= (#0::real))";
by(arith_tac 1);

Goal "(-x = (#0::real)) = (x = #0)";
by(arith_tac 1);

Goal "-(x - y) = y - (x::real)";
by(arith_tac 1);

Goal "((#0::real) < x - y) = (y < x)";
by(arith_tac 1);

Goal "((#0::real) <= x - y) = (y <= x)";
by(arith_tac 1);

Goal "(x + y) - x = (y::real)";
by(arith_tac 1);

Goal "(-x = y) = (x = (-y::real))";
by(arith_tac 1);

Goal "x < (y::real) ==> ~(x = y)";
by(arith_tac 1);

Goal "(x <= x + y) = ((#0::real) <= y)";
by(arith_tac 1);

Goal "(y <= x + y) = ((#0::real) <= x)";
by(arith_tac 1);

Goal "(x < x + y) = ((#0::real) < y)";
by(arith_tac 1);

Goal "(y < x + y) = ((#0::real) < x)";
by(arith_tac 1);

Goal "(x - y) - x = (-y::real)";
by(arith_tac 1);

Goal "(x + y < z) = (x < z - (y::real))";
by(arith_tac 1);

Goal "(x - y < z) = (x < z + (y::real))";
by(arith_tac 1);

Goal "(x < y - z) = (x + z < (y::real))";
by(arith_tac 1);

Goal "(x <= y - z) = (x + z <= (y::real))";
by(arith_tac 1);

Goal "(x - y <= z) = (x <= z + (y::real))";
by(arith_tac 1);

Goal "(-x < -y) = (y < (x::real))";
by(arith_tac 1);

Goal "(-x <= -y) = (y <= (x::real))";
by(arith_tac 1);

Goal "(a + b) - (c + d) = (a - c) + (b - (d::real))";
by(arith_tac 1);

Goal "(#0::real) - x = -x";
by(arith_tac 1);

Goal "x - (#0::real) = x";
by(arith_tac 1);

Goal "w <= x & y < z ==> w + y < x + (z::real)";
by(arith_tac 1);

Goal "w < x & y <= z ==> w + y < x + (z::real)";
by(arith_tac 1);

Goal "(#0::real) <= x & #0 < y ==> #0 < x + (y::real)";
by(arith_tac 1);

Goal "(#0::real) < x & #0 <= y ==> #0 < x + y";
by(arith_tac 1);

Goal "-x - y = -(x + (y::real))";
by(arith_tac 1);

Goal "x - (-y) = x + (y::real)";
by(arith_tac 1);

Goal "-x - -y = y - (x::real)";
by(arith_tac 1);

Goal "(a - b) + (b - c) = a - (c::real)";
by(arith_tac 1);

Goal "(x = y - z) = (x + z = (y::real))";
by(arith_tac 1);

Goal "(x - y = z) = (x = z + (y::real))";
by(arith_tac 1);

Goal "x - (x - y) = (y::real)";
by(arith_tac 1);

Goal "x - (x + y) = -(y::real)";
by(arith_tac 1);

Goal "x = y ==> x <= (y::real)";
by(arith_tac 1);

Goal "(#0::real) < x ==> ~(x = #0)";
by(arith_tac 1);

Goal "(x + y) * (x - y) = (x * x) - (y * y)";

Goal "(-x = -y) = (x = (y::real))";
by(arith_tac 1);

Goal "(-x < -y) = (y < (x::real))";
by(arith_tac 1);

Goal "!!a::real. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);

Goal "!!a::real. [| a < b; c < d |] ==> a-d <= b+(-c)";
by (fast_arith_tac 1);

Goal "!!a::real. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);

Goal "!!a::real. [| a+b <= i+j; a<=b; i<=j |] \
\     ==> a+a <= j+j";
by (fast_arith_tac 1);

Goal "!!a::real. [| a+b < i+j; a<b; i<j |] \
\     ==> a+a < j+j";
by (fast_arith_tac 1);

Goal "!!a::real. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);

(* Too slow. Needs "combine_coefficients" simproc
Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);

Goal "!!a::real. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
*)

