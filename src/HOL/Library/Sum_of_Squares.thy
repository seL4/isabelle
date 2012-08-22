(*  Title:      HOL/Library/Sum_of_Squares.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Philipp Meyer, TU Muenchen
*)

header {* A decision method for universal multivariate real arithmetic with addition, 
  multiplication and ordering using semidefinite programming *}

theory Sum_of_Squares
imports Complex_Main
begin

ML_file "positivstellensatz.ML"
ML_file "Sum_of_Squares/sum_of_squares.ML"
ML_file "Sum_of_Squares/positivstellensatz_tools.ML"
ML_file "Sum_of_Squares/sos_wrapper.ML"

text {*
  Proof method sos invocations:
  \begin{itemize}

  \item remote solver: @{text "(sos remote_csdp)"}

  \item local solver: @{text "(sos csdp)"}

  The latter requires a local executable from
  https://projects.coin-or.org/Csdp and the Isabelle settings variable
  variable @{text ISABELLE_CSDP} pointing to it.

  \end{itemize}

  By default, method sos calls @{text remote_csdp}.  This can take of
  the order of a minute for one sos call, because sos calls CSDP
  repeatedly.  If you install CSDP locally, sos calls typically takes
  only a few seconds.

  The sos method generates a certificate which can be used to repeat
  the proof without calling an external prover.
*}

setup SOS_Wrapper.setup

text {* Tests *}

lemma "(3::real) * x + 7 * a < 4 & 3 < 2 * x \<Longrightarrow> a < 0"
by (sos_cert "((R<1 + (((A<1 * R<1) * (R<2 * [1]^2)) + (((A<0 * R<1) * (R<3 * [1]^2)) + ((A<=0 * R<1) * (R<14 * [1]^2))))))")

lemma "a1 >= 0 & a2 >= 0 \<and> (a1 * a1 + a2 * a2 = b1 * b1 + b2 * b2 + 2) \<and> (a1 * b1 + a2 * b2 = 0) --> a1 * a2 - b1 * b2 >= (0::real)"
by (sos_cert "(((A<0 * R<1) + (([~1/2*a1*b2 + ~1/2*a2*b1] * A=0) + (([~1/2*a1*a2 + 1/2*b1*b2] * A=1) + (((A<0 * R<1) * ((R<1/2 * [b2]^2) + (R<1/2 * [b1]^2))) + ((A<=0 * (A<=1 * R<1)) * ((R<1/2 * [b2]^2) + ((R<1/2 * [b1]^2) + ((R<1/2 * [a2]^2) + (R<1/2 * [a1]^2))))))))))")

lemma "(3::real) * x + 7 * a < 4 & 3 < 2 * x --> a < 0"
by (sos_cert "((R<1 + (((A<1 * R<1) * (R<2 * [1]^2)) + (((A<0 * R<1) * (R<3 * [1]^2)) + ((A<=0 * R<1) * (R<14 * [1]^2))))))")

lemma "(0::real) <= x & x <= 1 & 0 <= y & y <= 1  --> x^2 + y^2 < 1 |(x - 1)^2 + y^2 < 1 | x^2 + (y - 1)^2 < 1 | (x - 1)^2 + (y - 1)^2 < 1"
by (sos_cert "((R<1 + (((A<=3 * (A<=4 * R<1)) * (R<1 * [1]^2)) + (((A<=2 * (A<=7 * R<1)) * (R<1 * [1]^2)) + (((A<=1 * (A<=6 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=5 * R<1)) * (R<1 * [1]^2)))))))")

lemma "(0::real) <= x & 0 <= y & 0 <= z & x + y + z <= 3 --> x * y + x * z + y * z >= 3 * x * y * z"
by (sos_cert "(((A<0 * R<1) + (((A<0 * R<1) * (R<1/2 * [1]^2)) + (((A<=2 * R<1) * (R<1/2 * [~1*x + y]^2)) + (((A<=1 * R<1) * (R<1/2 * [~1*x + z]^2)) + (((A<=1 * (A<=2 * (A<=3 * R<1))) * (R<1/2 * [1]^2)) + (((A<=0 * R<1) * (R<1/2 * [~1*y + z]^2)) + (((A<=0 * (A<=2 * (A<=3 * R<1))) * (R<1/2 * [1]^2)) + ((A<=0 * (A<=1 * (A<=3 * R<1))) * (R<1/2 * [1]^2))))))))))")

lemma "((x::real)^2 + y^2 + z^2 = 1) --> (x + y + z)^2 <= 3"
by (sos_cert "(((A<0 * R<1) + (([~3] * A=0) + (R<1 * ((R<2 * [~1/2*x + ~1/2*y + z]^2) + (R<3/2 * [~1*x + y]^2))))))")

lemma "(w^2 + x^2 + y^2 + z^2 = 1) --> (w + x + y + z)^2 <= (4::real)"
by (sos_cert "(((A<0 * R<1) + (([~4] * A=0) + (R<1 * ((R<3 * [~1/3*w + ~1/3*x + ~1/3*y + z]^2) + ((R<8/3 * [~1/2*w + ~1/2*x + y]^2) + (R<2 * [~1*w + x]^2)))))))")

lemma "(x::real) >= 1 & y >= 1 --> x * y >= x + y - 1"
by (sos_cert "(((A<0 * R<1) + ((A<=0 * (A<=1 * R<1)) * (R<1 * [1]^2))))")

lemma "(x::real) > 1 & y > 1 --> x * y > x + y - 1"
by (sos_cert "((((A<0 * A<1) * R<1) + ((A<=0 * R<1) * (R<1 * [1]^2))))") 

lemma "abs(x) <= 1 --> abs(64 * x^7 - 112 * x^5 + 56 * x^3 - 7 * x) <= (1::real)"
by (sos_cert "((((A<0 * R<1) + ((A<=1 * R<1) * (R<1 * [~8*x^3 + ~4*x^2 + 4*x + 1]^2)))) & ((((A<0 * A<1) * R<1) + ((A<=1 * (A<0 * R<1)) * (R<1 * [8*x^3 + ~4*x^2 + ~4*x + 1]^2)))))")

(* ------------------------------------------------------------------------- *)
(* One component of denominator in dodecahedral example.                     *)
(* ------------------------------------------------------------------------- *)

lemma "2 <= x & x <= 125841 / 50000 & 2 <= y & y <= 125841 / 50000 & 2 <= z & z <= 125841 / 50000 --> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z) >= (0::real)"
by (sos_cert "(((A<0 * R<1) + ((R<1 * ((R<5749028157/5000000000 * [~25000/222477*x + ~25000/222477*y + ~25000/222477*z + 1]^2) + ((R<864067/1779816 * [419113/864067*x + 419113/864067*y + z]^2) + ((R<320795/864067 * [419113/1283180*x + y]^2) + (R<1702293/5132720 * [x]^2))))) + (((A<=4 * (A<=5 * R<1)) * (R<3/2 * [1]^2)) + (((A<=3 * (A<=5 * R<1)) * (R<1/2 * [1]^2)) + (((A<=2 * (A<=4 * R<1)) * (R<1 * [1]^2)) + (((A<=2 * (A<=3 * R<1)) * (R<3/2 * [1]^2)) + (((A<=1 * (A<=5 * R<1)) * (R<1/2 * [1]^2)) + (((A<=1 * (A<=3 * R<1)) * (R<1/2 * [1]^2)) + (((A<=0 * (A<=4 * R<1)) * (R<1 * [1]^2)) + (((A<=0 * (A<=2 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<3/2 * [1]^2)))))))))))))")

(* ------------------------------------------------------------------------- *)
(* Over a larger but simpler interval.                                       *)
(* ------------------------------------------------------------------------- *)

lemma "(2::real) <= x & x <= 4 & 2 <= y & y <= 4 & 2 <= z & z <= 4 --> 0 <= 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z)"
by (sos_cert "((R<1 + ((R<1 * ((R<1 * [~1/6*x + ~1/6*y + ~1/6*z + 1]^2) + ((R<1/18 * [~1/2*x + ~1/2*y + z]^2) + (R<1/24 * [~1*x + y]^2)))) + (((A<0 * R<1) * (R<1/12 * [1]^2)) + (((A<=4 * (A<=5 * R<1)) * (R<1/6 * [1]^2)) + (((A<=2 * (A<=4 * R<1)) * (R<1/6 * [1]^2)) + (((A<=2 * (A<=3 * R<1)) * (R<1/6 * [1]^2)) + (((A<=0 * (A<=4 * R<1)) * (R<1/6 * [1]^2)) + (((A<=0 * (A<=2 * R<1)) * (R<1/6 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<1/6 * [1]^2)))))))))))")

(* ------------------------------------------------------------------------- *)
(* We can do 12. I think 12 is a sharp bound; see PP's certificate.          *)
(* ------------------------------------------------------------------------- *)

lemma "2 <= (x::real) & x <= 4 & 2 <= y & y <= 4 & 2 <= z & z <= 4 --> 12 <= 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z)"
by (sos_cert "(((A<0 * R<1) + (((A<=4 * R<1) * (R<2/3 * [1]^2)) + (((A<=4 * (A<=5 * R<1)) * (R<1 * [1]^2)) + (((A<=3 * (A<=4 * R<1)) * (R<1/3 * [1]^2)) + (((A<=2 * R<1) * (R<2/3 * [1]^2)) + (((A<=2 * (A<=5 * R<1)) * (R<1/3 * [1]^2)) + (((A<=2 * (A<=4 * R<1)) * (R<8/3 * [1]^2)) + (((A<=2 * (A<=3 * R<1)) * (R<1 * [1]^2)) + (((A<=1 * (A<=4 * R<1)) * (R<1/3 * [1]^2)) + (((A<=1 * (A<=2 * R<1)) * (R<1/3 * [1]^2)) + (((A<=0 * R<1) * (R<2/3 * [1]^2)) + (((A<=0 * (A<=5 * R<1)) * (R<1/3 * [1]^2)) + (((A<=0 * (A<=4 * R<1)) * (R<8/3 * [1]^2)) + (((A<=0 * (A<=3 * R<1)) * (R<1/3 * [1]^2)) + (((A<=0 * (A<=2 * R<1)) * (R<8/3 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<1 * [1]^2))))))))))))))))))")

(* ------------------------------------------------------------------------- *)
(* Inequality from sci.math (see "Leon-Sotelo, por favor").                  *)
(* ------------------------------------------------------------------------- *)

lemma "0 <= (x::real) & 0 <= y & (x * y = 1) --> x + y <= x^2 + y^2"
by (sos_cert "(((A<0 * R<1) + (([1] * A=0) + (R<1 * ((R<1 * [~1/2*x + ~1/2*y + 1]^2) + (R<3/4 * [~1*x + y]^2))))))") 

lemma "0 <= (x::real) & 0 <= y & (x * y = 1) --> x * y * (x + y) <= x^2 + y^2"
by (sos_cert "(((A<0 * R<1) + (([~1*x + ~1*y + 1] * A=0) + (R<1 * ((R<1 * [~1/2*x + ~1/2*y + 1]^2) + (R<3/4 * [~1*x + y]^2))))))") 

lemma "0 <= (x::real) & 0 <= y --> x * y * (x + y)^2 <= (x^2 + y^2)^2"
by (sos_cert "(((A<0 * R<1) + (R<1 * ((R<1 * [~1/2*x^2 + y^2 + ~1/2*x*y]^2) + (R<3/4 * [~1*x^2 + x*y]^2)))))")

lemma "(0::real) <= a & 0 <= b & 0 <= c & c * (2 * a + b)^3/ 27 <= x \<longrightarrow> c * a^2 * b <= x"
by (sos_cert "(((A<0 * R<1) + (((A<=3 * R<1) * (R<1 * [1]^2)) + (((A<=1 * (A<=2 * R<1)) * (R<1/27 * [~1*a + b]^2)) + ((A<=0 * (A<=2 * R<1)) * (R<8/27 * [~1*a + b]^2))))))")
 
lemma "(0::real) < x --> 0 < 1 + x + x^2"
by (sos_cert "((R<1 + ((R<1 * (R<1 * [x]^2)) + (((A<0 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2))))))")

lemma "(0::real) <= x --> 0 < 1 + x + x^2"
by (sos_cert "((R<1 + ((R<1 * (R<1 * [x]^2)) + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2))))))")

lemma "(0::real) < 1 + x^2"
by (sos_cert "((R<1 + ((R<1 * (R<1 * [x]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2)))))")

lemma "(0::real) <= 1 + 2 * x + x^2"
by (sos_cert "(((A<0 * R<1) + (R<1 * (R<1 * [x + 1]^2))))")

lemma "(0::real) < 1 + abs x"
by (sos_cert "((R<1 + (((A<=1 * R<1) * (R<1/2 * [1]^2)) + ((A<=0 * R<1) * (R<1/2 * [1]^2)))))")

lemma "(0::real) < 1 + (1 + x)^2 * (abs x)"
by (sos_cert "(((R<1 + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [x + 1]^2))))) & ((R<1 + (((A<0 * R<1) * (R<1 * [x + 1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2))))))")



lemma "abs ((1::real) + x^2) = (1::real) + x^2"
by (sos_cert "(() & (((R<1 + ((R<1 * (R<1 * [x]^2)) + ((A<1 * R<1) * (R<1/2 * [1]^2))))) & ((R<1 + ((R<1 * (R<1 * [x]^2)) + ((A<0 * R<1) * (R<1 * [1]^2)))))))")
lemma "(3::real) * x + 7 * a < 4 \<and> 3 < 2 * x \<longrightarrow> a < 0"
by (sos_cert "((R<1 + (((A<1 * R<1) * (R<2 * [1]^2)) + (((A<0 * R<1) * (R<3 * [1]^2)) + ((A<=0 * R<1) * (R<14 * [1]^2))))))")

lemma "(0::real) < x --> 1 < y --> y * x <= z --> x < z"
by (sos_cert "((((A<0 * A<1) * R<1) + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2)))))")
lemma "(1::real) < x --> x^2 < y --> 1 < y"
by (sos_cert "((((A<0 * A<1) * R<1) + ((R<1 * ((R<1/10 * [~2*x + y + 1]^2) + (R<1/10 * [~1*x + y]^2))) + (((A<1 * R<1) * (R<1/2 * [1]^2)) + (((A<0 * R<1) * (R<1 * [x]^2)) + (((A<=0 * R<1) * ((R<1/10 * [x + 1]^2) + (R<1/10 * [x]^2))) + (((A<=0 * (A<1 * R<1)) * (R<1/5 * [1]^2)) + ((A<=0 * (A<0 * R<1)) * (R<1/5 * [1]^2)))))))))")
lemma "(b::real)^2 < 4 * a * c --> ~(a * x^2 + b * x + c = 0)"
by (sos_cert "(((A<0 * R<1) + (R<1 * (R<1 * [2*a*x + b]^2))))")
lemma "(b::real)^2 < 4 * a * c --> ~(a * x^2 + b * x + c = 0)"
by (sos_cert "(((A<0 * R<1) + (R<1 * (R<1 * [2*a*x + b]^2))))")
lemma "((a::real) * x^2 + b * x + c = 0) --> b^2 >= 4 * a * c"
by (sos_cert "(((A<0 * R<1) + (R<1 * (R<1 * [2*a*x + b]^2))))")
lemma "(0::real) <= b & 0 <= c & 0 <= x & 0 <= y & (x^2 = c) & (y^2 = a^2 * c + b) --> a * c <= y * x"
by (sos_cert "(((A<0 * (A<0 * R<1)) + (((A<=2 * (A<=3 * (A<0 * R<1))) * (R<2 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<1 * [1]^2)))))")
lemma "abs(x - z) <= e & abs(y - z) <= e & 0 <= u & 0 <= v & (u + v = 1) --> abs((u * x + v * y) - z) <= (e::real)"
by (sos_cert "((((A<0 * R<1) + (((A<=3 * (A<=6 * R<1)) * (R<1 * [1]^2)) + ((A<=1 * (A<=5 * R<1)) * (R<1 * [1]^2))))) & ((((A<0 * A<1) * R<1) + (((A<=3 * (A<=5 * (A<0 * R<1))) * (R<1 * [1]^2)) + ((A<=1 * (A<=4 * (A<0 * R<1))) * (R<1 * [1]^2))))))")


(* lemma "((x::real) - y - 2 * x^4 = 0) & 0 <= x & x <= 2 & 0 <= y & y <= 3 --> y^2 - 7 * y - 12 * x + 17 >= 0" by sos *) (* Too hard?*)

lemma "(0::real) <= x --> (1 + x + x^2)/(1 + x^2) <= 1 + x"
by (sos_cert "(((((A<0 * A<1) * R<1) + ((A<=0 * (A<0 * R<1)) * (R<1 * [x]^2)))) & ((R<1 + ((R<1 * (R<1 * [x]^2)) + ((A<0 * R<1) * (R<1 * [1]^2))))))")

lemma "(0::real) <= x --> 1 - x <= 1 / (1 + x + x^2)"
by (sos_cert "(((R<1 + (([~4/3] * A=0) + ((R<1 * ((R<1/3 * [3/2*x + 1]^2) + (R<7/12 * [x]^2))) + ((A<=0 * R<1) * (R<1/3 * [1]^2)))))) & (((((A<0 * A<1) * R<1) + ((A<=0 * (A<0 * R<1)) * (R<1 * [x]^2)))) & ((R<1 + ((R<1 * (R<1 * [x]^2)) + (((A<0 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2))))))))")

lemma "(x::real) <= 1 / 2 --> - x - 2 * x^2 <= - x / (1 - x)"
by (sos_cert "((((A<0 * A<1) * R<1) + ((A<=0 * (A<0 * R<1)) * (R<1 * [x]^2))))")

lemma "4*r^2 = p^2 - 4*q & r >= (0::real) & x^2 + p*x + q = 0 --> 2*(x::real) = - p + 2*r | 2*x = -p - 2*r"
by (sos_cert "((((((A<0 * A<1) * R<1) + ([~4] * A=0))) & ((((A<0 * A<1) * R<1) + ([4] * A=0)))) & (((((A<0 * A<1) * R<1) + ([4] * A=0))) & ((((A<0 * A<1) * R<1) + ([~4] * A=0)))))")

end
