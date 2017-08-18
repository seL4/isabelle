(*  Title:      HOL/ex/SOS_Cert.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Philipp Meyer, TU Muenchen

Examples for Sum_of_Squares: replay of certificates.
*)

theory SOS_Cert
imports "HOL-Library.Sum_of_Squares"
begin

lemma "(3::real) * x + 7 * a < 4 \<and> 3 < 2 * x \<Longrightarrow> a < 0"
  by (sos "((R<1 + (((A<1 * R<1) * (R<2 * [1]^2)) + (((A<0 * R<1) * (R<3 * [1]^2)) + ((A<=0 * R<1) * (R<14 * [1]^2))))))")

lemma "a1 \<ge> 0 \<and> a2 \<ge> 0 \<and> (a1 * a1 + a2 * a2 = b1 * b1 + b2 * b2 + 2) \<and> (a1 * b1 + a2 * b2 = 0) \<longrightarrow>
    a1 * a2 - b1 * b2 \<ge> (0::real)"
  by (sos "(((A<0 * R<1) + (([~1/2*a1*b2 + ~1/2*a2*b1] * A=0) + (([~1/2*a1*a2 + 1/2*b1*b2] * A=1) + (((A<0 * R<1) * ((R<1/2 * [b2]^2) + (R<1/2 * [b1]^2))) + ((A<=0 * (A<=1 * R<1)) * ((R<1/2 * [b2]^2) + ((R<1/2 * [b1]^2) + ((R<1/2 * [a2]^2) + (R<1/2 * [a1]^2))))))))))")

lemma "(3::real) * x + 7 * a < 4 \<and> 3 < 2 * x \<longrightarrow> a < 0"
  by (sos "((R<1 + (((A<1 * R<1) * (R<2 * [1]^2)) + (((A<0 * R<1) * (R<3 * [1]^2)) + ((A<=0 * R<1) * (R<14 * [1]^2))))))")

lemma "(0::real) \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow>
    x\<^sup>2 + y\<^sup>2 < 1 \<or> (x - 1)\<^sup>2 + y\<^sup>2 < 1 \<or> x\<^sup>2 + (y - 1)\<^sup>2 < 1 \<or> (x - 1)\<^sup>2 + (y - 1)\<^sup>2 < 1"
  by (sos "((R<1 + (((A<=3 * (A<=4 * R<1)) * (R<1 * [1]^2)) + (((A<=2 * (A<=7 * R<1)) * (R<1 * [1]^2)) + (((A<=1 * (A<=6 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=5 * R<1)) * (R<1 * [1]^2)))))))")

lemma "(0::real) \<le> x \<and> 0 \<le> y \<and> 0 \<le> z \<and> x + y + z \<le> 3 \<longrightarrow> x * y + x * z + y * z \<ge> 3 * x * y * z"
  by (sos "(((A<0 * R<1) + (((A<0 * R<1) * (R<1/2 * [1]^2)) + (((A<=2 * R<1) * (R<1/2 * [~1*x + y]^2)) + (((A<=1 * R<1) * (R<1/2 * [~1*x + z]^2)) + (((A<=1 * (A<=2 * (A<=3 * R<1))) * (R<1/2 * [1]^2)) + (((A<=0 * R<1) * (R<1/2 * [~1*y + z]^2)) + (((A<=0 * (A<=2 * (A<=3 * R<1))) * (R<1/2 * [1]^2)) + ((A<=0 * (A<=1 * (A<=3 * R<1))) * (R<1/2 * [1]^2))))))))))")

lemma "(x::real)\<^sup>2 + y\<^sup>2 + z\<^sup>2 = 1 \<longrightarrow> (x + y + z)\<^sup>2 \<le> 3"
  by (sos "(((A<0 * R<1) + (([~3] * A=0) + (R<1 * ((R<2 * [~1/2*x + ~1/2*y + z]^2) + (R<3/2 * [~1*x + y]^2))))))")

lemma "w\<^sup>2 + x\<^sup>2 + y\<^sup>2 + z\<^sup>2 = 1 \<longrightarrow> (w + x + y + z)\<^sup>2 \<le> (4::real)"
  by (sos "(((A<0 * R<1) + (([~4] * A=0) + (R<1 * ((R<3 * [~1/3*w + ~1/3*x + ~1/3*y + z]^2) + ((R<8/3 * [~1/2*w + ~1/2*x + y]^2) + (R<2 * [~1*w + x]^2)))))))")

lemma "(x::real) \<ge> 1 \<and> y \<ge> 1 \<longrightarrow> x * y \<ge> x + y - 1"
  by (sos "(((A<0 * R<1) + ((A<=0 * (A<=1 * R<1)) * (R<1 * [1]^2))))")

lemma "(x::real) > 1 \<and> y > 1 \<longrightarrow> x * y > x + y - 1"
  by (sos "((((A<0 * A<1) * R<1) + ((A<=0 * R<1) * (R<1 * [1]^2))))")

lemma "\<bar>x\<bar> \<le> 1 \<longrightarrow> \<bar>64 * x^7 - 112 * x^5 + 56 * x^3 - 7 * x\<bar> \<le> (1::real)"
  by (sos "((((A<0 * R<1) + ((A<=1 * R<1) * (R<1 * [~8*x^3 + ~4*x^2 + 4*x + 1]^2)))) & ((((A<0 * A<1) * R<1) + ((A<=1 * (A<0 * R<1)) * (R<1 * [8*x^3 + ~4*x^2 + ~4*x + 1]^2)))))")


text \<open>One component of denominator in dodecahedral example.\<close>

lemma "2 \<le> x \<and> x \<le> 125841 / 50000 \<and> 2 \<le> y \<and> y \<le> 125841 / 50000 \<and> 2 \<le> z \<and> z \<le> 125841 / 50000 \<longrightarrow>
    2 * (x * z + x * y + y * z) - (x * x + y * y + z * z) \<ge> (0::real)"
  by (sos "(((A<0 * R<1) + ((R<1 * ((R<5749028157/5000000000 * [~25000/222477*x + ~25000/222477*y + ~25000/222477*z + 1]^2) + ((R<864067/1779816 * [419113/864067*x + 419113/864067*y + z]^2) + ((R<320795/864067 * [419113/1283180*x + y]^2) + (R<1702293/5132720 * [x]^2))))) + (((A<=4 * (A<=5 * R<1)) * (R<3/2 * [1]^2)) + (((A<=3 * (A<=5 * R<1)) * (R<1/2 * [1]^2)) + (((A<=2 * (A<=4 * R<1)) * (R<1 * [1]^2)) + (((A<=2 * (A<=3 * R<1)) * (R<3/2 * [1]^2)) + (((A<=1 * (A<=5 * R<1)) * (R<1/2 * [1]^2)) + (((A<=1 * (A<=3 * R<1)) * (R<1/2 * [1]^2)) + (((A<=0 * (A<=4 * R<1)) * (R<1 * [1]^2)) + (((A<=0 * (A<=2 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<3/2 * [1]^2)))))))))))))")


text \<open>Over a larger but simpler interval.\<close>

lemma "(2::real) \<le> x \<and> x \<le> 4 \<and> 2 \<le> y \<and> y \<le> 4 \<and> 2 \<le> z \<and> z \<le> 4 \<longrightarrow>
    0 \<le> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z)"
  by (sos "((R<1 + ((R<1 * ((R<1 * [~1/6*x + ~1/6*y + ~1/6*z + 1]^2) + ((R<1/18 * [~1/2*x + ~1/2*y + z]^2) + (R<1/24 * [~1*x + y]^2)))) + (((A<0 * R<1) * (R<1/12 * [1]^2)) + (((A<=4 * (A<=5 * R<1)) * (R<1/6 * [1]^2)) + (((A<=2 * (A<=4 * R<1)) * (R<1/6 * [1]^2)) + (((A<=2 * (A<=3 * R<1)) * (R<1/6 * [1]^2)) + (((A<=0 * (A<=4 * R<1)) * (R<1/6 * [1]^2)) + (((A<=0 * (A<=2 * R<1)) * (R<1/6 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<1/6 * [1]^2)))))))))))")


text \<open>We can do 12. I think 12 is a sharp bound; see PP's certificate.\<close>

lemma "2 \<le> (x::real) \<and> x \<le> 4 \<and> 2 \<le> y \<and> y \<le> 4 \<and> 2 \<le> z \<and> z \<le> 4 \<longrightarrow>
    12 \<le> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z)"
  by (sos "(((A<0 * R<1) + (((A<=4 * R<1) * (R<2/3 * [1]^2)) + (((A<=4 * (A<=5 * R<1)) * (R<1 * [1]^2)) + (((A<=3 * (A<=4 * R<1)) * (R<1/3 * [1]^2)) + (((A<=2 * R<1) * (R<2/3 * [1]^2)) + (((A<=2 * (A<=5 * R<1)) * (R<1/3 * [1]^2)) + (((A<=2 * (A<=4 * R<1)) * (R<8/3 * [1]^2)) + (((A<=2 * (A<=3 * R<1)) * (R<1 * [1]^2)) + (((A<=1 * (A<=4 * R<1)) * (R<1/3 * [1]^2)) + (((A<=1 * (A<=2 * R<1)) * (R<1/3 * [1]^2)) + (((A<=0 * R<1) * (R<2/3 * [1]^2)) + (((A<=0 * (A<=5 * R<1)) * (R<1/3 * [1]^2)) + (((A<=0 * (A<=4 * R<1)) * (R<8/3 * [1]^2)) + (((A<=0 * (A<=3 * R<1)) * (R<1/3 * [1]^2)) + (((A<=0 * (A<=2 * R<1)) * (R<8/3 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<1 * [1]^2))))))))))))))))))")


text \<open>Inequality from sci.math (see "Leon-Sotelo, por favor").\<close>

lemma "0 \<le> (x::real) \<and> 0 \<le> y \<and> x * y = 1 \<longrightarrow> x + y \<le> x\<^sup>2 + y\<^sup>2"
  by (sos "(((A<0 * R<1) + (([1] * A=0) + (R<1 * ((R<1 * [~1/2*x + ~1/2*y + 1]^2) + (R<3/4 * [~1*x + y]^2))))))")

lemma "0 \<le> (x::real) \<and> 0 \<le> y \<and> x * y = 1 \<longrightarrow> x * y * (x + y) \<le> x\<^sup>2 + y\<^sup>2"
  by (sos "(((A<0 * R<1) + (([~1*x + ~1*y + 1] * A=0) + (R<1 * ((R<1 * [~1/2*x + ~1/2*y + 1]^2) + (R<3/4 * [~1*x + y]^2))))))")

lemma "0 \<le> (x::real) \<and> 0 \<le> y \<longrightarrow> x * y * (x + y)\<^sup>2 \<le> (x\<^sup>2 + y\<^sup>2)\<^sup>2"
  by (sos "(((A<0 * R<1) + (R<1 * ((R<1 * [~1/2*x^2 + y^2 + ~1/2*x*y]^2) + (R<3/4 * [~1*x^2 + x*y]^2)))))")

lemma "(0::real) \<le> a \<and> 0 \<le> b \<and> 0 \<le> c \<and> c * (2 * a + b)^3 / 27 \<le> x \<longrightarrow> c * a\<^sup>2 * b \<le> x"
  by (sos "(((A<0 * R<1) + (((A<=3 * R<1) * (R<1 * [1]^2)) + (((A<=1 * (A<=2 * R<1)) * (R<1/27 * [~1*a + b]^2)) + ((A<=0 * (A<=2 * R<1)) * (R<8/27 * [~1*a + b]^2))))))")

lemma "(0::real) < x \<longrightarrow> 0 < 1 + x + x\<^sup>2"
  by (sos "((R<1 + ((R<1 * (R<1 * [x]^2)) + (((A<0 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2))))))")

lemma "(0::real) \<le> x \<longrightarrow> 0 < 1 + x + x\<^sup>2"
  by (sos "((R<1 + ((R<1 * (R<1 * [x]^2)) + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2))))))")

lemma "(0::real) < 1 + x\<^sup>2"
  by (sos "((R<1 + ((R<1 * (R<1 * [x]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2)))))")

lemma "(0::real) \<le> 1 + 2 * x + x\<^sup>2"
  by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [x + 1]^2))))")

lemma "(0::real) < 1 + \<bar>x\<bar>"
  by (sos "((R<1 + (((A<=1 * R<1) * (R<1/2 * [1]^2)) + ((A<=0 * R<1) * (R<1/2 * [1]^2)))))")

lemma "(0::real) < 1 + (1 + x)\<^sup>2 * \<bar>x\<bar>"
  by (sos "(((R<1 + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [x + 1]^2))))) & ((R<1 + (((A<0 * R<1) * (R<1 * [x + 1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2))))))")


lemma "\<bar>(1::real) + x\<^sup>2\<bar> = (1::real) + x\<^sup>2"
  by (sos "(() & (((R<1 + ((R<1 * (R<1 * [x]^2)) + ((A<1 * R<1) * (R<1/2 * [1]^2))))) & ((R<1 + ((R<1 * (R<1 * [x]^2)) + ((A<0 * R<1) * (R<1 * [1]^2)))))))")

lemma "(3::real) * x + 7 * a < 4 \<and> 3 < 2 * x \<longrightarrow> a < 0"
  by (sos "((R<1 + (((A<1 * R<1) * (R<2 * [1]^2)) + (((A<0 * R<1) * (R<3 * [1]^2)) + ((A<=0 * R<1) * (R<14 * [1]^2))))))")

lemma "(0::real) < x \<longrightarrow> 1 < y \<longrightarrow> y * x \<le> z \<longrightarrow> x < z"
  by (sos "((((A<0 * A<1) * R<1) + (((A<=1 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2)))))")

lemma "(1::real) < x \<longrightarrow> x\<^sup>2 < y \<longrightarrow> 1 < y"
  by (sos "((((A<0 * A<1) * R<1) + ((R<1 * ((R<1/10 * [~2*x + y + 1]^2) + (R<1/10 * [~1*x + y]^2))) + (((A<1 * R<1) * (R<1/2 * [1]^2)) + (((A<0 * R<1) * (R<1 * [x]^2)) + (((A<=0 * R<1) * ((R<1/10 * [x + 1]^2) + (R<1/10 * [x]^2))) + (((A<=0 * (A<1 * R<1)) * (R<1/5 * [1]^2)) + ((A<=0 * (A<0 * R<1)) * (R<1/5 * [1]^2)))))))))")

lemma "(b::real)\<^sup>2 < 4 * a * c \<longrightarrow> a * x\<^sup>2 + b * x + c \<noteq> 0"
  by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [2*a*x + b]^2))))")

lemma "(b::real)\<^sup>2 < 4 * a * c \<longrightarrow> a * x^2 + b * x + c \<noteq> 0"
  by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [2*a*x + b]^2))))")

lemma "(a::real) * x\<^sup>2 + b * x + c = 0 \<longrightarrow> b\<^sup>2 \<ge> 4 * a * c"
  by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [2*a*x + b]^2))))")

lemma "(0::real) \<le> b \<and> 0 \<le> c \<and> 0 \<le> x \<and> 0 \<le> y \<and> x\<^sup>2 = c \<and> y\<^sup>2 = a\<^sup>2 * c + b \<longrightarrow> a * c \<le> y * x"
  by (sos "(((A<0 * (A<0 * R<1)) + (((A<=2 * (A<=3 * (A<0 * R<1))) * (R<2 * [1]^2)) + ((A<=0 * (A<=1 * R<1)) * (R<1 * [1]^2)))))")

lemma "\<bar>x - z\<bar> \<le> e \<and> \<bar>y - z\<bar> \<le> e \<and> 0 \<le> u \<and> 0 \<le> v \<and> u + v = 1 \<longrightarrow> \<bar>(u * x + v * y) - z\<bar> \<le> (e::real)"
  by (sos "((((A<0 * R<1) + (((A<=3 * (A<=6 * R<1)) * (R<1 * [1]^2)) + ((A<=1 * (A<=5 * R<1)) * (R<1 * [1]^2))))) & ((((A<0 * A<1) * R<1) + (((A<=3 * (A<=5 * (A<0 * R<1))) * (R<1 * [1]^2)) + ((A<=1 * (A<=4 * (A<0 * R<1))) * (R<1 * [1]^2))))))")


lemma "(x::real) - y - 2 * x^4 = 0 \<and> 0 \<le> x \<and> x \<le> 2 \<and> 0 \<le> y \<and> y \<le> 3 \<longrightarrow> y\<^sup>2 - 7 * y - 12 * x + 17 \<ge> 0"
  oops (*Too hard?*)

lemma "(0::real) \<le> x \<longrightarrow> (1 + x + x\<^sup>2) / (1 + x\<^sup>2) \<le> 1 + x"
  by (sos "(((((A<0 * A<1) * R<1) + ((A<=0 * (A<0 * R<1)) * (R<1 * [x]^2)))) & ((R<1 + ((R<1 * (R<1 * [x]^2)) + ((A<0 * R<1) * (R<1 * [1]^2))))))")

lemma "(0::real) \<le> x \<longrightarrow> 1 - x \<le> 1 / (1 + x + x\<^sup>2)"
  by (sos "(((R<1 + (([~4/3] * A=0) + ((R<1 * ((R<1/3 * [3/2*x + 1]^2) + (R<7/12 * [x]^2))) + ((A<=0 * R<1) * (R<1/3 * [1]^2)))))) & (((((A<0 * A<1) * R<1) + ((A<=0 * (A<0 * R<1)) * (R<1 * [x]^2)))) & ((R<1 + ((R<1 * (R<1 * [x]^2)) + (((A<0 * R<1) * (R<1 * [1]^2)) + ((A<=0 * R<1) * (R<1 * [1]^2))))))))")

lemma "(x::real) \<le> 1 / 2 \<longrightarrow> - x - 2 * x\<^sup>2 \<le> - x / (1 - x)"
  by (sos "((((A<0 * A<1) * R<1) + ((A<=0 * (A<0 * R<1)) * (R<1 * [x]^2))))")

lemma "4 * r\<^sup>2 = p\<^sup>2 - 4 * q \<and> r \<ge> (0::real) \<and> x\<^sup>2 + p * x + q = 0 \<longrightarrow> 2 * (x::real) = - p + 2 * r \<or> 2 * x = - p - 2 * r"
  by (sos "((((((A<0 * A<1) * R<1) + ([~4] * A=0))) & ((((A<0 * A<1) * R<1) + ([4] * A=0)))) & (((((A<0 * A<1) * R<1) + ([4] * A=0))) & ((((A<0 * A<1) * R<1) + ([~4] * A=0)))))")

end
