(*  Title:      HOL/ex/SOS.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Philipp Meyer, TU Muenchen

Examples for Sum_of_Squares.
*)

theory SOS
imports "HOL-Library.Sum_of_Squares"
begin

lemma "(3::real) * x + 7 * a < 4 & 3 < 2 * x \<Longrightarrow> a < 0"
  by sos

lemma "a1 \<ge> 0 \<and> a2 \<ge> 0 \<and> (a1 * a1 + a2 * a2 = b1 * b1 + b2 * b2 + 2) \<and> (a1 * b1 + a2 * b2 = 0) \<longrightarrow>
    a1 * a2 - b1 * b2 \<ge> (0::real)"
  by sos

lemma "(3::real) * x + 7 * a < 4 & 3 < 2 * x \<longrightarrow> a < 0"
  by sos

lemma "(0::real) \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow>
    x\<^sup>2 + y\<^sup>2 < 1 \<or> (x - 1)\<^sup>2 + y\<^sup>2 < 1 \<or> x\<^sup>2 + (y - 1)\<^sup>2 < 1 \<or> (x - 1)\<^sup>2 + (y - 1)\<^sup>2 < 1"
  by sos

lemma "(0::real) \<le> x \<and> 0 \<le> y \<and> 0 \<le> z \<and> x + y + z \<le> 3 \<longrightarrow> x * y + x * z + y * z \<ge> 3 * x * y * z"
  by sos

lemma "(x::real)\<^sup>2 + y\<^sup>2 + z\<^sup>2 = 1 \<longrightarrow> (x + y + z)\<^sup>2 \<le> 3"
  by sos

lemma "w\<^sup>2 + x\<^sup>2 + y\<^sup>2 + z\<^sup>2 = 1 \<longrightarrow> (w + x + y + z)\<^sup>2 \<le> (4::real)"
  by sos

lemma "(x::real) \<ge> 1 \<and> y \<ge> 1 \<longrightarrow> x * y \<ge> x + y - 1"
  by sos

lemma "(x::real) > 1 \<and> y > 1 \<longrightarrow> x * y > x + y - 1"
  by sos

lemma "\<bar>x\<bar> \<le> 1 \<longrightarrow> \<bar>64 * x^7 - 112 * x^5 + 56 * x^3 - 7 * x\<bar> \<le> (1::real)"
  by sos


text \<open>One component of denominator in dodecahedral example.\<close>

lemma "2 \<le> x \<and> x \<le> 125841 / 50000 \<and> 2 \<le> y \<and> y \<le> 125841 / 50000 \<and> 2 \<le> z \<and> z \<le> 125841 / 50000 \<longrightarrow>
    2 * (x * z + x * y + y * z) - (x * x + y * y + z * z) \<ge> (0::real)"
  by sos


text \<open>Over a larger but simpler interval.\<close>

lemma "(2::real) \<le> x \<and> x \<le> 4 \<and> 2 \<le> y \<and> y \<le> 4 \<and> 2 \<le> z \<and> z \<le> 4 \<longrightarrow>
    0 \<le> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z)"
  by sos


text \<open>We can do 12. I think 12 is a sharp bound; see PP's certificate.\<close>

lemma "2 \<le> (x::real) \<and> x \<le> 4 \<and> 2 \<le> y \<and> y \<le> 4 \<and> 2 \<le> z \<and> z \<le> 4 \<longrightarrow>
    12 \<le> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z)"
  by sos


text \<open>Inequality from sci.math (see "Leon-Sotelo, por favor").\<close>

lemma "0 \<le> (x::real) \<and> 0 \<le> y \<and> x * y = 1 \<longrightarrow> x + y \<le> x\<^sup>2 + y\<^sup>2"
  by sos

lemma "0 \<le> (x::real) \<and> 0 \<le> y \<and> x * y = 1 \<longrightarrow> x * y * (x + y) \<le> x\<^sup>2 + y\<^sup>2"
  by sos

lemma "0 \<le> (x::real) \<and> 0 \<le> y \<longrightarrow> x * y * (x + y)\<^sup>2 \<le> (x\<^sup>2 + y\<^sup>2)\<^sup>2"
  by sos

lemma "(0::real) \<le> a \<and> 0 \<le> b \<and> 0 \<le> c \<and> c * (2 * a + b)^3 / 27 \<le> x \<longrightarrow> c * a\<^sup>2 * b \<le> x"
  by sos

lemma "(0::real) < x \<longrightarrow> 0 < 1 + x + x\<^sup>2"
  by sos

lemma "(0::real) \<le> x \<longrightarrow> 0 < 1 + x + x\<^sup>2"
  by sos

lemma "(0::real) < 1 + x\<^sup>2"
  by sos

lemma "(0::real) \<le> 1 + 2 * x + x\<^sup>2"
  by sos

lemma "(0::real) < 1 + \<bar>x\<bar>"
  by sos

lemma "(0::real) < 1 + (1 + x)\<^sup>2 * \<bar>x\<bar>"
  by sos


lemma "\<bar>(1::real) + x\<^sup>2\<bar> = (1::real) + x\<^sup>2"
  by sos

lemma "(3::real) * x + 7 * a < 4 \<and> 3 < 2 * x \<longrightarrow> a < 0"
  by sos

lemma "(0::real) < x \<longrightarrow> 1 < y \<longrightarrow> y * x \<le> z \<longrightarrow> x < z"
  by sos

lemma "(1::real) < x \<longrightarrow> x\<^sup>2 < y \<longrightarrow> 1 < y"
  by sos

lemma "(b::real)\<^sup>2 < 4 * a * c \<longrightarrow> a * x\<^sup>2 + b * x + c \<noteq> 0"
  by sos

lemma "(b::real)\<^sup>2 < 4 * a * c \<longrightarrow> a * x\<^sup>2 + b * x + c \<noteq> 0"
  by sos

lemma "(a::real) * x\<^sup>2 + b * x + c = 0 \<longrightarrow> b\<^sup>2 \<ge> 4 * a * c"
  by sos

lemma "(0::real) \<le> b \<and> 0 \<le> c \<and> 0 \<le> x \<and> 0 \<le> y \<and> x\<^sup>2 = c \<and> y\<^sup>2 = a\<^sup>2 * c + b \<longrightarrow> a * c \<le> y * x"
  by sos

lemma "\<bar>x - z\<bar> \<le> e \<and> \<bar>y - z\<bar> \<le> e \<and> 0 \<le> u \<and> 0 \<le> v \<and> u + v = 1 --> \<bar>(u * x + v * y) - z\<bar> \<le> (e::real)"
  by sos

lemma "(x::real) - y - 2 * x^4 = 0 \<and> 0 \<le> x \<and> x \<le> 2 \<and> 0 \<le> y \<and> y \<le> 3 \<longrightarrow> y\<^sup>2 - 7 * y - 12 * x + 17 \<ge> 0"
  oops (*Too hard?*)

lemma "(0::real) \<le> x \<longrightarrow> (1 + x + x\<^sup>2) / (1 + x\<^sup>2) \<le> 1 + x"
  by sos

lemma "(0::real) \<le> x \<longrightarrow> 1 - x \<le> 1 / (1 + x + x\<^sup>2)"
  by sos

lemma "(x::real) \<le> 1 / 2 \<longrightarrow> - x - 2 * x\<^sup>2 \<le> - x / (1 - x)"
  by sos

lemma "4 * r\<^sup>2 = p\<^sup>2 - 4 * q \<and> r \<ge> (0::real) \<and> x\<^sup>2 + p * x + q = 0 \<longrightarrow>
    2 * (x::real) = - p + 2 * r \<or> 2 * x = - p - 2 * r"
  by sos

end
