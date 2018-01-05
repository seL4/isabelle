(*  Title:      HOL/Decision_Procs/ex/Commutative_Ring_Ex.thy
    Author:     Bernhard Haeupler, Stefan Berghofer
*)

section \<open>Some examples demonstrating the ring and field methods\<close>

theory Commutative_Ring_Ex
  imports "../Reflective_Field"
begin

lemma "4 * (x::int) ^ 5 * y ^ 3 * x ^ 2 * 3 + x * z + 3 ^ 5 = 12 * x ^ 7 * y ^ 3 + z * x + 243"
  by ring

lemma (in cring)
  assumes "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R"
  shows "\<guillemotleft>4\<guillemotright> \<otimes> x [^] (5::nat) \<otimes> y [^] (3::nat) \<otimes> x [^] (2::nat) \<otimes> \<guillemotleft>3\<guillemotright> \<oplus> x \<otimes> z \<oplus> \<guillemotleft>3\<guillemotright> [^] (5::nat) =
    \<guillemotleft>12\<guillemotright> \<otimes> x [^] (7::nat) \<otimes> y [^] (3::nat) \<oplus> z \<otimes> x \<oplus> \<guillemotleft>243\<guillemotright>"
  by ring

lemma "((x::int) + y) ^ 2  = x ^ 2 + y ^ 2 + 2 * x * y"
  by ring

lemma (in cring)
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "(x \<oplus> y) [^] (2::nat)  = x [^] (2::nat) \<oplus> y [^] (2::nat) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> x \<otimes> y"
  by ring

lemma "((x::int) + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * x ^ 2 * y + 3 * y ^ 2 * x"
  by ring

lemma (in cring)
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "(x \<oplus> y) [^] (3::nat) =
    x [^] (3::nat) \<oplus> y [^] (3::nat) \<oplus> \<guillemotleft>3\<guillemotright> \<otimes> x [^] (2::nat) \<otimes> y \<oplus> \<guillemotleft>3\<guillemotright> \<otimes> y [^] (2::nat) \<otimes> x"
  by ring

lemma "((x::int) - y) ^ 3 = x ^ 3 + 3 * x * y ^ 2 + (- 3) * y * x ^ 2 - y ^ 3"
  by ring

lemma (in cring)
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "(x \<ominus> y) [^] (3::nat) =
    x [^] (3::nat) \<oplus> \<guillemotleft>3\<guillemotright> \<otimes> x \<otimes> y [^] (2::nat) \<oplus> (\<ominus> \<guillemotleft>3\<guillemotright>) \<otimes> y \<otimes> x [^] (2::nat) \<ominus> y [^] (3::nat)"
  by ring

lemma "((x::int) - y) ^ 2 = x ^ 2 + y ^ 2 - 2 * x * y"
  by ring

lemma (in cring)
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "(x \<ominus> y) [^] (2::nat) = x [^] (2::nat) \<oplus> y [^] (2::nat) \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> x \<otimes> y"
  by ring

lemma " ((a::int) + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * b * c + 2 * a * c"
  by ring

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows " (a \<oplus> b \<oplus> c) [^] (2::nat) =
    a [^] (2::nat) \<oplus> b [^] (2::nat) \<oplus> c [^] (2::nat) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> a \<otimes> b \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b \<otimes> c \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> a \<otimes> c"
  by ring

lemma "((a::int) - b - c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 - 2 * a * b + 2 * b * c - 2 * a * c"
  by ring

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "(a \<ominus> b \<ominus> c) [^] (2::nat) =
    a [^] (2::nat) \<oplus> b [^] (2::nat) \<oplus> c [^] (2::nat) \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> a \<otimes> b \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b \<otimes> c \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> a \<otimes> c"
  by ring

lemma "(a::int) * b + a * c = a * (b + c)"
  by ring

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "a \<otimes> b \<oplus> a \<otimes> c = a \<otimes> (b \<oplus> c)"
  by ring

lemma "(a::int) ^ 2 - b ^ 2 = (a - b) * (a + b)"
  by ring

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a [^] (2::nat) \<ominus> b [^] (2::nat) = (a \<ominus> b) \<otimes> (a \<oplus> b)"
  by ring

lemma "(a::int) ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2)"
  by ring

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a [^] (3::nat) \<ominus> b [^] (3::nat) = (a \<ominus> b) \<otimes> (a [^] (2::nat) \<oplus> a \<otimes> b \<oplus> b [^] (2::nat))"
  by ring

lemma "(a::int) ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2)"
  by ring

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a [^] (3::nat) \<oplus> b [^] (3::nat) = (a \<oplus> b) \<otimes> (a [^] (2::nat) \<ominus> a \<otimes> b \<oplus> b [^] (2::nat))"
  by ring

lemma "(a::int) ^ 4 - b ^ 4 = (a - b) * (a + b) * (a ^ 2 + b ^ 2)"
  by ring

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a [^] (4::nat) \<ominus> b [^] (4::nat) = (a \<ominus> b) \<otimes> (a \<oplus> b) \<otimes> (a [^] (2::nat) \<oplus> b [^] (2::nat))"
  by ring

lemma "(a::int) ^ 10 - b ^ 10 =
  (a - b) * (a ^ 9 + a ^ 8 * b + a ^ 7 * b ^ 2 + a ^ 6 * b ^ 3 + a ^ 5 * b ^ 4 +
    a ^ 4 * b ^ 5 + a ^ 3 * b ^ 6 + a ^ 2 * b ^ 7 + a * b ^ 8 + b ^ 9)"
  by ring

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a [^] (10::nat) \<ominus> b [^] (10::nat) =
  (a \<ominus> b) \<otimes> (a [^] (9::nat) \<oplus> a [^] (8::nat) \<otimes> b \<oplus> a [^] (7::nat) \<otimes> b [^] (2::nat) \<oplus>
    a [^] (6::nat) \<otimes> b [^] (3::nat) \<oplus> a [^] (5::nat) \<otimes> b [^] (4::nat) \<oplus>
    a [^] (4::nat) \<otimes> b [^] (5::nat) \<oplus> a [^] (3::nat) \<otimes> b [^] (6::nat) \<oplus>
    a [^] (2::nat) \<otimes> b [^] (7::nat) \<oplus> a \<otimes> b [^] (8::nat) \<oplus> b [^] (9::nat))"
  by ring

lemma "(x::'a::field) \<noteq> 0 \<Longrightarrow> (1 - 1 / x) * x - x + 1 = 0"
  by field

lemma (in field)
  assumes "x \<in> carrier R"
  shows "x \<noteq> \<zero> \<Longrightarrow> (\<one> \<ominus> \<one> \<oslash> x) \<otimes> x \<ominus> x \<oplus> \<one> = \<zero>"
  by field

end
