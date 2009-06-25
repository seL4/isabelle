(* Author:     Johannes Hoelzl <hoelzl@in.tum.de> 2009 *)

theory Approximation_Ex
imports Complex_Main "~~/src/HOL/Decision_Procs/Approximation"
begin

text {*

Here are some examples how to use the approximation method.

The parameter passed to the method specifies the precision used by the computations, it is specified
as number of bits to calculate. When a variable is used it needs to be bounded by an interval. This
interval is specified as a conjunction of the lower and upper bound. It must have the form
@{text "\<lbrakk> l\<^isub>1 \<le> x\<^isub>1 \<and> x\<^isub>1 \<le> u\<^isub>1 ; \<dots> ; l\<^isub>n \<le> x\<^isub>n \<and> x\<^isub>n \<le> u\<^isub>n \<rbrakk> \<Longrightarrow> F"} where @{term F} is the formula, and
@{text "x\<^isub>1, \<dots>, x\<^isub>n"} are the variables. The lower bounds @{text "l\<^isub>1, \<dots>, l\<^isub>n"} and the upper bounds
@{text "u\<^isub>1, \<dots>, u\<^isub>n"} must either be integer numerals, floating point numbers or of the form
@{term "m * pow2 e"} to specify a exact floating point value.

*}

section "Compute some transcendental values"

lemma "\<bar> ln 2 - 544531980202654583340825686620847 / 785593587443817081832229725798400 \<bar> < inverse (2^51) "
  by (approximation 80)

lemma "\<bar> exp 1.626 - 5.083499996273 \<bar> < (inverse 10 ^ 10 :: real)"
  by (approximation 80)

lemma "\<bar> sqrt 2 - 1.4142135623730951 \<bar> < inverse 10 ^ 16"
  by (approximation 80)

lemma "\<bar> pi - 3.1415926535897932385 \<bar> < inverse 10 ^ 18"
  by (approximation 80)

lemma "\<bar> sin 100 + 0.50636564110975879 \<bar> < inverse 10 ^ 17"
  by (approximation 80)

section "Use variable ranges"

lemma "0.5 \<le> x \<and> x \<le> 4.5 \<Longrightarrow> \<bar> arctan x - 0.91 \<bar> < 0.455"
  by (approximation 10)

lemma "x \<in> {0.5 .. 4.5} \<longrightarrow> \<bar> arctan x - 0.91 \<bar> < 0.455"
  by (approximation 10)

lemma "0.49 \<le> x \<and> x \<le> 4.49 \<Longrightarrow> \<bar> arctan x - 0.91 \<bar> < 0.455"
  by (approximation 20)

lemma "1 / 2^1 \<le> x \<and> x \<le> 9 / 2^1 \<Longrightarrow> \<bar> arctan x - 0.91 \<bar> < 0.455"
  by (approximation 10)

lemma "3.2 \<le> x \<and> x \<le> 6.2 \<Longrightarrow> sin x \<le> 0"
  by (approximation 9)

lemma
  defines "g \<equiv> 9.80665" and "v \<equiv> 128.61" and "d \<equiv> pi / 180"
  shows "g / v * tan (35 * d) \<in> { 3 * d .. 3.1 * d }"
  using assms by (approximation 80)

end
