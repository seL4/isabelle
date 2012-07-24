(* Author:     Johannes Hoelzl <hoelzl@in.tum.de> 2009 *)

theory Approximation_Ex
imports Complex_Main "../Approximation"
begin

text {*

Here are some examples how to use the approximation method.

The approximation method has the following syntax:

approximate "prec" (splitting: "x" = "depth" and "y" = "depth" ...)? (taylor: "z" = "derivates")?

Here "prec" specifies the precision used in all computations, it is specified as
number of bits to calculate. In the proposition to prove an arbitrary amount of
variables can be used, but each one need to be bounded by an upper and lower
bound.

To specify the bounds either @{term "l\<^isub>1 \<le> x \<and> x \<le> u\<^isub>1"},
@{term "x \<in> { l\<^isub>1 .. u\<^isub>1 }"} or @{term "x = bnd"} can be used. Where the
bound specification are again arithmetic formulas containing variables. They can
be connected using either meta level or HOL equivalence.

To use interval splitting add for each variable whos interval should be splitted
to the "splitting:" parameter. The parameter specifies how often each interval
should be divided, e.g. when x = 16 is specified, there will be @{term "65536 = 2^16"}
intervals to be calculated.

To use taylor series expansion specify the variable to derive. You need to
specify the amount of derivations to compute. When using taylor series expansion
only one variable can be used.

*}

section "Compute some transcendental values"

lemma "\<bar> ln 2 - 544531980202654583340825686620847 / 785593587443817081832229725798400 \<bar> < inverse (2^51) "
  by (approximation 60)

lemma "\<bar> exp 1.626 - 5.083499996273 \<bar> < (inverse 10 ^ 10 :: real)"
  by (approximation 40)

lemma "\<bar> sqrt 2 - 1.4142135623730951 \<bar> < inverse 10 ^ 16"
  by (approximation 60)

lemma "\<bar> pi - 3.1415926535897932385 \<bar> < inverse 10 ^ 18"
  by (approximation 70)

lemma "\<bar> sin 100 + 0.50636564110975879 \<bar> < inverse 10 ^ 17"
  by (approximation 70)

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
  using assms by (approximation 20)

lemma "x \<in> { 0 .. 1 :: real } \<longrightarrow> x ^ 2 \<le> x"
  by (approximation 30 splitting: x=1 taylor: x = 3)

value [approximate] "10"

end
