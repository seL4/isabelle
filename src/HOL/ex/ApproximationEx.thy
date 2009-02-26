(*  Title:      HOL/ex/ApproximationEx.thy
    Author:     Johannes Hoelzl <hoelzl@in.tum.de> 2009
*)

theory ApproximationEx
imports "~~/src/HOL/Reflection/Approximation"
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

section "Use variable ranges"

lemma "0.5 \<le> x \<and> x \<le> 4.5 \<Longrightarrow> \<bar> arctan x - 0.91 \<bar> < 0.455"
  by (approximation 10)

lemma "0 \<le> x \<and> x \<le> 1 \<Longrightarrow> 0 \<le> sin x"
  by (approximation 10)


end

