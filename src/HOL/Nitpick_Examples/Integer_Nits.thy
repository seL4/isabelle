(*  Title:      HOL/Nitpick_Examples/Integer_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009

Examples featuring Nitpick applied to natural numbers and integers.
*)

header {* Examples Featuring Nitpick Applied to Natural Numbers and Integers *} 

theory Integer_Nits
imports Nitpick
begin

nitpick_params [sat_solver = MiniSatJNI, max_threads = 1, timeout = 60 s,
                card = 1\<midarrow>6, bits = 1,2,3,4,6,8]

lemma "Suc x = x + 1"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x < Suc x"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x + y \<ge> (x::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "y \<noteq> 0 \<Longrightarrow> x + y > (x::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x + y = y + (x::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x > y \<Longrightarrow> x - y \<noteq> (0::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x \<le> y \<Longrightarrow> x - y = (0::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x - (0::nat) = x"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<noteq> (0::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "0 * y = (0::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "y * 0 = (0::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<ge> (x::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<ge> (y::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x * y div y = (x::nat)"
nitpick [unary_ints, expect = genuine]
nitpick [binary_ints, expect = genuine]
oops

lemma "y \<noteq> 0 \<Longrightarrow> x * y div y = (x::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "5 * 55 < (260::nat)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
nitpick [binary_ints, bits = 9, expect = genuine]
oops

lemma "nat (of_nat n) = n"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x + y \<ge> (x::int)"
nitpick [unary_ints, expect = genuine]
nitpick [binary_ints, expect = genuine]
oops

lemma "\<lbrakk>x \<ge> 0; y \<ge> 0\<rbrakk> \<Longrightarrow> x + y \<ge> (0::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "y \<ge> 0 \<Longrightarrow> x + y \<ge> (x::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x \<ge> 0 \<Longrightarrow> x + y \<ge> (y::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x \<ge> 0 \<Longrightarrow> x + y \<ge> (x::int)"
nitpick [unary_ints, expect = genuine]
nitpick [binary_ints, expect = genuine]
oops

lemma "\<lbrakk>x \<le> 0; y \<le> 0\<rbrakk> \<Longrightarrow> x + y \<le> (0::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "y \<noteq> 0 \<Longrightarrow> x + y > (x::int)"
nitpick [unary_ints, expect = genuine]
nitpick [binary_ints, expect = genuine]
oops

lemma "x + y = y + (x::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x > y \<Longrightarrow> x - y \<noteq> (0::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "x \<le> y \<Longrightarrow> x - y = (0::int)"
nitpick [unary_ints, expect = genuine]
nitpick [binary_ints, expect = genuine]
oops

lemma "x - (0::int) = x"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<noteq> (0::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "0 * y = (0::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "y * 0 = (0::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<ge> (x::int)"
nitpick [unary_ints, expect = genuine]
nitpick [binary_ints, expect = genuine]
oops

lemma "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> x * y \<ge> (y::int)"
nitpick [unary_ints, expect = genuine]
nitpick [binary_ints, expect = genuine]
oops

lemma "x * y div y = (x::int)"
nitpick [unary_ints, expect = genuine]
nitpick [binary_ints, expect = genuine]
oops

lemma "y \<noteq> 0 \<Longrightarrow> x * y div y = (x::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none, card = 1\<midarrow>5, bits = 1\<midarrow>5]
sorry

lemma "(x * y < 0) \<longleftrightarrow> (x > 0 \<and> y < 0) \<or> (x < 0 \<and> y > (0::int))"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

lemma "-5 * 55 > (-260::int)"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
nitpick [binary_ints, bits = 9, expect = genuine]
oops

lemma "nat (of_nat n) = n"
nitpick [unary_ints, expect = none]
nitpick [binary_ints, expect = none]
sorry

end
