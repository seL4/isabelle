(*  Title:      HOL/Nitpick_Examples/Integer_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick applied to natural numbers and integers.
*)

header {* Examples Featuring Nitpick Applied to Natural Numbers and Integers *} 

theory Integer_Nits
imports Nitpick
begin

nitpick_params [verbose, card = 1\<emdash>5, bits = 1,2,3,4,6,
                sat_solver = MiniSat_JNI, max_threads = 1, timeout = 240]

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
nitpick [binary_ints, card = 1\<emdash>4, bits = 1\<emdash>4, expect = none]
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

datatype tree = Null | Node nat tree tree

primrec labels where
"labels Null = {}" |
"labels (Node x t u) = {x} \<union> labels t \<union> labels u"

lemma "labels (Node x t u) \<noteq> labels (Node y v w)"
nitpick [expect = potential] (* unfortunate *)
nitpick [dont_finitize, expect = potential]
oops

lemma "labels (Node x t u) \<noteq> {}"
nitpick [expect = none]
oops

lemma "card (labels t) > 0"
nitpick [expect = potential] (* unfortunate *)
nitpick [dont_finitize, expect = potential]
oops

lemma "(\<Sum>n \<in> labels t. n + 2) \<ge> 2"
nitpick [expect = potential] (* unfortunate *)
nitpick [dont_finitize, expect = potential]
oops

lemma "t \<noteq> Null \<Longrightarrow> (\<Sum>n \<in> labels t. n + 2) \<ge> 2"
nitpick [expect = potential] (* unfortunate *)
nitpick [dont_finitize, expect = potential]
sorry

lemma "(\<Sum>i \<in> labels (Node x t u). f i\<Colon>nat) = f x + (\<Sum>i \<in> labels t. f i) + (\<Sum>i \<in> labels u. f i)"
nitpick [expect = potential] (* unfortunate *)
nitpick [dont_finitize, expect = potential]
oops

end
