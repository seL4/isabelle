(*  Title:      HOL/SPARK/Manual/Greatest_Common_Divisor.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG
*)

theory Simple_Greatest_Common_Divisor
imports SPARK GCD
begin

spark_proof_functions
  gcd = "gcd :: int \<Rightarrow> int \<Rightarrow> int"

spark_open "simple_greatest_common_divisor/g_c_d.siv"

spark_vc procedure_g_c_d_4
  using `0 < d` `gcd c d = gcd m n`
  by (simp add: gcd_non_0_int)

spark_vc procedure_g_c_d_9
  using `0 \<le> c` `gcd c 0 = gcd m n`
  by simp

spark_end

end
