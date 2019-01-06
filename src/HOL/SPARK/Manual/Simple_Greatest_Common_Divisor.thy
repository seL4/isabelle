(*  Title:      HOL/SPARK/Manual/Simple_Greatest_Common_Divisor.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG
*)

theory Simple_Greatest_Common_Divisor
imports "HOL-SPARK.SPARK"
begin

spark_proof_functions
  gcd = "gcd :: int \<Rightarrow> int \<Rightarrow> int"

spark_open \<open>simple_greatest_common_divisor/g_c_d\<close>

spark_vc procedure_g_c_d_4
  using \<open>0 < d\<close> \<open>gcd c d = gcd m n\<close>
  by (simp add: gcd_non_0_int)

spark_vc procedure_g_c_d_9
  using \<open>0 \<le> c\<close> \<open>gcd c 0 = gcd m n\<close>
  by simp

spark_end

end
