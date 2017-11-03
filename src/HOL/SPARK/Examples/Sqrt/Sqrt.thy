(*  Title:      HOL/SPARK/Examples/Sqrt/Sqrt.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG
*)

theory Sqrt
imports "HOL-SPARK.SPARK"
begin

spark_open "sqrt/isqrt"

spark_vc function_isqrt_4
proof -
  from \<open>0 \<le> r\<close> have "(r = 0 \<or> r = 1 \<or> r = 2) \<or> 2 < r" by auto
  then show "2 * r \<le> 2147483646"
  proof
    assume "2 < r"
    then have "0 < r" by simp
    with \<open>2 < r\<close> have "2 * r < r * r" by (rule mult_strict_right_mono)
    with \<open>r * r \<le> n\<close> and \<open>n \<le> 2147483647\<close> show ?thesis
      by simp
  qed auto
  then show "2 * r \<le> 2147483647" by simp
qed

spark_end

end
