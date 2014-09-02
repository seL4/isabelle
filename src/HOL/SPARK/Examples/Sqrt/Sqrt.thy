(*  Title:      HOL/SPARK/Examples/Sqrt/Sqrt.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG
*)

theory Sqrt
imports "../../SPARK"
begin

spark_open "sqrt/isqrt"

spark_vc function_isqrt_4
proof -
  from `0 \<le> r` have "(r = 0 \<or> r = 1 \<or> r = 2) \<or> 2 < r" by auto
  then show "2 * r \<le> 2147483646"
  proof
    assume "2 < r"
    then have "0 < r" by simp
    with `2 < r` have "2 * r < r * r" by (rule mult_strict_right_mono)
    with `r * r \<le> n` and `n \<le> 2147483647` show ?thesis
      by simp
  qed auto
  then show "2 * r \<le> 2147483647" by simp
qed

spark_end

end
