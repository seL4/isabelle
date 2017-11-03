(*  Title:      HOL/SPARK/Examples/Gcd/Greatest_Common_Divisor.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG
*)

theory Greatest_Common_Divisor
imports "HOL-SPARK.SPARK"
begin

spark_proof_functions
  gcd = "gcd :: int \<Rightarrow> int \<Rightarrow> int"

spark_open "greatest_common_divisor/g_c_d"

spark_vc procedure_g_c_d_4
proof -
  from \<open>0 < d\<close> have "0 \<le> c mod d" by (rule pos_mod_sign)
  with \<open>0 \<le> c\<close> \<open>0 < d\<close> \<open>c - c sdiv d * d \<noteq> 0\<close> show ?C1
    by (simp add: sdiv_pos_pos minus_div_mult_eq_mod [symmetric])
next
  from \<open>0 \<le> c\<close> \<open>0 < d\<close> \<open>gcd c d = gcd m n\<close> show ?C2
    by (simp add: sdiv_pos_pos minus_div_mult_eq_mod [symmetric] gcd_non_0_int)
qed

spark_vc procedure_g_c_d_11
proof -
  from \<open>0 \<le> c\<close> \<open>0 < d\<close> \<open>c - c sdiv d * d = 0\<close>
  have "d dvd c"
    by (auto simp add: sdiv_pos_pos dvd_def ac_simps)
  with \<open>0 < d\<close> \<open>gcd c d = gcd m n\<close> show ?C1
    by simp
qed

spark_end

end
