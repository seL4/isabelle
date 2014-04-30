(*  Title:      HOL/SPARK/Examples/Gcd/Greatest_Common_Divisor.thy
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG
*)

theory Greatest_Common_Divisor
imports SPARK GCD
begin

spark_proof_functions
  gcd = "gcd :: int \<Rightarrow> int \<Rightarrow> int"

spark_open "greatest_common_divisor/g_c_d"

spark_vc procedure_g_c_d_4
proof -
  from `0 < d` have "0 \<le> c mod d" by (rule pos_mod_sign)
  with `0 \<le> c` `0 < d` `c - c sdiv d * d \<noteq> 0` show ?C1
    by (simp add: sdiv_pos_pos zmod_zdiv_equality')
next
  from `0 \<le> c` `0 < d` `gcd c d = gcd m n` show ?C2
    by (simp add: sdiv_pos_pos zmod_zdiv_equality' gcd_non_0_int)
qed

spark_vc procedure_g_c_d_11
proof -
  from `0 \<le> c` `0 < d` `c - c sdiv d * d = 0`
  have "d dvd c"
    by (auto simp add: sdiv_pos_pos dvd_def mult_ac)
  with `0 < d` `gcd c d = gcd m n` show ?C1
    by simp
qed

spark_end

end
