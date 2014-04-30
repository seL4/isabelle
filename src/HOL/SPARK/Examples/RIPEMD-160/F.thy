(*  Title:      HOL/SPARK/Examples/RIPEMD-160/F.thy
    Author:     Fabian Immler, TU Muenchen

Verification of the RIPEMD-160 hash function
*)

theory F
imports RMD_Specification
begin

spark_open "rmd/f"

spark_vc function_f_2
  using assms by simp_all

spark_vc function_f_3
  using assms by simp_all

spark_vc function_f_4
  using assms by simp_all

spark_vc function_f_5
  using assms by simp_all

spark_vc function_f_6
proof -
  from H8 have "nat j <= 15" by simp
  with assms show ?thesis
    by (simp add: f_def bwsimps int_word_uint int_mod_eq')
qed

spark_vc function_f_7
proof -
  from H7 have "16 <= nat j" by simp
  moreover from H8 have "nat j <= 31" by simp
  ultimately show ?thesis using assms
    by (simp add: f_def bwsimps int_word_uint int_mod_eq')
qed

spark_vc function_f_8
proof -
  from H7 have "32 <= nat j" by simp
  moreover from H8 have "nat j <= 47" by simp
  ultimately show ?thesis using assms
    by (simp add: f_def bwsimps int_word_uint int_mod_eq')
qed

spark_vc function_f_9
proof -
  from H7 have "48 <= nat j" by simp
  moreover from H8 have   "nat j <= 63" by simp
  ultimately show ?thesis using assms
    by (simp add: f_def bwsimps int_word_uint int_mod_eq')
qed

spark_vc function_f_10
proof -
  from H2 have "nat j <= 79" by simp
  moreover from H12 have "64 <= nat j" by simp
  ultimately show ?thesis using assms
    by (simp add: f_def bwsimps int_word_uint int_mod_eq')
qed

spark_end

end
