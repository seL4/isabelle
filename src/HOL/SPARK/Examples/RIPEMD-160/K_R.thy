(*  Title:      HOL/SPARK/Examples/RIPEMD-160/K_R.thy
    Author:     Fabian Immler, TU Muenchen

Verification of the RIPEMD-160 hash function
*)

theory K_R
imports RMD_Specification
begin

spark_open "rmd/k_r"

spark_vc function_k_r_6
  using assms by (simp add: K'_def)

spark_vc function_k_r_7
proof-
  from H1 have "16 <= nat j" by simp
  moreover from H2 have "nat j <= 31" by simp
  ultimately show ?thesis by (simp add: K'_def)
qed

spark_vc function_k_r_8
proof -
  from H1 have "32 <= nat j" by simp
  moreover from H2 have "nat j <= 47" by simp
  ultimately show ?thesis by (simp add: K'_def)
qed

spark_vc function_k_r_9
proof -
  from H1 have "48 <= nat j" by simp
  moreover from H2 have "nat j <= 63" by simp
  ultimately show ?thesis by (simp add: K'_def)
qed

spark_vc function_k_r_10
proof -
  from H6 have "64 <= nat j" by simp
  moreover from H2 have "nat j <= 79" by simp
  ultimately show ?thesis by (simp add: K'_def)
qed

spark_end

end
