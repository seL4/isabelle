(*  Title:      HOL/SPARK/Examples/RIPEMD-160/S_R.thy
    Author:     Fabian Immler, TU Muenchen

Verification of the RIPEMD-160 hash function
*)

theory S_R
imports RMD_Specification RMD_Lemmas
begin

spark_open "rmd/s_r"

spark_vc function_s_r_2
proof -
  from `0 \<le> j` `j \<le> 79`
  show C: ?C1
    by (simp add: s'_def s'_list_def nth_map [symmetric, of _ _ int] del: fun_upd_apply)
      (simp add: nth_fun_of_list_eq [of _ _ undefined] del: fun_upd_apply)
  from C show ?C2 by simp
  have "list_all (\<lambda>n. int n \<le> 15) s'_list"
    by (simp add: s'_list_def)
  moreover have "length s'_list = 80"
    by (simp add: s'_list_def)
  ultimately show ?C3 unfolding C using `j \<le> 79`
    by (simp add: s'_def list_all_length)
qed

spark_end

end