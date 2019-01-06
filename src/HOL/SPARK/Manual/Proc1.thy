theory Proc1
imports "HOL-SPARK.SPARK"
begin

spark_open \<open>loop_invariant/proc1\<close>

spark_vc procedure_proc1_5
  by (simp add: ring_distribs mod_simps)

spark_vc procedure_proc1_8
  by (simp add: ring_distribs mod_simps)

spark_end

lemma pow_2_32_simp: "4294967296 = (2::int)^32"
  by simp

end
