theory Proc1
imports SPARK
begin

spark_open "loop_invariant/proc1.siv"

spark_vc procedure_proc1_5
  by (simp add: ring_distribs pull_mods)

spark_vc procedure_proc1_8
  by (simp add: ring_distribs pull_mods)

spark_end

lemma pow_2_32_simp: "4294967296 = (2::int)^32"
  by simp

end
