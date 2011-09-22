theory Proc2
imports SPARK
begin

spark_open "loop_invariant/proc2.siv"

spark_vc procedure_proc2_7
  by (simp add: ring_distribs pull_mods)

spark_end

end
