theory Proc2
imports "HOL-SPARK.SPARK"
begin

spark_open "loop_invariant/proc2"

spark_vc procedure_proc2_7
  by (simp add: ring_distribs mod_simps)

spark_end

end
