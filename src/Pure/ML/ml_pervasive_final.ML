(*  Title:      Pure/ML/ml_pervasive_final.ML
    Author:     Makarius

Pervasive ML environment: final setup.
*)

if Options.default_bool "ML_system_unsafe" then ()
else
 (List.app ML_Name_Space.forget_structure (remove (op =) "PolyML" ML_Name_Space.excluded_structures);
  ML \<open>structure PolyML = struct structure IntInf = PolyML.IntInf end\<close>);

structure Output: OUTPUT = Output;  (*seal system channels!*)

Proofterm.proofs := 0;

Context.set_thread_data NONE;
