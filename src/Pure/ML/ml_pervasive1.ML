(*  Title:      Pure/ML/ml_pervasive1.ML
    Author:     Makarius

Pervasive ML environment: final setup.
*)

if Options.default_bool "ML_system_bootstrap" then ()
else
  (List.app ML_Name_Space.forget_structure
    (remove (op =) "PolyML" ML_Name_Space.bootstrap_structures);
   ML \<open>structure PolyML = struct structure IntInf = PolyML.IntInf end\<close>);

Proofterm.proofs := 0;

Context.set_thread_data NONE;
