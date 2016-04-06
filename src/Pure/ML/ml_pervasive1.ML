(*  Title:      Pure/ML/ml_pervasive1.ML
    Author:     Makarius

Pervasive ML environment: final setup.
*)

List.app ML_Name_Space.forget_structure
  (remove (op =) "PolyML" ML_Name_Space.bootstrap_structures);

structure PolyML = struct structure IntInf = PolyML.IntInf end;

Proofterm.proofs := 0;

Context.set_thread_data NONE;
