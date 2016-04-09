(*  Title:      Pure/ML/ml_pervasive1.ML
    Author:     Makarius

Pervasive ML environment: final setup.
*)

List.app ML_Name_Space.forget_structure ML_Name_Space.hidden_structures;

structure PolyML = struct structure IntInf = PolyML.IntInf end;

Proofterm.proofs := 0;

Context.put_generic_context NONE;

val use = ML_file;
