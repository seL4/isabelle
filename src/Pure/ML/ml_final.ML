(*  Title:      Pure/ML/ml_final.ML
    Author:     Makarius

Final setup of ML environment.
*)

(*no access to system internals!*)
structure PolyML = struct structure IntInf = PolyML.IntInf end;
val _ = List.app ML_Name_Space.forget_structure ML_Name_Space.critical_structures;

structure Output: OUTPUT = Output;  (*seal system channels!*)

structure Pure = struct val thy = Thy_Info.pure_theory () end;

Proofterm.proofs := 0;

Context.set_thread_data NONE;
