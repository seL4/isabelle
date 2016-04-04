(*  Title:      Pure/ML/ml_final.ML
    Author:     Makarius

Final setup of ML environment.
*)

(*no access to system internals!*)
structure PolyML = struct structure IntInf = PolyML.IntInf end;
val _ = List.app ML_Name_Space.forget_structure ML_Name_Space.critical_structures;

structure Output: OUTPUT = Output;  (*seal system channels!*)

structure Pure = struct val thy = Thy_Info.pure_theory () end;

fun use_thys args =
  Runtime.toplevel_program (fn () => Thy_Info.use_thys (map (rpair Position.none) args));
val use_thy = use_thys o single;

Proofterm.proofs := 0;

Context.set_thread_data NONE;
