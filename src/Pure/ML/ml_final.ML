(*  Title:      Pure/ML/ml_final.ML
    Author:     Makarius

Final setup of ML environment.
*)

if Options.default_bool "ML_system_unsafe" then ()
else
  (List.app ML_Name_Space.forget_structure
    ["CInterface", "Foreign", "RunCall", "RuntimeCalls", "Signal"];
   ML \<open>structure PolyML = struct structure IntInf = PolyML.IntInf end\<close>);

structure Output: OUTPUT = Output;  (*seal system channels!*)

structure Pure = struct val thy = Thy_Info.pure_theory () end;

Proofterm.proofs := 0;

Context.set_thread_data NONE;
