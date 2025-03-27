(* Title:      HOL/Try0.thy
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen
*)

theory Try0
  imports Pure
  keywords "try0" :: diag
begin

ML_file \<open>Tools/try0.ML\<close>
ML_file \<open>Tools/try0_util.ML\<close>

ML \<open>
val () =
  Try0.register_proof_method "simp" {run_if_auto_try = true}
    (Try0_Util.apply_raw_named_method "simp" false Try0_Util.simp_attrs Simplifier_Trace.disable)
  handle Symtab.DUP _ => ()
\<close>

end