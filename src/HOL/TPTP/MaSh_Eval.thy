(*  Title:      HOL/TPTP/MaSh_Eval.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Evaluation Driver *}

theory MaSh_Eval
imports Complex_Main
begin

ML_file "mash_eval.ML"

sledgehammer_params
  [provers = spass, max_relevant = 32, strict, dont_slice, type_enc = mono_native,
   lam_trans = combs_and_lifting, timeout = 15, dont_preplay, minimize]

declare [[sledgehammer_instantiate_inducts]]

ML {*
open MaSh_Eval
*}

ML {*
val do_it = false (* switch to "true" to generate the files *)
val params = Sledgehammer_Isar.default_params @{context} []
*}

ML {*
if do_it then
  evaluate_mash_suggestions @{context} params "/tmp/mash_suggestions"
      "/tmp/mash_eval.out"
else
  ()
*}

end
