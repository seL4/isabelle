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
!Multithreading.max_threads
*}

ML {*
open MaSh_Eval
*}

ML {*
val do_it = false (* switch to "true" to generate the files *)
val params = Sledgehammer_Isar.default_params @{context} []
val dir = "List"
val prefix = "/tmp/" ^ dir ^ "/"
val prob_dir = prefix ^ "mash_problems"
*}

ML {*
if do_it then
  Isabelle_System.mkdir (Path.explode prob_dir)
else
  ()
*}

ML {*
if do_it then
  evaluate_mash_suggestions @{context} params (SOME prob_dir)
      (prefix ^ "mash_suggestions") (prefix ^ "/tmp/mash_eval.out")
else
  ()
*}

end
