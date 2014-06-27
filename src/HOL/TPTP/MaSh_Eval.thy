(*  Title:      HOL/TPTP/MaSh_Eval.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Evaluation Driver *}

theory MaSh_Eval
imports Complex_Main
begin

ML_file "mash_eval.ML"

sledgehammer_params
  [provers = spass, max_facts = 32, strict, dont_slice, type_enc = mono_native,
   lam_trans = lifting, timeout = 15, dont_preplay, minimize]

declare [[sledgehammer_fact_duplicates = true]]
declare [[sledgehammer_instantiate_inducts = false]]

ML {*
Multithreading.max_threads_value ()
*}

ML {*
open MaSh_Eval
*}

ML {*
val do_it = false (* switch to "true" to generate the files *)
val params = Sledgehammer_Commands.default_params @{theory} []
val range = (1, NONE)
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
  evaluate_mash_suggestions @{context} params range
      [MePoN, MaSh_IsarN, MaSh_ProverN, MeSh_IsarN, MeSh_ProverN, IsarN]
      (SOME prob_dir)
      (prefix ^ "mepo_suggestions")
      (prefix ^ "mash_suggestions")
      (prefix ^ "mash_prover_suggestions")
      (prefix ^ "mesh_suggestions")
      (prefix ^ "mesh_prover_suggestions")
      (prefix ^ "mash_eval")
else
  ()
*}

end
