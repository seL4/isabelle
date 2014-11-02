(*  Title:      HOL/TPTP/MaSh_Eval.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

section {* MaSh Evaluation Driver *}

theory MaSh_Eval
imports MaSh_Export_Base
begin

ML_file "mash_eval.ML"

sledgehammer_params
  [provers = e, max_facts = 64, strict, dont_slice, type_enc = poly_guards??,
   lam_trans = combs, timeout = 30, dont_preplay, minimize]

ML {*
Multithreading.max_threads_value ()
*}

ML {*
open MaSh_Eval
*}

ML {*
val params = Sledgehammer_Commands.default_params @{theory} []
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
  evaluate_mash_suggestions @{context} params range (SOME prob_dir)
    [prefix ^ "mepo_suggestions",
     prefix ^ "mash_suggestions",
     prefix ^ "mash_prover_suggestions",
     prefix ^ "mesh_suggestions",
     prefix ^ "mesh_prover_suggestions"]
    (prefix ^ "mash_eval")
else
  ()
*}

end
