(*  Title:      HOL/TPTP/MaSh_Eval.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

section \<open>MaSh Evaluation Driver\<close>

theory MaSh_Eval
imports MaSh_Export_Base
begin

ML_file \<open>mash_eval.ML\<close>

sledgehammer_params
  [provers = e, max_facts = 64, strict, dont_slice, type_enc = poly_guards??,
   lam_trans = combs, timeout = 30, dont_preplay, minimize]

ML \<open>
Multithreading.max_threads ()
\<close>

ML \<open>
open MaSh_Eval
\<close>

ML \<open>
val params = Sledgehammer_Commands.default_params \<^theory> []
val prob_dir = prefix ^ "mash_problems"
\<close>

ML \<open>
if do_it then
  ignore (Isabelle_System.make_directory (Path.explode prob_dir))
else
  ()
\<close>

ML \<open>
if do_it then
  evaluate_mash_suggestions \<^context> params range (SOME prob_dir)
    [prefix ^ "mepo_suggestions",
     prefix ^ "mash_suggestions",
     prefix ^ "mash_prover_suggestions",
     prefix ^ "mesh_suggestions",
     prefix ^ "mesh_prover_suggestions"]
    (prefix ^ "mash_eval")
else
  ()
\<close>

end
