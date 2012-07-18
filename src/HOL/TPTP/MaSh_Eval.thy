(*  Title:      HOL/TPTP/MaSh_Eval.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Evaluation Driver *}

theory MaSh_Eval
imports Complex_Main
uses "mash_eval.ML"
begin

sledgehammer_params
  [provers = e, max_relevant = 40, strict, dont_slice, type_enc = poly_guards??,
   lam_trans = combs_and_lifting, timeout = 5, dont_preplay, minimize]

declare [[sledgehammer_instantiate_inducts]]

ML {*
open MaSh_Eval
*}

ML {*
val do_it = false (* switch to "true" to generate the files *);
val thy = @{theory List};
val params = Sledgehammer_Isar.default_params @{context} []
*}

ML {*
if do_it then
  evaluate_mash_suggestions @{context} params thy "/tmp/mash_suggestions_list"
else
  ()
*}

end
