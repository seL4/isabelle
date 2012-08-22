(*  Title:      HOL/TPTP/MaSh_Export.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Exporter *}

theory MaSh_Export
imports Complex_Main
begin

ML_file "mash_export.ML"

sledgehammer_params
  [provers = e, max_relevant = 40, strict, dont_slice, type_enc = poly_guards??,
   lam_trans = combs_and_lifting, timeout = 1, dont_preplay, minimize]

ML {*
open MaSh_Export
*}

ML {*
val do_it = false (* switch to "true" to generate the files *)
val thy = @{theory List}
val params as {provers, ...} = Sledgehammer_Isar.default_params @{context} []
val prover = hd provers
*}

ML {*
if do_it then
  generate_accessibility @{context} thy false "/tmp/mash_accessibility"
else
  ()
*}

ML {*
if do_it then
  generate_features @{context} prover thy false "/tmp/mash_features"
else
  ()
*}

ML {*
if do_it then
  generate_isar_dependencies @{context} thy false "/tmp/mash_dependencies"
else
  ()
*}

ML {*
if do_it then
  generate_commands @{context} params thy "/tmp/mash_commands"
else
  ()
*}

ML {*
if do_it then
  generate_mepo_suggestions @{context} params thy 500 "/tmp/mash_mepo_suggestions"
else
  ()
*}

ML {*
if do_it then
  generate_atp_dependencies @{context} params thy false "/tmp/mash_atp_dependencies"
else
  ()
*}

end
