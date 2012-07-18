(*  Title:      HOL/TPTP/MaSh_Export.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Exporter *}

theory MaSh_Export
imports Complex_Main
uses "mash_export.ML"
begin

sledgehammer_params
  [provers = e, max_relevant = 40, strict, dont_slice, type_enc = poly_guards??,
   lam_trans = combs_and_lifting, timeout = 5, dont_preplay, minimize]

ML {*
open Sledgehammer_Filter_MaSh
open MaSh_Export
*}

ML {*
val do_it = false (* switch to "true" to generate the files *);
val thy = @{theory List};
val params = Sledgehammer_Isar.default_params @{context} []
*}

ML {*
if do_it then
  generate_accessibility thy false "/tmp/mash_accessibility"
else
  ()
*}

ML {*
if do_it then
  generate_features thy false "/tmp/mash_features"
else
  ()
*}

ML {*
if do_it then
  generate_isa_dependencies thy false "/tmp/mash_isa_dependencies"
else
  ()
*}

ML {*
if do_it then
  generate_atp_dependencies @{context} params thy false "/tmp/mash_atp_dependencies"
else
  ()
*}

ML {*
if do_it then
  generate_commands thy "/tmp/mash_commands"
else
  ()
*}

ML {*
if do_it then
  generate_iter_suggestions @{context} params thy 500 "/tmp/mash_iter_suggestions"
else
  ()
*}

end
