(*  Title:      HOL/TPTP/MaSh_Export.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Exporter *}

theory MaSh_Export
imports ATP_Theory_Export
uses "mash_export.ML"
begin

ML {*
open MaSh_Export
*}

ML {*
val do_it = false; (* switch to "true" to generate the files *)
val thy = @{theory List};
val ctxt = @{context}
*}

ML {*
if do_it then
  "/tmp/mash_sample_problem.out"
  |> generate_mash_problem_file_for_theory thy
else
  ()
*}

ML {*
if do_it then
  "/tmp/mash_features.out"
  |> generate_mash_feature_file_for_theory thy false
else
  ()
*}

ML {*
if do_it then
  "/tmp/mash_accessibility.out"
  |> generate_mash_accessibility_file_for_theory thy false
else
  ()
*}

ML {*
if do_it then
  "/tmp/mash_dependencies.out"
  |> generate_mash_dependency_file_for_theory thy false
else
   ()
*}

end
