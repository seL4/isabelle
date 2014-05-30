(*  Title:      HOL/TPTP/MaSh_Export.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Exporter *}

theory MaSh_Export
imports Main
begin

ML_file "~~/src/HOL/Tools/Sledgehammer/sledgehammer_mash.ML" (*###*)
ML_file "mash_export.ML"

sledgehammer_params
  [provers = spass, max_facts = 32, strict, dont_slice, type_enc = mono_native,
   lam_trans = lifting, timeout = 2, dont_preplay, minimize]

declare [[sledgehammer_instantiate_inducts = false]]

hide_fact (open) HOL.ext

ML {*
Multithreading.max_threads_value ()
*}

ML {*
open MaSh_Export
*}

ML {*
val do_it = true (*###*) (* switch to "true" to generate the files *)
val thys = [@{theory List}]
val params as {provers, ...} = Sledgehammer_Commands.default_params @{theory} []
val prover = hd provers
val range = (1, (* ### NONE *) SOME 100)
val step = 1
val max_suggestions = 1024
val dir = "List"
val prefix = "/tmp/" ^ dir ^ "/"
*}

ML {*
if do_it then
  Isabelle_System.mkdir (Path.explode prefix)
else
  ()
*}

ML {* Options.put_default @{system_option MaSh} "sml_nb" *}

ML {*
if do_it then
  generate_mash_suggestions @{context} params (range, step) thys max_suggestions
    (prefix ^ "mash_sml_knn_suggestions")
else
  ()
*}

ML {* Options.put_default @{system_option MaSh} "sml_knn" *}

ML {*
if do_it then
  generate_mepo_suggestions @{context} params (range, step) thys max_suggestions
    (prefix ^ "mash_sml_nb_suggestions")
else
  ()
*}

ML {* Options.put_default @{system_option MaSh} "py" *}

ML {*
if do_it then
  generate_mepo_suggestions @{context} params (range, step) thys max_suggestions
    (prefix ^ "mepo_suggestions")
else
  ()
*}

ML {*
if do_it then
  generate_accessibility @{context} thys (prefix ^ "mash_accessibility")
else
  ()
*}

ML {*
if do_it then
  generate_features @{context} thys (prefix ^ "mash_features")
else
  ()
*}

ML {*
if do_it then
  generate_isar_dependencies @{context} range thys (prefix ^ "mash_dependencies")
else
  ()
*}

ML {*
if do_it then
  generate_isar_commands @{context} prover (range, step) thys max_suggestions
    (prefix ^ "mash_commands")
else
  ()
*}

ML {*
if do_it then
  generate_mepo_suggestions @{context} params (range, step) thys max_suggestions
    (prefix ^ "mepo_suggestions")
else
  ()
*}

ML {*
if do_it then
  generate_mesh_suggestions max_suggestions (prefix ^ "mash_suggestions")
    (prefix ^ "mepo_suggestions") (prefix ^ "mesh_suggestions")
else
  ()
*}

ML {*
if do_it then
  generate_prover_dependencies @{context} params range thys (prefix ^ "mash_prover_dependencies")
else
  ()
*}

ML {*
if do_it then
  generate_prover_commands @{context} params (range, step) thys max_suggestions
    (prefix ^ "mash_prover_commands")
else
  ()
*}

ML {*
if do_it then
  generate_mesh_suggestions max_suggestions (prefix ^ "mash_prover_suggestions")
    (prefix ^ "mepo_suggestions") (prefix ^ "mesh_prover_suggestions")
else
  ()
*}

end
