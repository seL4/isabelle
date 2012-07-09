(*  Title:      HOL/TPTP/ATP_Theory_Export.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* ATP Theory Exporter *}

theory ATP_Theory_Export
imports "~~/src/HOL/Sledgehammer2d" Complex_Main (* ### *)
uses "atp_theory_export.ML"
begin

ML {*
open ATP_Problem;
open ATP_Theory_Export;
*}

ML {*
val do_it = true (* false ### *); (* switch to "true" to generate the files *)
val thy = @{theory Nat}; (* @{theory Complex_Main}; ### *)
val ctxt = @{context}
*}


(* MaSh *)

ML {*
if do_it then
  "/tmp/mash_sample_problem.out"
  |> generate_mash_problem_file_for_theory thy
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
  "/tmp/mash_features.out"
  |> generate_mash_feature_file_for_theory thy false
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


(* TPTP/DFG *)

ML {*
if do_it then
  "/tmp/infs_poly_guards_query_query.tptp"
  |> generate_tptp_inference_file_for_theory ctxt thy FOF
         "poly_guards_query_query"
else
  ()
*}

ML {*
if do_it then
  "/tmp/infs_poly_tags_query_query.tptp"
  |> generate_tptp_inference_file_for_theory ctxt thy FOF
         "poly_tags_query_query"
else
  ()
*}

ML {*
if do_it then
  "/tmp/axs_tc_native.dfg"
  |> generate_tptp_inference_file_for_theory ctxt thy (DFG Polymorphic)
         "tc_native"
else
  ()
*}

end
