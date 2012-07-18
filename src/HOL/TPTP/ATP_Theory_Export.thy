(*  Title:      HOL/TPTP/ATP_Theory_Export.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* ATP Theory Exporter *}

theory ATP_Theory_Export
imports Complex_Main
uses "atp_theory_export.ML"
begin

ML {*
open ATP_Problem;
open ATP_Theory_Export;
*}

ML {*
val do_it = false; (* switch to "true" to generate the files *)
val thy = @{theory List};
val ctxt = @{context}
*}

ML {*
if do_it then
  "/tmp/axs_tc_native.dfg"
  |> generate_atp_inference_file_for_theory ctxt thy (DFG Polymorphic)
         "tc_native"
else
  ()
*}

ML {*
if do_it then
  "/tmp/infs_poly_guards_query_query.tptp"
  |> generate_atp_inference_file_for_theory ctxt thy FOF
         "poly_guards_query_query"
else
  ()
*}

ML {*
if do_it then
  "/tmp/infs_poly_tags_query_query.tptp"
  |> generate_atp_inference_file_for_theory ctxt thy FOF
         "poly_tags_query_query"
else
  ()
*}

end
