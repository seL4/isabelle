theory ATP_Export
imports Complex_Main
uses "atp_export.ML"
begin

ML {*
open ATP_Problem;
open ATP_Export;
*}

ML {*
val do_it = false; (* switch to "true" to generate the files *)
val thy = @{theory Complex_Main};
val ctxt = @{context}
*}

ML {*
if do_it then
  "/tmp/axs_mono_simple.dfg"
  |> generate_tptp_inference_file_for_theory ctxt thy (DFG DFG_Sorted)
         "mono_simple"
else
  ()
*}

ML {*
if do_it then
  "/tmp/infs_poly_guards.tptp"
  |> generate_tptp_inference_file_for_theory ctxt thy FOF "poly_guards"
else
  ()
*}

ML {*
if do_it then
  "/tmp/infs_poly_tags.tptp"
  |> generate_tptp_inference_file_for_theory ctxt thy FOF "poly_tags"
else
  ()
*}

ML {*
if do_it then
  "/tmp/infs_poly_tags_uniform.tptp"
  |> generate_tptp_inference_file_for_theory ctxt thy FOF "poly_tags_uniform"
else
  ()
*}

ML {*
if do_it then
  "/tmp/graph.out" |> generate_tptp_graph_file_for_theory ctxt thy
else
  ()
*}

end
