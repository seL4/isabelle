theory TPTP_Export
imports Complex_Main
uses "tptp_export.ML"
begin

declare [[sledgehammer_atp_readable_names = false]]

ML {*
val do_it = false; (* switch to true to generate files *)
val thy = @{theory Complex_Main};
val ctxt = @{context}
*}

ML {*
if do_it then
  TPTP_Export.generate_tptp_inference_file_for_theory ctxt thy true
      "/tmp/infs_full_types.tptp"
else
  ()
*}

ML {*
if do_it then
  TPTP_Export.generate_tptp_inference_file_for_theory ctxt thy false
      "/tmp/infs_partial_types.tptp"
else
  ()
*}

ML {*
if do_it then
  TPTP_Export.generate_tptp_graph_file_for_theory ctxt thy
      "/tmp/graph.out"
else
  ()
*}

end
