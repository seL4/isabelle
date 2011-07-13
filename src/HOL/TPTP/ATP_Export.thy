theory ATP_Export
imports Complex_Main
uses "atp_export.ML"
begin

ML {*
val do_it = false; (* switch to "true" to generate the files *)
val thy = @{theory Complex_Main};
val ctxt = @{context}
*}

ML {*
if do_it then
  ATP_Export.generate_tptp_inference_file_for_theory ctxt thy "poly_preds"
      "/tmp/infs_poly_preds.tptp"
else
  ()
*}

ML {*
if do_it then
  ATP_Export.generate_tptp_inference_file_for_theory ctxt thy "poly_tags"
      "/tmp/infs_poly_tags.tptp"
else
  ()
*}

ML {*
if do_it then
  ATP_Export.generate_tptp_inference_file_for_theory ctxt thy "poly_tags_heavy"
      "/tmp/infs_poly_tags_heavy.tptp"
else
  ()
*}

ML {*
if do_it then
  ATP_Export.generate_tptp_graph_file_for_theory ctxt thy
      "/tmp/graph.out"
else
  ()
*}

end
