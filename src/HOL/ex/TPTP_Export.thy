theory TPTP_Export
imports Complex_Main
uses "tptp_export.ML"
begin

ML {*
val readable_names = !Sledgehammer_ATP_Translate.readable_names;
Sledgehammer_ATP_Translate.readable_names := false
*}

ML {*
val thy = @{theory Complex_Main}
val ctxt = @{context}
*}

(*
ML {*
TPTP_Export.generate_tptp_inference_file_for_theory ctxt thy true
    "/tmp/infs_full_types.tptp"
*}

ML {*
TPTP_Export.generate_tptp_inference_file_for_theory ctxt thy false
    "/tmp/infs_partial_types.tptp"
*}

ML {*
TPTP_Export.generate_tptp_graph_file_for_theory ctxt thy
    "/tmp/graph.out"
*}
*)

ML {*
Sledgehammer_ATP_Translate.readable_names := readable_names
*}

end
