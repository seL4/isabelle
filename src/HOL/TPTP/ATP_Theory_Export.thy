(*  Title:      HOL/TPTP/ATP_Theory_Export.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* ATP Theory Exporter *}

theory ATP_Theory_Export
imports "~~/src/HOL/Sledgehammer2d"(*###*) Complex_Main
begin

ML_file "atp_theory_export.ML"

ML {*
open ATP_Problem
open ATP_Theory_Export
*}

ML {*
val do_it = true (* ### *)
val thy = @{theory Orderings}
val ctxt = @{context}
*}

ML {*
"/tmp/casc_ltb_isa"
|> generate_casc_lbt_isa_files_for_theory ctxt thy FOF Unchecked_Inferences
        "poly_tags??"
*}




ML {*
"/tmp/orderings.tptp"
|> generate_atp_inference_file_for_theory ctxt thy FOF Unchecked_Inferences
       "poly_tags??"
*}


end
