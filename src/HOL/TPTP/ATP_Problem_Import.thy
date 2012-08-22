(*  Title:      HOL/TPTP/ATP_Problem_Import.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* ATP Problem Importer *}

theory ATP_Problem_Import
imports Complex_Main TPTP_Interpret
begin

ML_file "sledgehammer_tactics.ML"

ML {* Proofterm.proofs := 0 *}

declare [[show_consts]] (* for Refute *)
declare [[smt_oracle]]

declare [[unify_search_bound = 60]]
declare [[unify_trace_bound = 60]]

ML_file "atp_problem_import.ML"

(*
ML {* ATP_Problem_Import.isabelle_tptp_file @{theory} 50
          "$TPTP/Problems/PUZ/PUZ107^5.p" *}
*)

end
