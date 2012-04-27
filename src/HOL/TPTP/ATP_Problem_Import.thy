(*  Title:      HOL/TPTP/ATP_Problem_Import.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* ATP Problem Importer *}
theory ATP_Problem_Import
imports Complex_Main TPTP_Interpret
uses "sledgehammer_tactics.ML"
     ("atp_problem_import.ML")
begin

ML {* Proofterm.proofs := 0 *}

declare [[show_consts]] (* for Refute *)
declare [[smt_oracle]]

declare [[unify_search_bound = 60]]
declare [[unify_trace_bound = 60]]

use "atp_problem_import.ML"

(*
ML {* ATP_Problem_Import.isabelle_tptp_file @{theory} 50
          "$TPTP/Problems/PUZ/PUZ107^5.p" *}
*)

end
