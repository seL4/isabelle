(*  Title:      HOL/SAT.thy
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005

Basic setup for the 'sat' and 'satx' tactic.
*)

header {* Reconstructing external resolution proofs for propositional logic *}

theory SAT
imports Hilbert_Choice List Sledgehammer
begin

ML_file "Tools/sat_funcs.ML"

ML {* structure sat = SATFunc(cnf) *}

method_setup sat = {* Scan.succeed (SIMPLE_METHOD' o sat.sat_tac) *}
  "SAT solver"

method_setup satx = {* Scan.succeed (SIMPLE_METHOD' o sat.satx_tac) *}
  "SAT solver (with definitional CNF)"

end
