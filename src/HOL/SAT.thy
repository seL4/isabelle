(*  Title:      HOL/SAT.thy
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005

Basic setup for the 'sat' and 'satx' tactics.
*)

section \<open>Reconstructing external resolution proofs for propositional logic\<close>

theory SAT
imports Argo
begin

ML_file "Tools/prop_logic.ML"
ML_file "Tools/sat_solver.ML"
ML_file "Tools/sat.ML"
ML_file "Tools/Argo/argo_sat_solver.ML"

method_setup sat = \<open>Scan.succeed (SIMPLE_METHOD' o SAT.sat_tac)\<close>
  "SAT solver"

method_setup satx = \<open>Scan.succeed (SIMPLE_METHOD' o SAT.satx_tac)\<close>
  "SAT solver (with definitional CNF)"

end
