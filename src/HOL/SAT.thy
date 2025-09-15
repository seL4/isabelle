(*  Title:      HOL/SAT.thy
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005

Basic setup for the proof methods "sat" and "satx".
*)

section \<open>Reconstructing external resolution proofs for propositional logic\<close>

theory SAT
imports Argo
begin

ML_file \<open>Tools/prop_logic.ML\<close>
ML_file \<open>Tools/sat_solver.ML\<close>
ML_file \<open>Tools/sat.ML\<close>
ML_file \<open>Tools/Argo/argo_sat_solver.ML\<close>

method_setup sat = \<open>Scan.succeed (SIMPLE_METHOD' o SAT.sat_tac)\<close>
  "SAT solver"

method_setup satx = \<open>Scan.succeed (SIMPLE_METHOD' o SAT.satx_tac)\<close>
  "SAT solver (with definitional CNF)"

end
