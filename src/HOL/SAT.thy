(*  Title:      HOL/SAT.thy
    ID:         $Id$
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005

Basic setup for the 'sat' tactic.
*)

header {* Reconstructing external resolution proofs for propositional logic *}

theory SAT imports HOL

uses "Tools/sat_solver.ML"
     "Tools/cnf_funcs.ML"
     "Tools/sat_funcs.ML"

begin

ML {* structure sat = SATFunc(structure cnf_struct = cnf); *}

method_setup sat = {* Method.no_args (Method.SIMPLE_METHOD sat.sat_tac) *}
  "SAT solver"

method_setup satx = {* Method.no_args (Method.SIMPLE_METHOD sat.satx_tac) *}
  "SAT solver (with definitional CNF)"

(*
method_setup cnf = {* Method.no_args (Method.SIMPLE_METHOD cnf.cnf_tac) *}
  "Transforming hypotheses in a goal into CNF"

method_setup cnf_concl = {* Method.no_args (Method.SIMPLE_METHOD cnf.cnf_concl_tac) *}
  "Transforming the conclusion of a goal to CNF"

method_setup cnf_thin = {* Method.no_args (Method.SIMPLE_METHOD cnf.cnf_thin_tac) *}
  "Same as cnf, but remove the original hypotheses"

method_setup cnfx_thin = {* Method.no_args (Method.SIMPLE_METHOD cnf.cnfx_thin_tac) *}
  "Same as cnf_thin, but may introduce extra variables"
*)

end
