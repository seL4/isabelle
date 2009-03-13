(*  Title:      HOL/SAT.thy
    ID:         $Id$
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005

Basic setup for the 'sat' and 'satx' tactic.
*)

header {* Reconstructing external resolution proofs for propositional logic *}

theory SAT
imports Refute
uses
  "Tools/cnf_funcs.ML"
  "Tools/sat_funcs.ML"
begin

text {* \medskip Late package setup: default values for refute, see
  also theory @{theory Refute}. *}

refute_params
 ["itself"=1,
  minsize=1,
  maxsize=8,
  maxvars=10000,
  maxtime=60,
  satsolver="auto"]

ML {* structure sat = SATFunc(structure cnf = cnf); *}

method_setup sat = {* Method.no_args (SIMPLE_METHOD' sat.sat_tac) *}
  "SAT solver"

method_setup satx = {* Method.no_args (SIMPLE_METHOD' sat.satx_tac) *}
  "SAT solver (with definitional CNF)"

end
