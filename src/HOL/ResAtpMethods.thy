(* ID: $Id$
   Author: Jia Meng, NICTA
*)

header {* ATP setup (Vampire and E prover) *}

theory ResAtpMethods
imports Reconstruction
uses
  "Tools/res_atp_setup.ML"
  "Tools/res_atp_provers.ML"
  ("Tools/res_atp_methods.ML")

begin

oracle vampire_oracle ("(string list * string list) * int") = {* ResAtpProvers.vampire_o *}
oracle eprover_oracle ("(string list * string list) * int") = {* ResAtpProvers.eprover_o *}

use "Tools/res_atp_methods.ML"
setup ResAtpMethods.ResAtps_setup

end
