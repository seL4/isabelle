(* ID: $Id$
   Author: Jia Meng, NICTA
*)

header {* ATP setup (Vampire, E prover and SPASS) *}

theory ResAtpMethods
imports Reconstruction
uses
  "Tools/res_atp_provers.ML"
  ("Tools/res_atp_methods.ML")

begin

oracle vampire_oracle ("string * int") = {* ResAtpProvers.vampire_o *}
oracle eprover_oracle ("string * int") = {* ResAtpProvers.eprover_o *}
oracle spass_oracle ("string * int") = {* ResAtpProvers.spass_o *}

use "Tools/res_atp_methods.ML"
setup ResAtpMethods.ResAtps_setup

end
