(* ID: $Id$
   Author: Jia Meng

setup vampire prover as an oracle
setup E prover as an oracle
*)

theory ResAtpOracle 
  imports HOL   
uses "Tools/res_atp_setup.ML" 
     "Tools/res_atp_provers.ML"

begin 




oracle vampire_oracle ("string list * int") = {*ResAtpProvers.vampire_o
*}




oracle eprover_oracle ("string list * int") = {*ResAtpProvers.eprover_o
  *}


end