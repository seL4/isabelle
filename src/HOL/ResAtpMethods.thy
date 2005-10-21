(* ID: $Id$
   Author: Jia Meng, NICTA
 a method to setup "vampire" method 
 a method to setup "eprover" method
*)

theory ResAtpMethods
  imports Reconstruction 

uses ("Tools/res_atp_setup.ML")
     ("Tools/res_atp_provers.ML")
     ("Tools/res_atp_methods.ML")

begin

ML{*use "Tools/res_atp_setup.ML"*}
ML{*use "Tools/res_atp_provers.ML"*}

oracle vampire_oracle ("string list * int") =  {*ResAtpProvers.vampire_o*}
oracle eprover_oracle ("string list * int") =  {*ResAtpProvers.eprover_o*}


ML{*use "Tools/res_atp_methods.ML"*}

setup ResAtpMethods.ResAtps_setup
end
