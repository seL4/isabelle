(* ID: $Id$
   Author: Jia Meng, NICTA
 a method to setup "vampire" method 
 a method to setup "eprover" method
*)

theory ResAtpMethods
  imports Reconstruction ResAtpOracle

  uses "Tools/res_atp_setup.ML"
       "Tools/res_atp_methods.ML"

begin
setup ResAtpMethods.ResAtps_setup

end
