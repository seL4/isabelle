theory Lambda_mu 
  imports "HOL-Nominal.Nominal" 
begin

section \<open>Lambda-Mu according to a paper by Gavin Bierman\<close>

atom_decl var mvar

nominal_datatype trm = 
    Var   "var" 
  | Lam  "\<guillemotleft>var\<guillemotright>trm"   (\<open>Lam [_]._\<close> [100,100] 100)
  | App  "trm" "trm" 
  | Pss  "mvar" "trm"                                   (* passivate *)
  | Act  "\<guillemotleft>mvar\<guillemotright>trm"  (\<open>Act [_]._\<close> [100,100] 100)       (* activate  *)


end
