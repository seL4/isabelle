(* Author: Florian Haftmann, TU München *)

theory Quantified_Premise_Simproc
  imports Main
begin

simproc_setup defined_all ("\<And>x. PROP P x") = \<open>K Quantifier1.rearrange_all\<close>

end
