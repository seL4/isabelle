(* Author: Florian Haftmann, TU München *)

theory Quantified_Premise_Simproc
  imports Main
begin

simproc_setup defined_forall ("\<And>x. PROP P x") = \<open>K Quantifier1.rearrange_All\<close>

end
