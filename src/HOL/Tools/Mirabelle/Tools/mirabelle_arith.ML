(* Title:  mirabelle_arith.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Arith : MIRABELLE_ACTION =
struct

fun arith_action timeout {pre=st, ...} =
  if Mirabelle.can_apply timeout Arith_Data.arith_tac st
  then SOME "succeeded"
  else NONE

fun invoke _ = Mirabelle.register ("arith", arith_action)

end
