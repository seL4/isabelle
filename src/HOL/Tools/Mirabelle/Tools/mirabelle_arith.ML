(* Title:  mirabelle_arith.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Arith : MIRABELLE_ACTION =
struct

fun arith_action {pre, timeout, log, ...} =
  if Mirabelle.can_apply timeout Arith_Data.arith_tac pre
  then log "succeeded"
  else ()

fun invoke _ = Mirabelle.register ("arith", arith_action)

end
