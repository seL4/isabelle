(* Title:  mirabelle_arith.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Arith : MIRABELLE_ACTION =
struct

fun arith_action {pre, timeout, log, ...} =
  if Mirabelle.can_apply timeout Arith_Data.arith_tac pre
  then log "arith: succeeded"
  else ()
  handle TimeLimit.TimeOut => log "arith: time out"

fun invoke _ = Mirabelle.register (Mirabelle.catch "arith: " arith_action)

end
