(*  Title:      HOL/Mirabelle/Tools/mirabelle_arith.ML
    Author:     Jasmin Blanchette, TU Munich
    Author:     Sascha Boehme, TU Munich
    Author:     Makarius
    Author:     Martin Desharnais, UniBw Munich

Mirabelle action: "arith".
*)

structure Mirabelle_Arith: MIRABELLE_ACTION =
struct

fun make_action ({timeout, ...} : Mirabelle.action_context) =
  let
    fun run_action ({pre, ...} : Mirabelle.command) =
      if Mirabelle.can_apply timeout Arith_Data.arith_tac pre then
        "succeeded"
      else
        ""
  in {run_action = run_action, finalize = K ""} end

val () = Mirabelle.register_action "arith" make_action

end
