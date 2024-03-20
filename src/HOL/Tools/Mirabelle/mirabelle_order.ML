(*  Title:      HOL/Tools/Mirabelle/mirabelle_order.ML
    Author:     Martin Desharnais, MPI-INF Saarbrücken

Mirabelle action: "order".
*)

structure Mirabelle_Order: MIRABELLE_ACTION =
struct

fun make_action ({timeout, ...} : Mirabelle.action_context) =
  let
    val _ = HOL_Order_Tac.tac []
    fun run ({pre, ...} : Mirabelle.command) =
      (case Timing.timing (Mirabelle.can_apply timeout (HOL_Order_Tac.tac [])) pre of
        ({cpu, ...}, true) => "succeeded (" ^ Time.toString cpu ^ " s)"
      | (_, false) => "failed")
  in ("", {run = run, finalize = K ""}) end

val () = Mirabelle.register_action "order" make_action

end
