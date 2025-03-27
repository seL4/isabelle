(*  Title:      HOL/Tools/Mirabelle/mirabelle_try0.ML
    Author:     Jasmin Blanchette, TU Munich
    Author:     Makarius
    Author:     Martin Desharnais, UniBw Munich

Mirabelle action: "try0".
*)

structure Mirabelle_Try0: MIRABELLE_ACTION =
struct

fun make_action ({timeout, ...} : Mirabelle.action_context) =
  let
    val generous_timeout = Time.scale 10.0 timeout
    val try0 = Try0.try0 (SOME timeout) Try0.empty_facts

    fun run ({pre, ...} : Mirabelle.command) =
      if Timeout.apply generous_timeout (not o null o try0) pre then
        "succeeded"
      else
        ""
  in ("", {run = run, finalize = K ""}) end

val () = Mirabelle.register_action "try0" make_action

end
