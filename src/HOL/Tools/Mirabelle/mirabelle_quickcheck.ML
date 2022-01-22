(*  Title:      HOL/Mirabelle/Tools/mirabelle_quickcheck.ML
    Author:     Jasmin Blanchette, TU Munich
    Author:     Sascha Boehme, TU Munich
    Author:     Martin Desharnais, UniBw Munich

Mirabelle action: "quickcheck".
*)

structure Mirabelle_Quickcheck: MIRABELLE_ACTION =
struct

fun make_action ({arguments, timeout, ...} : Mirabelle.action_context) =
  let
    val has_valid_key = member (op =) ["iterations", "size", "generator"] o fst
    val quickcheck =
      Quickcheck.quickcheck (map (apsnd single) (filter has_valid_key arguments)) 1

    fun run ({pre, ...} : Mirabelle.command) =
      (case Timeout.apply timeout quickcheck pre of
        NONE => "no counterexample"
      | SOME _ => "counterexample found")
  in ("", {run = run, finalize = K ""}) end

val () = Mirabelle.register_action "quickcheck" make_action

end
