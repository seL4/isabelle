(* Title:  mirabelle_quickcheck.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Quickcheck : MIRABELLE_ACTION =
struct

fun quickcheck_action args {pre, timeout, log, ...} =
  let
    val has_valid_key = member (op =) ["iterations", "size", "generator"] o fst
    val quickcheck = Quickcheck.quickcheck (filter has_valid_key args) 1
  in
    (case TimeLimit.timeLimit timeout quickcheck pre of
      NONE => log "quickcheck: no counterexample"
    | SOME _ => log "quickcheck: counterexample found")
  end
  handle TimeLimit.TimeOut => log "quickcheck: timeout"

fun invoke args =
  Mirabelle.register (Mirabelle.catch "quickcheck: " (quickcheck_action args))

end
