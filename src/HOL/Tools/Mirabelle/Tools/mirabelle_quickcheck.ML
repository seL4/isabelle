(* Title:  mirabelle_quickcheck.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Quickcheck : MIRABELLE_ACTION =
struct

fun quickcheck_action limit args {pre=st, ...} =
  let
    val has_valid_key = member (op =) ["iterations", "size", "generator"] o fst
    val quickcheck = Quickcheck.quickcheck (filter has_valid_key args) 1
  in
    (case TimeLimit.timeLimit limit quickcheck st of
      NONE => SOME "no counterexample"
    | SOME _ => SOME "counterexample found")
  end

fun invoke args = Mirabelle.register ("quickcheck", quickcheck_action args)

end
