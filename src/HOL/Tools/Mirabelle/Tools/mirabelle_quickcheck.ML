(* Title:  mirabelle_quickcheck.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Quickcheck : MIRABELLE_ACTION =
struct

fun quickcheck_action args {pre=st, ...} =
  let
    val has_valid_key = member (op =) ["iterations", "size", "generator"] o fst
  in
    (case Quickcheck.quickcheck (filter has_valid_key args) 1 st of
      NONE => SOME "no counterexample"
    | SOME _ => SOME "counterexample found")
  end

fun invoke args = Mirabelle.register ("quickcheck", quickcheck_action args)

end
