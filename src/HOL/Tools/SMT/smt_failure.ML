(*  Title:      HOL/Tools/SMT/smt_failure.ML
    Author:     Sascha Boehme, TU Muenchen

Failures and exception of SMT.
*)

signature SMT_FAILURE =
sig
  datatype failure =
    Counterexample of bool * term list |
    Time_Out |
    Out_Of_Memory |
    Other_Failure of string
  val string_of_failure: Proof.context -> failure -> string
  exception SMT of failure
end

structure SMT_Failure: SMT_FAILURE =
struct

datatype failure =
  Counterexample of bool * term list |
  Time_Out |
  Out_Of_Memory |
  Other_Failure of string

fun string_of_failure ctxt (Counterexample (real, ex)) =
      let
        val msg = (if real then "C" else "Potential c") ^ "ounterexample found"
      in
        if null ex then msg
        else Pretty.string_of (Pretty.big_list (msg ^ ":")
          (map (Syntax.pretty_term ctxt) ex))
      end
  | string_of_failure _ Time_Out = "Timed out"
  | string_of_failure _ Out_Of_Memory = "Ran out of memory"
  | string_of_failure _ (Other_Failure msg) = msg

exception SMT of failure

end
