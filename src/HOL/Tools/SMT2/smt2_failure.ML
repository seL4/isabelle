(*  Title:      HOL/Tools/SMT2/smt2_failure.ML
    Author:     Sascha Boehme, TU Muenchen

Failures and exception of SMT.
*)

signature SMT2_FAILURE =
sig
  datatype failure =
    Counterexample of bool |
    Time_Out |
    Out_Of_Memory |
    Abnormal_Termination of int |
    Other_Failure of string
  val string_of_failure: failure -> string
  exception SMT of failure
end

structure SMT2_Failure: SMT2_FAILURE =
struct

datatype failure =
  Counterexample of bool |
  Time_Out |
  Out_Of_Memory |
  Abnormal_Termination of int |
  Other_Failure of string

fun string_of_failure (Counterexample genuine) =
      if genuine then "Counterexample found (possibly spurious)"
      else "Potential counterexample found"
  | string_of_failure Time_Out = "Timed out"
  | string_of_failure Out_Of_Memory = "Ran out of memory"
  | string_of_failure (Abnormal_Termination err) =
      "Solver terminated abnormally with error code " ^ string_of_int err
  | string_of_failure (Other_Failure msg) = msg

exception SMT of failure

end
