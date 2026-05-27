(*  Title:      HOL/Tools/SMT/smt_failure.ML
    Author:     Sascha Boehme, TU Muenchen

Failures and exception of SMT.
*)

signature SMT_FAILURE =
sig
  datatype failure =
    Counterexample of bool |
    Time_Out of string |
    Out_Of_Memory |
    Abnormal_Termination of int |
    Unknown |
    Replay of (string * exn) | (*temp for testing*)
    Other_Failure of string
  val string_of_failure: failure -> string
  exception SMT of failure
end;

structure SMT_Failure: SMT_FAILURE =
struct

datatype failure =
  Counterexample of bool |
  Time_Out of string |
  Out_Of_Memory |
  Abnormal_Termination of int |
  Unknown |
  Replay of (string * exn) | (*Temp for testing*)
  Other_Failure of string

fun string_of_failure (Counterexample genuine) =
      if genuine then "Counterexample found (possibly spurious)"
      else "Potential counterexample found"
  | string_of_failure (Time_Out s) = "Timed out " ^ s
  | string_of_failure Out_Of_Memory = "Ran out of memory"
  | string_of_failure (Abnormal_Termination err) =
      "Solver terminated abnormally with error code " ^ string_of_int err
  | string_of_failure Unknown = "Solver answered unknown"
  | string_of_failure (Replay (rule, _)) = (*temp for testing*)
      "Isabelle could not replay step " ^ rule
  | string_of_failure (Other_Failure msg) = msg

exception SMT of failure

end;
