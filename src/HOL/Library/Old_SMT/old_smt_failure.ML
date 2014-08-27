(*  Title:      HOL/Library/Old_SMT/old_smt_failure.ML
    Author:     Sascha Boehme, TU Muenchen

Failures and exception of SMT.
*)

signature OLD_SMT_FAILURE =
sig
  type counterexample = {
    is_real_cex: bool,
    free_constraints: term list,
    const_defs: term list}
  datatype failure =
    Counterexample of counterexample |
    Time_Out |
    Out_Of_Memory |
    Abnormal_Termination of int |
    Other_Failure of string
  val pretty_counterexample: Proof.context -> counterexample -> Pretty.T
  val string_of_failure: Proof.context -> failure -> string
  exception SMT of failure
end

structure Old_SMT_Failure: OLD_SMT_FAILURE =
struct

type counterexample = {
  is_real_cex: bool,
  free_constraints: term list,
  const_defs: term list}

datatype failure =
  Counterexample of counterexample |
  Time_Out |
  Out_Of_Memory |
  Abnormal_Termination of int |
  Other_Failure of string

fun pretty_counterexample ctxt {is_real_cex, free_constraints, const_defs} =
  let
    val msg =
      if is_real_cex then "Counterexample found (possibly spurious)"
      else "Potential counterexample found"
  in
    if null free_constraints andalso null const_defs then Pretty.str msg
    else
      Pretty.big_list (msg ^ ":")
        (map (Syntax.pretty_term ctxt) (free_constraints @ const_defs))
  end

fun string_of_failure ctxt (Counterexample cex) =
      Pretty.string_of (pretty_counterexample ctxt cex)
  | string_of_failure _ Time_Out = "Timed out"
  | string_of_failure _ Out_Of_Memory = "Ran out of memory"
  | string_of_failure _ (Abnormal_Termination err) =
      "Solver terminated abnormally with error code " ^ string_of_int err
  | string_of_failure _ (Other_Failure msg) = msg

exception SMT of failure

end
