(*  Title:      HOL/Library/Sum_of_Squares/sos_wrapper.ML
    Author:     Philipp Meyer, TU Muenchen

Wrapper for "sos" proof method.
*)

signature SOS_WRAPPER =
sig
  val sos_tac: Proof.context -> string option -> int -> tactic
end

structure SOS_Wrapper: SOS_WRAPPER =
struct

datatype prover_result = Success | Failure | Error

fun str_of_result Success = "Success"
  | str_of_result Failure = "Failure"
  | str_of_result Error = "Error"

fun get_result rc =
  (case rc of
    0 => (Success, "SDP solved")
  | 1 => (Failure, "SDP is primal infeasible")
  | 2 => (Failure, "SDP is dual infeasible")
  | 3 => (Success, "SDP solved with reduced accuracy")
  | 4 => (Failure, "Maximum iterations reached")
  | 5 => (Failure, "Stuck at edge of primal feasibility")
  | 6 => (Failure, "Stuck at edge of dual infeasibility")
  | 7 => (Failure, "Lack of progress")
  | 8 => (Failure, "X, Z, or O was singular")
  | 9 => (Failure, "Detected NaN or Inf values")
  | _ => (Error, "return code is " ^ string_of_int rc))

fun run_solver ctxt input =
  Isabelle_System.with_tmp_file "sos_in" "" (fn in_path =>
    Isabelle_System.with_tmp_file "sos_out" "" (fn out_path =>
      let
        val _ = File.write in_path input

        val (output, rc) =
          Isabelle_System.bash_output
            ("\"$ISABELLE_CSDP\" " ^ File.shell_path in_path ^ " " ^ File.shell_path out_path)
        val _ = Sum_of_Squares.debug_message ctxt (fn () => "Solver output:\n" ^ output)

        val result = if File.exists out_path then File.read out_path else ""

        val (res, res_msg) = get_result rc
        val _ = Sum_of_Squares.trace_message ctxt (fn () => str_of_result res ^ ": " ^ res_msg)
      in
        (case res of
          Success => result
        | Failure => raise Sum_of_Squares.Failure res_msg
        | Error => error ("Prover failed: " ^ res_msg))
      end))


(* method setup *)

fun print_cert cert =
  Output.information
    ("To repeat this proof with a certificate use this command:\n" ^
      Active.sendback_markup [] ("by (sos \"" ^ Positivstellensatz_Tools.print_cert cert ^ "\")"))

fun sos_tac ctxt NONE =
      Sum_of_Squares.sos_tac print_cert
        (Sum_of_Squares.Prover (run_solver ctxt)) ctxt
  | sos_tac ctxt (SOME cert) =
      Sum_of_Squares.sos_tac ignore
        (Sum_of_Squares.Certificate (Positivstellensatz_Tools.read_cert ctxt cert)) ctxt

val _ = Theory.setup
 (Method.setup @{binding sos}
    (Scan.lift (Scan.option Parse.string)
      >> (fn arg => fn ctxt => SIMPLE_METHOD' (sos_tac ctxt arg)))
    "prove universal problems over the reals using sums of squares")

end
