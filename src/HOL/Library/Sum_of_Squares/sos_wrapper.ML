(*  Title:      HOL/Library/Sum_of_Squares/sos_wrapper.ML
    Author:     Philipp Meyer, TU Muenchen

Added functionality for sums of squares, e.g. calling a remote prover.
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


fun filename name =
  File.tmp_path (Path.basic (name ^ serial_string ()))

fun find_failure rv =
  case rv of
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
  | _ => (Error, "return code is " ^ string_of_int rv)

val exe = Path.explode "$ISABELLE_CSDP"

fun run_solver ctxt input =
  let
    (* create input file *)
    val input_file = filename "sos_in"
    val _ = File.write input_file input

    (* call solver *)
    val output_file = filename "sos_out"
    val (output, rv) =
      Isabelle_System.bash_output
       (if File.exists exe then
          space_implode " " (map File.shell_path [exe, input_file, output_file])
        else error ("Bad executable: " ^ File.platform_path exe))

    (* read and analyze output *)
    val (res, res_msg) = find_failure rv
    val result = if File.exists output_file then File.read output_file else ""

    (* remove temporary files *)
    val _ = File.rm input_file
    val _ = if File.exists output_file then File.rm output_file else ()

    val _ =
      if Config.get ctxt Sum_of_Squares.trace
      then writeln ("Solver output:\n" ^ output)
      else ()

    val _ = warning (str_of_result res ^ ": " ^ res_msg)
  in
    (case res of
      Success => result
    | Failure => raise Sum_of_Squares.Failure res_msg
    | Error => error ("Prover failed: " ^ res_msg))
  end


(* method setup *)

fun print_cert cert =
  warning
    ("To repeat this proof with a certificate use this proof method:\n" ^
      Active.sendback_markup [] ("(sos \"" ^ Positivstellensatz_Tools.print_cert cert ^ "\")"))

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
