(*  Title:      HOL/Library/Sum_of_Squares/sos_wrapper.ML
    Author:     Philipp Meyer, TU Muenchen

Added functionality for sums of squares, e.g. calling a remote prover.
*)

signature SOS_WRAPPER =
sig
  datatype prover_result = Success | Failure | Error
  val setup: theory -> theory
  val dest_dir: string Config.T
  val prover_name: string Config.T
end

structure SOS_Wrapper: SOS_WRAPPER =
struct

datatype prover_result = Success | Failure | Error

fun str_of_result Success = "Success"
  | str_of_result Failure = "Failure"
  | str_of_result Error = "Error"


(*** calling provers ***)

val dest_dir = Attrib.setup_config_string @{binding sos_dest_dir} (K "")

fun filename dir name =
  let
    val probfile = Path.basic (name ^ serial_string ())
    val dir_path = Path.explode dir
  in
    if dir = "" then
      File.tmp_path probfile
    else if File.exists dir_path then
      Path.append dir_path probfile
    else error ("No such directory: " ^ dir)
  end

fun run_solver ctxt name exe find_failure input =
  let
    val _ = warning ("Calling solver: " ^ name)

    (* create input file *)
    val dir = Config.get ctxt dest_dir
    val input_file = filename dir "sos_in"
    val _ = File.write input_file input

    (* call solver *)
    val output_file = filename dir "sos_out"
    val (output, rv) =
      Isabelle_System.bash_output
       (if File.exists exe then
          space_implode " " (map File.shell_path [exe, input_file, output_file])
        else error ("Bad executable: " ^ File.platform_path exe))

    (* read and analyze output *)
    val (res, res_msg) = find_failure rv
    val result = if File.exists output_file then File.read output_file else ""

    (* remove temporary files *)
    val _ =
      if dir = "" then
        (File.rm input_file; if File.exists output_file then File.rm output_file else ())
      else ()

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


(*** various provers ***)

(* local csdp client *)

fun find_csdp_failure rv =
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

val csdp = (Path.explode "$ISABELLE_CSDP", find_csdp_failure)


(* remote neos server *)

fun find_neos_failure rv =
  case rv of
    20 => (Error, "error submitting job")
  | 21 => (Error, "interrupt")
  |  _ => find_csdp_failure rv

val neos_csdp = (Path.explode "$ISABELLE_SUM_OF_SQUARES/neos_csdp_client", find_neos_failure)


(* named provers *)

fun prover "remote_csdp" = neos_csdp
  | prover "csdp" = csdp
  | prover name = error ("Unknown prover: " ^ name)

val prover_name = Attrib.setup_config_string @{binding sos_prover_name} (K "remote_csdp")

fun call_solver ctxt opt_name =
  let
    val name = the_default (Config.get ctxt prover_name) opt_name
    val (exe, find_failure) = prover name
  in run_solver ctxt name exe find_failure end


(* certificate output *)

fun output_line cert =
  "To repeat this proof with a certifiate use this command:\n" ^
    Markup.markup Isabelle_Markup.sendback ("by (sos_cert \"" ^ cert ^ "\")")

val print_cert = warning o output_line o PositivstellensatzTools.pss_tree_to_cert


(* method setup *)

fun sos_solver print method = SIMPLE_METHOD' o Sum_of_Squares.sos_tac print method

val setup =
  Method.setup @{binding sos}
    (Scan.lift (Scan.option Parse.xname)
      >> (fn opt_name => fn ctxt =>
        sos_solver print_cert
          (Sum_of_Squares.Prover (call_solver ctxt opt_name)) ctxt))
    "prove universal problems over the reals using sums of squares" #>
  Method.setup @{binding sos_cert}
    (Scan.lift Parse.string
      >> (fn cert => fn ctxt =>
        sos_solver ignore
          (Sum_of_Squares.Certificate (PositivstellensatzTools.cert_to_pss_tree ctxt cert)) ctxt))
    "prove universal problems over the reals using sums of squares with certificates"

end
