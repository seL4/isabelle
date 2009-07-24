(* Title:      sos_wrapper.ML
   Author:     Philipp Meyer, TU Muenchen

Added functionality for sums of squares, e.g. calling a remote prover
*)

signature SOS_WRAPPER =
sig

  datatype prover_result = Success | PartialSuccess | Failure | Error
  type prover = string * (int -> string -> prover_result * string)

  val setup: theory -> theory
end

structure SosWrapper : SOS_WRAPPER=
struct

datatype prover_result = Success | PartialSuccess | Failure | Error
type prover =
  string *                           (* command name *)
  (int -> string ->prover_result * string)   (* function to find failure from return value and output *)


(*** output control ***)

fun debug s = Output.debug (fn () => s)
val answer = Output.priority
val write = Output.writeln

(*** calling provers ***)

val destdir = ref ""

fun filename dir name =
  let
    val probfile = Path.basic (name ^ serial_string ())
  in
    if dir = "" then
      File.tmp_path probfile
    else
      if File.exists (Path.explode dir) then
        Path.append  (Path.explode dir) probfile
      else
        error ("No such directory: " ^ dir)
  end

fun is_success Success = true
  | is_success PartialSuccess = true
  | is_success _ = false
fun str_of_status Success = "Success"
  | str_of_status PartialSuccess = "Partial Success"
  | str_of_status Failure= "Failure"
  | str_of_status Error= "Error"

fun run_solver name (cmd, find_failure) input =
  let
    val _ = answer ("Calling solver: " ^ name)

    (* create input file *)
    val dir = ! destdir
    val input_file = filename dir "sos_in" 
    val _ = File.write input_file input

    val _ = debug "Solver input:"
    val _ = debug input

    (* call solver *)
    val output_file = filename dir "sos_out"
    val (output, rv) = system_out (cmd ^ " " ^ (Path.implode input_file) ^
                         " " ^ (Path.implode output_file))
 
    (* read and analysize output *)
    val (res, res_msg) = find_failure rv output
    val result = if is_success res then File.read output_file else ""

    (* remove temporary files *)
    val _ = if dir = "" then (File.rm input_file ; if File.exists output_file then File.rm output_file else ()) else ()

    val _ = debug "Solver output:"
    val _ = debug output
    val _ = debug "Solver result:"
    val _ = debug result

    val _ = answer (str_of_status res ^ ": " ^ res_msg)

  in
    if is_success res then
      result
    else
      error ("Prover failed: " ^ res_msg)
  end

(*** various provers ***)

(* local csdp client *)

fun find_csdp_run_failure rv _ =
  case rv of
    0 => (Success, "SDP solved")
  | 1 => (Failure, "SDP is primal infeasible")
  | 2 => (Failure, "SDP is dual infeasible")
  | 3 => (PartialSuccess, "SDP solved with reduced accuracy")
  | _ => (Failure, "return code is " ^ string_of_int rv)

val csdp = ("csdp", find_csdp_run_failure)

(* remote neos server *)

fun find_neos_failure rv output =
  if rv = 2 then (Failure, "no solution") else
  if rv <> 0 then (Error, "return code is " ^ string_of_int rv) else
  let
    fun find_success str =
      if String.isPrefix "Success: " str then
        SOME (Success, unprefix "Success: " str)
      else if String.isPrefix "Partial Success: " str then
        SOME (PartialSuccess, unprefix "Partial Success: " str)
      else if String.isPrefix "Failure: " str then
        SOME (Failure, unprefix "Failure: " str)
      else
        NONE 
    val exit_line = get_first find_success (split_lines output)
  in
    case exit_line of
      SOME (status, msg) =>
        if String.isPrefix "SDP solved" msg then
          (status, msg)
        else (Failure, msg)
    | NONE => (Failure, "no success")
  end

val neos_csdp = ("$ISABELLE_HOME/lib/scripts/neos/NeosCSDPClient.py", find_neos_failure)

(* save provers in table *)

val provers =
     Symtab.make [("remote_csdp", neos_csdp),("csdp", csdp)]

fun get_prover name =
  case Symtab.lookup provers name of
    SOME prover => prover
  | NONE => error ("unknown prover: " ^ name)

fun call_solver name =
    run_solver name (get_prover name)

(* setup tactic *)

val def_solver = "remote_csdp"

fun sos_solver name = (SIMPLE_METHOD' o (Sos.sos_tac (call_solver name))) 

val sos_method = Scan.optional (Scan.lift OuterParse.xname) def_solver >> sos_solver

val setup = Method.setup @{binding sos} sos_method "Prove universal problems over the reals using sums of squares"

end
