(*  Title:      HOL/Tools/SMT/smt_setup_solvers.ML
    Author:     Sascha Boehme, TU Muenchen

Setup SMT solvers.
*)

signature SMT_SETUP_SOLVERS =
sig
  datatype z3_non_commercial =
    Z3_Non_Commercial_Unknown |
    Z3_Non_Commercial_Accepted |
    Z3_Non_Commercial_Declined
  val z3_non_commercial: unit -> z3_non_commercial
  val setup: theory -> theory
end

structure SMT_Setup_Solvers: SMT_SETUP_SOLVERS =
struct

(* helper functions *)

val remote_prefix = "remote_"
fun make_name is_remote name = name |> is_remote ? prefix remote_prefix

fun make_local_avail name () = getenv (name ^ "_INSTALLED") = "yes"
fun make_remote_avail name () = getenv (name ^ "_REMOTE_SOLVER") <> ""
fun make_avail is_remote name =
  if is_remote then make_remote_avail name
  else make_local_avail name orf make_remote_avail name

fun make_local_command name () = [getenv (name ^ "_SOLVER")]
fun make_remote_command name () =
  [getenv "ISABELLE_SMT_REMOTE", getenv (name ^ "_REMOTE_SOLVER")]
fun make_command is_remote name =
  if is_remote then make_remote_command name
  else (fn () =>
    if make_local_avail name () then make_local_command name ()
    else make_remote_command name ())

fun outcome_of unsat sat unknown solver_name line =
  if String.isPrefix unsat line then SMT_Solver.Unsat
  else if String.isPrefix sat line then SMT_Solver.Sat
  else if String.isPrefix unknown line then SMT_Solver.Unknown
  else raise SMT_Failure.SMT (SMT_Failure.Other_Failure ("Solver " ^
    quote solver_name ^ " failed. Enable SMT tracing by setting the " ^
    "configuration option " ^ quote (Config.name_of SMT_Config.trace) ^ " and " ^
    "see the trace for details."))

fun on_first_line test_outcome solver_name lines =
  let
    val empty_line = (fn "" => true | _ => false)
    val split_first = (fn [] => ("", []) | l :: ls => (l, ls))
    val (l, ls) = split_first (snd (chop_while empty_line lines))
  in (test_outcome solver_name l, ls) end


(* CVC3 *)

local
  fun cvc3_options ctxt = [
    "-seed", string_of_int (Config.get ctxt SMT_Config.random_seed),
    "-lang", "smtlib", "-output-lang", "presentation"]

  fun mk is_remote = {
    name = make_name is_remote "cvc3",
    class = SMTLIB_Interface.smtlibC,
    avail = make_avail is_remote "CVC3",
    command = make_command is_remote "CVC3",
    options = cvc3_options,
    default_max_relevant = 400 (* FUDGE *),
    supports_filter = false,
    outcome =
      on_first_line (outcome_of "Unsatisfiable." "Satisfiable." "Unknown."),
    cex_parser = NONE,
    reconstruct = NONE }
in

fun cvc3 () = mk false
fun remote_cvc3 () = mk true

end


(* Yices *)

fun yices () = {
  name = "yices",
  class = SMTLIB_Interface.smtlibC,
  avail = make_local_avail "YICES",
  command = make_local_command "YICES",
  options = (fn ctxt => [
    "--rand-seed=" ^ string_of_int (Config.get ctxt SMT_Config.random_seed),
    "--smtlib"]),
  default_max_relevant = 350 (* FUDGE *),
  supports_filter = false,
  outcome = on_first_line (outcome_of "unsat" "sat" "unknown"),
  cex_parser = NONE,
  reconstruct = NONE }


(* Z3 *)

datatype z3_non_commercial =
  Z3_Non_Commercial_Unknown |
  Z3_Non_Commercial_Accepted |
  Z3_Non_Commercial_Declined


local
  val flagN = "Z3_NON_COMMERCIAL"

  val accepted = member (op =) ["yes", "Yes", "YES"]
  val declined = member (op =) ["no", "No", "NO"]
in

fun z3_non_commercial () =
  if accepted (getenv flagN) then Z3_Non_Commercial_Accepted
  else if declined (getenv flagN) then Z3_Non_Commercial_Declined
  else Z3_Non_Commercial_Unknown

fun if_z3_non_commercial f =
  (case z3_non_commercial () of
    Z3_Non_Commercial_Accepted => f ()
  | Z3_Non_Commercial_Declined =>
      error ("The SMT solver Z3 may only be used for non-commercial " ^
        "applications.")
  | Z3_Non_Commercial_Unknown =>
      error ("The SMT solver Z3 is not activated. To activate it, set\n" ^
        "the environment variable " ^ quote flagN ^ " to " ^ quote "yes" ^ "." ^
        (if getenv "Z3_COMPONENT" = "" then ""
         else "\nSee also " ^ Path.print (Path.expand (Path.explode "$Z3_COMPONENT/etc/settings")))))

end


local
  fun z3_make_command is_remote name () =
    if_z3_non_commercial (make_command is_remote name)

  fun z3_options ctxt =
    ["-rs:" ^ string_of_int (Config.get ctxt SMT_Config.random_seed),
      "MODEL=true", "-smt"]
    |> not (Config.get ctxt SMT_Config.oracle) ?
         append ["DISPLAY_PROOF=true","PROOF_MODE=2"]

  fun z3_on_last_line solver_name lines =
    let
      fun junk l =
        if String.isPrefix "WARNING: Out of allocated virtual memory" l
        then raise SMT_Failure.SMT SMT_Failure.Out_Of_Memory
        else
          String.isPrefix "WARNING" l orelse
          String.isPrefix "ERROR" l orelse
          forall Symbol.is_ascii_blank (Symbol.explode l)
    in
      the_default ("", []) (try (swap o split_last) (filter_out junk lines))
      |>> outcome_of "unsat" "sat" "unknown" solver_name
    end

  fun mk is_remote = {
    name = make_name is_remote "z3",
    class = Z3_Interface.smtlib_z3C,
    avail = make_avail is_remote "Z3",
    command = z3_make_command is_remote "Z3",
    options = z3_options,
    default_max_relevant = 350 (* FUDGE *),
    supports_filter = true,
    outcome = z3_on_last_line,
    cex_parser = SOME Z3_Model.parse_counterex,
    reconstruct = SOME Z3_Proof_Reconstruction.reconstruct }
in

fun z3 () = mk false
fun remote_z3 () = mk true

end


(* overall setup *)

val setup =
  SMT_Solver.add_solver (cvc3 ()) #>
  SMT_Solver.add_solver (remote_cvc3 ()) #>
  SMT_Solver.add_solver (yices ()) #>
  SMT_Solver.add_solver (z3 ()) #>
  SMT_Solver.add_solver (remote_z3 ())

end
