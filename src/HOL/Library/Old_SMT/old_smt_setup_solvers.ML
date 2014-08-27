(*  Title:      HOL/Library/Old_SMT/old_smt_setup_solvers.ML
    Author:     Sascha Boehme, TU Muenchen

Setup SMT solvers.
*)

signature OLD_SMT_SETUP_SOLVERS =
sig
  datatype z3_non_commercial =
    Z3_Non_Commercial_Unknown |
    Z3_Non_Commercial_Accepted |
    Z3_Non_Commercial_Declined
  val z3_non_commercial: unit -> z3_non_commercial
  val z3_with_extensions: bool Config.T
  val setup: theory -> theory
end

structure Old_SMT_Setup_Solvers: OLD_SMT_SETUP_SOLVERS =
struct

(* helper functions *)

fun make_avail name () = getenv (name ^ "_SOLVER") <> ""

fun make_command name () = [getenv (name ^ "_SOLVER")]

fun outcome_of unsat sat unknown solver_name line =
  if String.isPrefix unsat line then Old_SMT_Solver.Unsat
  else if String.isPrefix sat line then Old_SMT_Solver.Sat
  else if String.isPrefix unknown line then Old_SMT_Solver.Unknown
  else raise Old_SMT_Failure.SMT (Old_SMT_Failure.Other_Failure ("Solver " ^
    quote solver_name ^ " failed. Enable SMT tracing by setting the " ^
    "configuration option " ^ quote (Config.name_of Old_SMT_Config.trace) ^ " and " ^
    "see the trace for details."))

fun on_first_line test_outcome solver_name lines =
  let
    val empty_line = (fn "" => true | _ => false)
    val split_first = (fn [] => ("", []) | l :: ls => (l, ls))
    val (l, ls) = split_first (snd (take_prefix empty_line lines))
  in (test_outcome solver_name l, ls) end


(* CVC3 *)

local
  fun cvc3_options ctxt = [
    "-seed", string_of_int (Config.get ctxt Old_SMT_Config.random_seed),
    "-lang", "smtlib", "-output-lang", "presentation",
    "-timeout", string_of_int (Real.ceil (Config.get ctxt Old_SMT_Config.timeout))]
in

val cvc3: Old_SMT_Solver.solver_config = {
  name = "cvc3",
  class = K Old_SMTLIB_Interface.smtlibC,
  avail = make_avail "CVC3",
  command = make_command "CVC3",
  options = cvc3_options,
  default_max_relevant = 400 (* FUDGE *),
  supports_filter = false,
  outcome =
    on_first_line (outcome_of "Unsatisfiable." "Satisfiable." "Unknown."),
  cex_parser = NONE,
  reconstruct = NONE }

end


(* Yices *)

val yices: Old_SMT_Solver.solver_config = {
  name = "yices",
  class = K Old_SMTLIB_Interface.smtlibC,
  avail = make_avail "YICES",
  command = make_command "YICES",
  options = (fn ctxt => [
    "--rand-seed=" ^ string_of_int (Config.get ctxt Old_SMT_Config.random_seed),
    "--timeout=" ^
      string_of_int (Real.ceil (Config.get ctxt Old_SMT_Config.timeout)),
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
  val accepted = member (op =) ["yes", "Yes", "YES"]
  val declined = member (op =) ["no", "No", "NO"]
in

fun z3_non_commercial () =
  let
    val flag1 = Options.default_string @{system_option z3_non_commercial}
    val flag2 = getenv "Z3_NON_COMMERCIAL"
  in
    if accepted flag1 then Z3_Non_Commercial_Accepted
    else if declined flag1 then Z3_Non_Commercial_Declined
    else if accepted flag2 then Z3_Non_Commercial_Accepted
    else if declined flag2 then Z3_Non_Commercial_Declined
    else Z3_Non_Commercial_Unknown
  end

fun if_z3_non_commercial f =
  (case z3_non_commercial () of
    Z3_Non_Commercial_Accepted => f ()
  | Z3_Non_Commercial_Declined =>
      error (Pretty.string_of (Pretty.para
        "The SMT solver Z3 may only be used for non-commercial applications."))
  | Z3_Non_Commercial_Unknown =>
      error
        (Pretty.string_of
          (Pretty.para
            ("The SMT solver Z3 is not activated. To activate it, set the Isabelle \
             \system option \"z3_non_commercial\" to \"yes\" (e.g. via \
             \the Isabelle/jEdit menu Plugin Options / Isabelle / General).")) ^
        "\n\nSee also " ^ Url.print (Url.explode "http://z3.codeplex.com/license")))

end


val z3_with_extensions =
  Attrib.setup_config_bool @{binding old_z3_with_extensions} (K false)

local
  fun z3_make_command name () = if_z3_non_commercial (make_command name)

  fun z3_options ctxt =
    ["-rs:" ^ string_of_int (Config.get ctxt Old_SMT_Config.random_seed),
      "MODEL=true",
      "SOFT_TIMEOUT=" ^
        string_of_int (Real.ceil (1000.0 * Config.get ctxt Old_SMT_Config.timeout)),
      "-smt"]
    |> not (Config.get ctxt Old_SMT_Config.oracle) ?
         append ["DISPLAY_PROOF=true", "PROOF_MODE=2"]

  fun z3_on_first_or_last_line solver_name lines =
    let
      fun junk l =
        if String.isPrefix "WARNING: Out of allocated virtual memory" l
        then raise Old_SMT_Failure.SMT Old_SMT_Failure.Out_Of_Memory
        else
          String.isPrefix "WARNING" l orelse
          String.isPrefix "ERROR" l orelse
          forall Symbol.is_ascii_blank (Symbol.explode l)
      val lines = filter_out junk lines
      fun outcome split =
        the_default ("", []) (try split lines)
        |>> outcome_of "unsat" "sat" "unknown" solver_name
    in
      (* Starting with version 4.0, Z3 puts the outcome on the first line of the
         output rather than on the last line. *)
      outcome (fn lines => (hd lines, tl lines))
      handle Old_SMT_Failure.SMT _ => outcome (swap o split_last)
    end

  fun select_class ctxt =
    if Config.get ctxt z3_with_extensions then Old_Z3_Interface.smtlib_z3C
    else Old_SMTLIB_Interface.smtlibC
in

val z3: Old_SMT_Solver.solver_config = {
  name = "z3",
  class = select_class,
  avail = make_avail "Z3",
  command = z3_make_command "Z3",
  options = z3_options,
  default_max_relevant = 350 (* FUDGE *),
  supports_filter = true,
  outcome = z3_on_first_or_last_line,
  cex_parser = SOME Old_Z3_Model.parse_counterex,
  reconstruct = SOME Old_Z3_Proof_Reconstruction.reconstruct }

end


(* overall setup *)

val setup =
  Old_SMT_Solver.add_solver cvc3 #>
  Old_SMT_Solver.add_solver yices #>
  Old_SMT_Solver.add_solver z3

end
