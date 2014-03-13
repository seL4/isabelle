(*  Title:      HOL/Tools/SMT2/smt2_setup_solvers.ML
    Author:     Sascha Boehme, TU Muenchen

Setup SMT solvers.
*)

signature SMT2_SETUP_SOLVERS =
sig
  datatype z3_non_commercial =
    Z3_Non_Commercial_Unknown |
    Z3_Non_Commercial_Accepted |
    Z3_Non_Commercial_Declined
  val z3_non_commercial: unit -> z3_non_commercial
  val z3_extensions: bool Config.T
end

structure SMT2_Setup_Solvers: SMT2_SETUP_SOLVERS =
struct

(* helper functions *)

fun make_avail name () = getenv (name ^ "_SOLVER") <> ""

fun make_command name () = [getenv (name ^ "_SOLVER")]

fun outcome_of unsat sat unknown solver_name line =
  if String.isPrefix unsat line then SMT2_Solver.Unsat
  else if String.isPrefix sat line then SMT2_Solver.Sat
  else if String.isPrefix unknown line then SMT2_Solver.Unknown
  else raise SMT2_Failure.SMT (SMT2_Failure.Other_Failure ("Solver " ^
    quote solver_name ^ " failed. Enable SMT tracing by setting the " ^
    "configuration option " ^ quote (Config.name_of SMT2_Config.trace) ^ " and " ^
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
    "-seed", string_of_int (Config.get ctxt SMT2_Config.random_seed),
    "-lang", "smtlib", "-output-lang", "presentation",
    "-timeout", string_of_int (Real.ceil (Config.get ctxt SMT2_Config.timeout))]
in

val cvc3: SMT2_Solver.solver_config = {
  name = "cvc3_new",
  class = K SMTLIB2_Interface.smtlib2C,
  avail = make_avail "CVC3_NEW",
  command = make_command "CVC3_NEW",
  options = cvc3_options,
  default_max_relevant = 400 (* FUDGE *),
  supports_filter = false,
  outcome =
    on_first_line (outcome_of "Unsatisfiable." "Satisfiable." "Unknown."),
  cex_parser = NONE,
  replay = NONE }

end


(* Yices *)

val yices: SMT2_Solver.solver_config = {
  name = "yices_new",
  class = K SMTLIB2_Interface.smtlib2C,
  avail = make_avail "YICES_NEW",
  command = make_command "YICES_NEW",
  options = (fn ctxt => [
    "--rand-seed=" ^ string_of_int (Config.get ctxt SMT2_Config.random_seed),
    "--timeout=" ^
      string_of_int (Real.ceil (Config.get ctxt SMT2_Config.timeout)),
    "--smtlib"]),
  default_max_relevant = 350 (* FUDGE *),
  supports_filter = false,
  outcome = on_first_line (outcome_of "unsat" "sat" "unknown"),
  cex_parser = NONE,
  replay = NONE }


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
    val flag1 = Options.default_string @{option z3_non_commercial}
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
      error (Pretty.string_of (Pretty.para
        ("The SMT solver Z3 is not activated. To activate it, set the Isabelle \
         \system option \"z3_non_commercial\" to \"yes\" (e.g. via \
         \the Isabelle/jEdit menu Plugin Options / Isabelle / General)."))))

end

val z3_extensions = Attrib.setup_config_bool @{binding z3_new_extensions} (K false)

local
  fun z3_make_command name () = if_z3_non_commercial (make_command name)

  fun z3_options ctxt =
    ["REFINE_INJ_AXIOM=false" (* not supported by replay *),
     "-rs:" ^ string_of_int (Config.get ctxt SMT2_Config.random_seed),
     "-T:" ^ string_of_int (Real.ceil (Config.get ctxt SMT2_Config.timeout)),
     "-smt2"]

  fun z3_on_first_or_last_line solver_name lines =
    let
      fun junk l =
        if String.isPrefix "WARNING: Out of allocated virtual memory" l
        then raise SMT2_Failure.SMT SMT2_Failure.Out_Of_Memory
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
      handle SMT2_Failure.SMT _ => outcome (swap o split_last)
    end

  fun select_class ctxt =
    if Config.get ctxt z3_extensions then Z3_New_Interface.smtlib2_z3C
    else SMTLIB2_Interface.smtlib2C
in

val z3: SMT2_Solver.solver_config = {
  name = "z3_new",
  class = select_class,
  avail = make_avail "Z3_NEW",
  command = z3_make_command "Z3_NEW",
  options = z3_options,
  default_max_relevant = 350 (* FUDGE *),
  supports_filter = true,
  outcome = z3_on_first_or_last_line,
  cex_parser = NONE,
  replay = SOME Z3_New_Proof_Replay.replay }

end


(* overall setup *)

val _ = Theory.setup (
  SMT2_Solver.add_solver cvc3 #>
  SMT2_Solver.add_solver yices #>
  SMT2_Solver.add_solver z3)

end
