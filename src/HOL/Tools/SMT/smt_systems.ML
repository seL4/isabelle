(*  Title:      HOL/Tools/SMT/smt_systems.ML
    Author:     Sascha Boehme, TU Muenchen

Setup SMT solvers.
*)

signature SMT_SYSTEMS =
sig
  val cvc4_extensions: bool Config.T
  val z3_extensions: bool Config.T
end;

structure SMT_Systems: SMT_SYSTEMS =
struct

(* helper functions *)

fun check_tool var () =
  (case getenv var of
    "" => NONE
  | s =>
      if File.is_file (Path.variable var |> Path.expand |> Path.platform_exe)
      then SOME [s] else NONE);

fun make_avail name () = getenv (name ^ "_SOLVER") <> ""

fun make_command name () = [getenv (name ^ "_SOLVER")]

fun outcome_of unsat sat unknown timeout solver_name line =
  if String.isPrefix unsat line then SMT_Solver.Unsat
  else if String.isPrefix sat line then SMT_Solver.Sat
  else if String.isPrefix unknown line then SMT_Solver.Unknown
  else if String.isPrefix timeout line then SMT_Solver.Time_Out
  else raise SMT_Failure.SMT (SMT_Failure.Other_Failure ("Solver " ^ quote solver_name ^
    " failed -- enable tracing using the " ^ quote (Config.name_of SMT_Config.trace) ^
    " option for details"))

(* When used with bitvectors, CVC4 can produce error messages like:

$ISABELLE_TMP_PREFIX/... No set-logic command was given before this point.

These message should be ignored.
*)
fun is_blank_or_error_line "" = true
  | is_blank_or_error_line s =
  String.isPrefix "(error " s orelse String.isPrefix (getenv "ISABELLE_TMP_PREFIX") s

fun on_first_line test_outcome solver_name lines =
  let
    val split_first = (fn [] => ("", []) | l :: ls => (l, ls))
    val (l, ls) = split_first (drop_prefix is_blank_or_error_line lines)
  in (test_outcome solver_name l, ls) end

fun on_first_non_unsupported_line test_outcome solver_name lines =
  on_first_line test_outcome solver_name (filter (curry (op <>) "unsupported") lines)


(* CVC4 *)

val cvc4_extensions = Attrib.setup_config_bool \<^binding>\<open>cvc4_extensions\<close> (K false)

local
  fun cvc4_options ctxt =
    ["--no-stats",
     "--random-seed=" ^ string_of_int (Config.get ctxt SMT_Config.random_seed),
     "--lang=smt2"] @
    (case SMT_Config.get_timeout ctxt of
      NONE => []
    | SOME t => ["--tlimit", string_of_int (Time.toMilliseconds t)])

  fun select_class ctxt =
    if Config.get ctxt cvc4_extensions then
      if Config.get ctxt SMT_Config.higher_order then
        CVC4_Interface.hosmtlib_cvc4C
      else
        CVC4_Interface.smtlib_cvc4C
    else
      if Config.get ctxt SMT_Config.higher_order then
        SMTLIB_Interface.hosmtlibC
      else
        SMTLIB_Interface.smtlibC
in

val cvc4: SMT_Solver.solver_config = {
  name = "cvc4",
  class = select_class,
  avail = make_avail "CVC4",
  command = make_command "CVC4",
  options = cvc4_options,
  smt_options = [(":produce-unsat-cores", "true")],
  default_max_relevant = 400 (* FUDGE *),
  outcome = on_first_line (outcome_of "unsat" "sat" "unknown" "timeout"),
  parse_proof = SOME (K CVC4_Proof_Parse.parse_proof),
  replay = NONE }

end


(* veriT *)

local
  fun select_class ctxt =
    if Config.get ctxt SMT_Config.higher_order then
      SMTLIB_Interface.hosmtlibC
    else
      SMTLIB_Interface.smtlibC

  fun veriT_options ctxt =
   ["--proof-with-sharing",
    "--proof-define-skolems",
    "--proof-prune",
    "--proof-merge",
    "--disable-print-success",
    "--disable-banner"] @
    Verit_Proof.veriT_current_strategy (Context.Proof ctxt) @
    (case SMT_Config.get_timeout ctxt of
      NONE => []
    | SOME t => ["--max-time " ^ string_of_int (Time.toMilliseconds t)])
in

val veriT: SMT_Solver.solver_config = {
  name = "verit",
  class = select_class,
  avail = is_some o check_tool "ISABELLE_VERIT",
  command = the o check_tool "ISABELLE_VERIT",
  options = veriT_options,
  smt_options = [(":produce-proofs", "true")],
  default_max_relevant = 200 (* FUDGE *),
  outcome = on_first_non_unsupported_line (outcome_of "unsat" "sat" "unknown" "timeout"),
  parse_proof = SOME (K VeriT_Proof_Parse.parse_proof),
  replay = SOME Verit_Replay.replay }

end


(* Z3 *)

val z3_extensions = Attrib.setup_config_bool \<^binding>\<open>z3_extensions\<close> (K false)

local
  fun z3_options ctxt =
    ["smt.random_seed=" ^ string_of_int (Config.get ctxt SMT_Config.random_seed),
     "smt.refine_inj_axioms=false"] @
    (case SMT_Config.get_timeout ctxt of
      NONE => []
    | SOME t => ["-T:" ^ string_of_int (Real.ceil (Time.toReal t))]) @
    ["-smt2"]

  fun select_class ctxt =
    if Config.get ctxt z3_extensions then Z3_Interface.smtlib_z3C else SMTLIB_Interface.smtlibC
in

val z3: SMT_Solver.solver_config = {
  name = "z3",
  class = select_class,
  avail = make_avail "Z3",
  command = make_command "Z3",
  options = z3_options,
  smt_options = [(":produce-proofs", "true")],
  default_max_relevant = 350 (* FUDGE *),
  outcome = on_first_line (outcome_of "unsat" "sat" "unknown" "timeout"),
  parse_proof = SOME Z3_Replay.parse_proof,
  replay = SOME Z3_Replay.replay }

end

(* smt tactic *)
val parse_smt_options =
  Scan.optional
    (Args.parens (Args.name -- Scan.option (\<^keyword>\<open>,\<close> |-- Args.name)) >> apfst SOME)
    (NONE, NONE)

fun smt_method ((solver, stgy), thms) ctxt facts =
  let
    val default_solver = SMT_Config.solver_of ctxt
    val solver = the_default default_solver solver
    val _ = 
      if solver = "z3" andalso stgy <> NONE
      then warning ("No strategy is available for z3. Ignoring " ^ quote (the stgy)) 
      else ()
    val ctxt =
      ctxt
      |> (if stgy <> NONE then Context.proof_map (Verit_Proof.select_veriT_stgy (the stgy)) else I)
      |> Context.Proof
      |> SMT_Config.select_solver solver
      |> Context.proof_of
  in
    HEADGOAL (SOLVED' (SMT_Solver.smt_tac ctxt (thms @ facts)))
  end

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>smt\<close>
      (Scan.lift parse_smt_options -- Attrib.thms >> (METHOD oo smt_method))
      "Call to the SMT solvers veriT or z3")

(* overall setup *)

val _ = Theory.setup (
  SMT_Solver.add_solver cvc4 #>
  SMT_Solver.add_solver veriT #>
  SMT_Solver.add_solver z3)

end;
