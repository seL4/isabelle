(*  Title:      HOL/SMT/Tools/smt_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT_SOLVER =
sig
  exception SMT of string
  exception SMT_COUNTEREXAMPLE of bool * term list

  type interface = {
    normalize: SMT_Normalize.config list,
    translate: SMT_Translate.config }
  type proof_data = {
    context: Proof.context,
    output: string list,
    recon: SMT_Translate.recon,
    assms: thm list option }
  type solver_config = {
    command: {env_var: string, remote_name: string option},
    arguments: string list,
    interface: interface,
    reconstruct: proof_data -> thm }

  (*options*)
  val timeout: int Config.T
  val with_timeout: Proof.context -> ('a -> 'b) -> 'a -> 'b
  val trace: bool Config.T
  val trace_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val record: bool Config.T
  val certificates: string Config.T

  (*solvers*)
  type solver = Proof.context -> thm list -> thm
  type solver_info = Context.generic -> Pretty.T list
  val add_solver: string * (Proof.context -> solver_config) -> theory ->
    theory
  val all_solver_names_of: theory -> string list
  val add_solver_info: string * solver_info -> theory -> theory
  val solver_name_of: Context.generic -> string
  val select_solver: string -> Context.generic -> Context.generic
  val solver_of: Context.generic -> solver

  (*tactic*)
  val smt_tac': bool -> Proof.context -> thm list -> int -> Tactical.tactic
  val smt_tac: Proof.context -> thm list -> int -> Tactical.tactic

  (*setup*)
  val setup: theory -> theory
  val print_setup: Context.generic -> unit
end

structure SMT_Solver: SMT_SOLVER =
struct

exception SMT of string
exception SMT_COUNTEREXAMPLE of bool * term list


type interface = {
  normalize: SMT_Normalize.config list,
  translate: SMT_Translate.config }

type proof_data = {
  context: Proof.context,
  output: string list,
  recon: SMT_Translate.recon,
  assms: thm list option }

type solver_config = {
  command: {env_var: string, remote_name: string option},
  arguments: string list,
  interface: interface,
  reconstruct: proof_data -> thm }


(* SMT options *)

val (timeout, setup_timeout) = Attrib.config_int "smt_timeout" 30

fun with_timeout ctxt f x =
  TimeLimit.timeLimit (Time.fromSeconds (Config.get ctxt timeout)) f x
  handle TimeLimit.TimeOut => raise SMT "timeout"

val (trace, setup_trace) = Attrib.config_bool "smt_trace" false

fun trace_msg ctxt f x =
  if Config.get ctxt trace then tracing (f x) else ()

val (record, setup_record) = Attrib.config_bool "smt_record" true
val no_certificates = ""
val (certificates, setup_certificates) =
  Attrib.config_string "smt_certificates" no_certificates



(* interface to external solvers *)

local

fun with_files ctxt f =
  let
    val paths as (problem_path, proof_path) =
      "smt-" ^ serial_string ()
      |> (fn n => (n, n ^ ".proof"))
      |> pairself (File.tmp_path o Path.explode)

    val y = Exn.capture f (problem_path, proof_path)

    val _ = pairself (try File.rm) paths
  in Exn.release y end

fun invoke ctxt output f (paths as (problem_path, proof_path)) =
  let
    fun pretty tag ls = Pretty.string_of (Pretty.big_list tag
      (map Pretty.str ls))

    val x = File.open_output output problem_path
    val _ = trace_msg ctxt (pretty "SMT problem:" o split_lines o File.read)
      problem_path

    val (s, _) = with_timeout ctxt f paths
    val _ = trace_msg ctxt (pretty "SMT solver:") (split_lines s)

    fun lines_of path = the_default [] (try (File.fold_lines cons path) [])
    val ls = rev (dropwhile (equal "") (lines_of proof_path))
    val _ = trace_msg ctxt (pretty "SMT result:") ls
  in (x, ls) end

fun choose {env_var, remote_name} =
  let
    val local_solver = getenv env_var
    val remote_solver = the_default "" remote_name
    val remote_url = getenv "REMOTE_SMT_URL"
  in
    if local_solver <> ""
    then (["local", local_solver],
      "Invoking local SMT solver " ^ quote local_solver ^ " ...")
    else if remote_solver <> "" andalso remote_url <> ""
    then (["remote", remote_solver],
      "Invoking remote SMT solver " ^ quote remote_solver ^ " at " ^
      quote remote_url ^ " ...")
    else error ("Undefined Isabelle environment variable: " ^ quote env_var)
  end

fun run ctxt cmd args (problem_path, proof_path) =
  let
    val certs = Config.get ctxt certificates
    val certs' = 
      if certs = no_certificates then "-"
      else File.shell_path (Path.explode certs)
    val (solver, msg) =
      if certs = no_certificates orelse Config.get ctxt record
      then choose cmd
      else (["certificate"], "Using certificate from " ^ quote certs' ^ " ...")
    val _ = tracing msg
  in
    system_out (space_implode " " ("perl -w" ::
      File.shell_path (Path.explode (getenv "RUN_SMT_SOLVER")) :: certs' ::
      map File.shell_quote (solver @ args) @
      map File.shell_path [problem_path, proof_path]))
  end

in

fun run_solver ctxt cmd args output =
  with_files ctxt (invoke ctxt output (run ctxt cmd args))

end

fun make_proof_data ctxt ((recon, thms), ls) =
  {context=ctxt, output=ls, recon=recon, assms=SOME thms}

fun gen_solver solver ctxt prems =
  let
    val {command, arguments, interface, reconstruct} = solver ctxt
    val {normalize=nc, translate=tc} = interface
    val thy = ProofContext.theory_of ctxt
  in
    SMT_Normalize.normalize nc ctxt prems
    ||> run_solver ctxt command arguments o SMT_Translate.translate tc thy
    ||> reconstruct o make_proof_data ctxt
    |-> fold SMT_Normalize.discharge_definition
  end


(* solver store *)

type solver = Proof.context -> thm list -> thm
type solver_info = Context.generic -> Pretty.T list

structure Solvers = Theory_Data
(
  type T = ((Proof.context -> solver_config) * solver_info) Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
    handle Symtab.DUP name => error ("Duplicate SMT solver: " ^ quote name)
)

val no_solver = "(none)"
val add_solver = Solvers.map o Symtab.update_new o apsnd (rpair (K []))
val all_solver_names_of = Symtab.keys o Solvers.get
val lookup_solver = Symtab.lookup o Solvers.get
fun add_solver_info (n, i) = Solvers.map (Symtab.map_entry n (apsnd (K i)))


(* selected solver *)

structure Selected_Solver = Generic_Data
(
  type T = string
  val empty = no_solver
  val extend = I
  fun merge (s, _) = s
)

val solver_name_of = Selected_Solver.get

fun select_solver name gen =
  if is_none (lookup_solver (Context.theory_of gen) name)
  then error ("SMT solver not registered: " ^ quote name)
  else Selected_Solver.map (K name) gen

fun raw_solver_of gen =
  (case lookup_solver (Context.theory_of gen) (solver_name_of gen) of
    NONE => error "No SMT solver selected"
  | SOME (s, _) => s)

val solver_of = gen_solver o raw_solver_of


(* SMT tactic *)

local
  fun pretty_cex ctxt (real, ex) =
    let
      val msg = if real then "SMT: counterexample found"
        else "SMT: potential counterexample found"
    in
      if null ex then msg ^ "."
      else Pretty.string_of (Pretty.big_list (msg ^ ":")
        (map (Syntax.pretty_term ctxt) ex))
    end

  fun fail_tac f msg st = (f msg; Tactical.no_tac st)

  fun SAFE pass_exns tac ctxt i st =
    if pass_exns then tac ctxt i st
    else (tac ctxt i st
      handle SMT msg => fail_tac (trace_msg ctxt (prefix "SMT: ")) msg st
           | SMT_COUNTEREXAMPLE ce => fail_tac tracing (pretty_cex ctxt ce) st)

  fun smt_solver rules ctxt = solver_of (Context.Proof ctxt) ctxt rules
in
fun smt_tac' pass_exns ctxt rules =
  Tactic.rtac @{thm ccontr} THEN'
  SUBPROOF (fn {context, prems, ...} =>
    SAFE pass_exns (Tactic.rtac o smt_solver (rules @ prems)) context 1) ctxt

val smt_tac = smt_tac' false
end

val smt_method =
  Scan.optional Attrib.thms [] >>
  (fn thms => fn ctxt => METHOD (fn facts =>
    HEADGOAL (smt_tac ctxt (thms @ facts))))


(* setup *)

val setup =
  Attrib.setup (Binding.name "smt_solver")
    (Scan.lift (OuterParse.$$$ "=" |-- Args.name) >>
      (Thm.declaration_attribute o K o select_solver))
    "SMT solver configuration" #>
  setup_timeout #>
  setup_trace #>
  setup_record #>
  setup_certificates #>
  Method.setup (Binding.name "smt") smt_method
    "Applies an SMT solver to the current goal."


fun print_setup gen =
  let
    val t = string_of_int (Config.get_generic gen timeout)
    val names = sort_strings (all_solver_names_of (Context.theory_of gen))
    val ns = if null names then [no_solver] else names
    val take_info = (fn (_, []) => NONE | info => SOME info)
    val infos =
      Context.theory_of gen
      |> Symtab.dest o Solvers.get
      |> map_filter (fn (n, (_, info)) => take_info (n, info gen))
      |> sort (prod_ord string_ord (K EQUAL))
      |> map (fn (n, ps) => Pretty.big_list (n ^ ":") ps)
  in
    Pretty.writeln (Pretty.big_list "SMT setup:" [
      Pretty.str ("Current SMT solver: " ^ solver_name_of gen),
      Pretty.str_list "Available SMT solvers: "  "" ns,
      Pretty.str ("Current timeout: " ^ t ^ " seconds"),
      Pretty.big_list "Solver-specific settings:" infos])
  end

val _ = OuterSyntax.improper_command "smt_status"
  "Show the available SMT solvers and the currently selected solver."
  OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.keep (fn state =>
      print_setup (Context.Proof (Toplevel.context_of state)))))

end
