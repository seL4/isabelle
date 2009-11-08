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
  val keep: string Config.T
  val cert: string Config.T

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

val (keep, setup_keep) = Attrib.config_string "smt_keep" ""
val (cert, setup_cert) = Attrib.config_string "smt_cert" ""


(* interface to external solvers *)

local

fun with_files ctxt f =
  let
    fun make_names n = (n, n ^ ".proof")

    val keep' = Config.get ctxt keep
    val paths as (problem_path, proof_path) =
      if keep' <> "" andalso File.exists (Path.dir (Path.explode keep'))
      then pairself Path.explode (make_names keep')
      else pairself (File.tmp_path o Path.explode)
        (make_names ("smt-" ^ serial_string ()))

    val y = Exn.capture f (problem_path, proof_path)

    val _ = if keep' = "" then (pairself (try File.rm) paths; ()) else ()
  in Exn.release y end

fun invoke ctxt output f (paths as (problem_path, proof_path)) =
  let
    fun pretty tag ls = Pretty.string_of (Pretty.big_list tag
      (map Pretty.str ls))

    val x = File.open_output output problem_path
    val _ = trace_msg ctxt (pretty "SMT problem:" o split_lines o File.read)
      problem_path

    val _ = with_timeout ctxt f paths
    fun lines_of path = the_default [] (try (File.fold_lines cons path) [])
    val ls = rev (dropwhile (equal "") (lines_of proof_path))
    val _ = trace_msg ctxt (pretty "SMT result:") ls
  in (x, ls) end

val expand_name = Path.implode o Path.expand o Path.explode 

fun run_perl name args ps =
  system_out (space_implode " " ("perl -w" ::
    File.shell_path (Path.explode (getenv name)) ::
    map File.shell_quote args @ ps))

fun use_certificate ctxt ps =
  let val name = Config.get ctxt cert
  in
    if name = "" then false
    else
     (tracing ("Using certificate " ^ quote (expand_name name) ^ " ...");
      run_perl "CERT_SMT_SOLVER" [expand_name name] ps;
      true)
  end

fun run_locally f ctxt env_var args ps =
  if getenv env_var = ""
  then f ("Undefined Isabelle environment variable: " ^ quote env_var)
  else
    let val app = Path.expand (Path.explode (getenv env_var))
    in
      if not (File.exists app)
      then f ("No such file: " ^ quote (Path.implode app))
      else
       (tracing ("Invoking local SMT solver " ^ quote (Path.implode app) ^
          " ...");
        system_out (space_implode " " (File.shell_path app ::
        map File.shell_quote args @ ps)); ())
    end

fun run_remote remote_name args ps msg =
  (case remote_name of
    NONE => error msg
  | SOME name =>
      let
        val url = getenv "REMOTE_SMT_URL"
        val _ = tracing ("Invoking remote SMT solver " ^ quote name ^ " at " ^
          quote url ^ " ...")
      in (run_perl "REMOTE_SMT_SOLVER" (url :: name :: args) ps; ()) end)

fun run ctxt {env_var, remote_name} args (problem_path, proof_path) =
  let val ps = [File.shell_path problem_path, ">", File.shell_path proof_path]
  in
    if use_certificate ctxt ps then ()
    else run_locally (run_remote remote_name args ps) ctxt env_var args ps
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

structure Solvers = TheoryDataFun
(
  type T = ((Proof.context -> solver_config) * solver_info) Symtab.table
  val empty = Symtab.empty
  val copy = I
  val extend = I
  fun merge _ = Symtab.merge (K true)
    handle Symtab.DUP name => error ("Duplicate SMT solver: " ^ quote name)
)

val no_solver = "(none)"
val add_solver = Solvers.map o Symtab.update_new o apsnd (rpair (K []))
val all_solver_names_of = Symtab.keys o Solvers.get
val lookup_solver = Symtab.lookup o Solvers.get
fun add_solver_info (n, i) = Solvers.map (Symtab.map_entry n (apsnd (K i)))


(* selected solver *)

structure SelectedSolver = Generic_Data
(
  type T = serial * string
  val empty = (serial (), no_solver)
  val extend = I
  fun merge (sl1 as (s1, _), sl2 as (s2, _)) =
    if s1 > s2 then sl1 else sl2   (* FIXME depends on accidental load order !?! *)
)

val solver_name_of = snd o SelectedSolver.get

fun select_solver name gen =
  if is_none (lookup_solver (Context.theory_of gen) name)
  then error ("SMT solver not registered: " ^ quote name)
  else SelectedSolver.map (K (serial (), name)) gen

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
  setup_keep #>
  setup_cert #>
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
