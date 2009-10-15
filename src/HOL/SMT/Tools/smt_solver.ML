(*  Title:      HOL/SMT/Tools/smt_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT_SOLVER =
sig
  exception SMT_COUNTEREXAMPLE of bool * term list

  datatype interface = Interface of {
    normalize: SMT_Normalize.config list,
    translate: SMT_Translate.config }

  datatype proof_data = ProofData of {
    context: Proof.context,
    output: string list,
    recon: SMT_Translate.recon,
    assms: thm list option }

  datatype solver_config = SolverConfig of {
    name: {env_var: string, remote_name: string},
    interface: interface,
    arguments: string list,
    reconstruct: proof_data -> thm }

  (*options*)
  val timeout: int Config.T
  val with_timeout: Proof.context -> ('a -> 'b) -> 'a -> 'b
  val trace: bool Config.T
  val trace_msg: Proof.context -> ('a -> string) -> 'a -> unit

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

exception SMT_COUNTEREXAMPLE of bool * term list


datatype interface = Interface of {
  normalize: SMT_Normalize.config list,
  translate: SMT_Translate.config }

datatype proof_data = ProofData of {
  context: Proof.context,
  output: string list,
  recon: SMT_Translate.recon,
  assms: thm list option }

datatype solver_config = SolverConfig of {
  name: {env_var: string, remote_name: string},
  interface: interface,
  arguments: string list,
  reconstruct: proof_data -> thm }


(* SMT options *)

val (timeout, setup_timeout) = Attrib.config_int "smt_timeout" 30

fun with_timeout ctxt f x =
  TimeLimit.timeLimit (Time.fromSeconds (Config.get ctxt timeout)) f x
  handle TimeLimit.TimeOut => error ("SMT: timeout")

val (trace, setup_trace) = Attrib.config_bool "smt_trace" false

fun trace_msg ctxt f x =
  if Config.get ctxt trace then tracing (f x) else ()


(* interface to external solvers *)

local

fun with_tmp_files f x =
  let
    fun tmp_path () = File.tmp_path (Path.explode ("smt-" ^ serial_string ()))
    val in_path = tmp_path () and out_path = tmp_path ()
    val y = Exn.capture (f in_path out_path) x
    val _ = try File.rm in_path and _ = try File.rm out_path
  in Exn.release y end

fun run in_path out_path (ctxt, cmd, output) =
  let
    val x = File.open_output output in_path
    val _ = trace_msg ctxt File.read in_path

    val _ = with_timeout ctxt system_out (cmd in_path out_path)
    fun lines_of path = the_default [] (try (File.fold_lines cons out_path) [])
    val ls = rev (dropwhile (equal "") (lines_of out_path))
    val _ = trace_msg ctxt cat_lines ls
  in (x, ls) end

in

fun run_solver ctxt {env_var, remote_name} args output =
  let
    val qf = File.shell_path and qq = File.shell_quote
    val path = getenv env_var and remote = getenv "REMOTE_SMT_SOLVER"
    fun cmd f1 f2 =
      if path <> ""
      then map qq (path :: args) @ [qf f1, ">", qf f2]
      else "perl -w" :: map qq (remote :: remote_name :: args) @ [qf f1, qf f2]
  in with_tmp_files run (ctxt, space_implode " " oo cmd, output) end

end

fun make_proof_data ctxt ((recon, thms), ls) =
  ProofData {context=ctxt, output=ls, recon=recon, assms=SOME thms}

fun gen_solver solver ctxt prems =
  let
    val SolverConfig {name, interface, arguments, reconstruct} = solver ctxt
    val Interface {normalize=nc, translate=tc} = interface
    val thy = ProofContext.theory_of ctxt
  in
    SMT_Normalize.normalize nc ctxt prems
    ||> run_solver ctxt name arguments o SMT_Translate.translate tc thy
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

structure SelectedSolver = GenericDataFun
(
  type T = serial * string
  val empty = (serial (), no_solver)
  val extend = I
  fun merge _ (sl1 as (s1, _), sl2 as (s2, _)) = if s1 > s2 then sl1 else sl2
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

fun smt_unsat_tac solver ctxt rules =
  Tactic.rtac @{thm ccontr} THEN'
  SUBPROOF (fn {context, prems, ...} =>
    Tactic.rtac (solver context (rules @ prems)) 1) ctxt

fun pretty_counterex ctxt (real, ex) =
  let
    val msg = if real then "Counterexample found:"
      else "Potential counterexample found:"
    val cex = if null ex then [Pretty.str "(no assignments)"]
      else map (Syntax.pretty_term ctxt) ex
  in Pretty.string_of (Pretty.big_list msg cex) end

fun smt_tac' pass_smt_exns ctxt =
  let
    val solver = solver_of (Context.Proof ctxt)
    fun safe_solver ctxt thms = solver ctxt thms
      handle SMT_COUNTEREXAMPLE cex => error (pretty_counterex ctxt cex)
    val solver' = if pass_smt_exns then solver else safe_solver
  in smt_unsat_tac solver' ctxt end

val smt_tac = smt_tac' false


(* setup *)

val setup =
  Attrib.setup (Binding.name "smt_solver")
    (Scan.lift (OuterParse.$$$ "=" |-- Args.name) >>
      (Thm.declaration_attribute o K o select_solver))
    "SMT solver configuration" #>
  setup_timeout #>
  setup_trace

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

end
