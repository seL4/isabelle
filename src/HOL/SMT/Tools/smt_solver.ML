(*  Title:      HOL/SMT/Tools/smt_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT_SOLVER =
sig
  exception SMT of string
  exception SMT_COUNTEREXAMPLE of bool * term list

  type proof_data = {
    context: Proof.context,
    output: string list,
    recon: SMT_Translate.recon }
  type solver_config = {
    command: {env_var: string, remote_name: string option},
    arguments: string list,
    interface: string list -> SMT_Translate.config,
    reconstruct: proof_data -> thm }

  (*options*)
  val timeout: int Config.T
  val with_timeout: Proof.context -> ('a -> 'b) -> 'a -> 'b
  val trace: bool Config.T
  val trace_msg: Proof.context -> ('a -> string) -> 'a -> unit

  (*certificates*)
  val fixed_certificates: bool Config.T
  val select_certificates: string -> Context.generic -> Context.generic

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


type proof_data = {
  context: Proof.context,
  output: string list,
  recon: SMT_Translate.recon }

type solver_config = {
  command: {env_var: string, remote_name: string option},
  arguments: string list,
  interface: string list -> SMT_Translate.config,
  reconstruct: proof_data -> thm }



(* SMT options *)

val (timeout, setup_timeout) = Attrib.config_int "smt_timeout" (K 30)

fun with_timeout ctxt f x =
  TimeLimit.timeLimit (Time.fromSeconds (Config.get ctxt timeout)) f x
  handle TimeLimit.TimeOut => raise SMT "timeout"

val (trace, setup_trace) = Attrib.config_bool "smt_trace" (K false)

fun trace_msg ctxt f x =
  if Config.get ctxt trace then tracing (f x) else ()



(* SMT certificates *)

val (fixed_certificates, setup_fixed_certificates) =
  Attrib.config_bool "smt_fixed" (K false)

structure Certificates = Generic_Data
(
  type T = Cache_IO.cache option
  val empty = NONE
  val extend = I
  fun merge (s, _) = s
)

fun select_certificates name = Certificates.put (
  if name = "" then NONE
  else SOME (Cache_IO.make (Path.explode name)))



(* interface to external solvers *)

local

fun choose {env_var, remote_name} =
  let
    val local_solver = getenv env_var
    val remote_solver = the_default "" remote_name
    val remote_url = getenv "REMOTE_SMT_URL"
  in
    if local_solver <> ""
    then 
     (tracing ("Invoking local SMT solver " ^ quote local_solver ^ " ...");
      [local_solver])
    else if remote_solver <> ""
    then
     (tracing ("Invoking remote SMT solver " ^ quote remote_solver ^ " at " ^
        quote remote_url ^ " ...");
      [getenv "REMOTE_SMT", remote_solver])
    else error ("Undefined Isabelle environment variable: " ^ quote env_var)
  end

fun make_cmd solver args problem_path proof_path = space_implode " " (
  map File.shell_quote (solver @ args) @
  [File.shell_path problem_path, "2>&1", ">", File.shell_path proof_path])

fun run ctxt cmd args input =
  (case Certificates.get (Context.Proof ctxt) of
    NONE => Cache_IO.run (make_cmd (choose cmd) args) input
  | SOME certs =>
      (case Cache_IO.lookup certs input of
        (NONE, key) =>
          if Config.get ctxt fixed_certificates
          then error ("Bad certificates cache: missing certificate")
          else Cache_IO.run_and_cache certs key (make_cmd (choose cmd) args)
            input
      | (SOME output, _) =>
         (tracing ("Using cached certificate from " ^
            File.shell_path (Cache_IO.cache_path_of certs) ^ " ...");
          output)))

in

fun run_solver ctxt cmd args input =
  let
    fun pretty tag ls = Pretty.string_of (Pretty.big_list tag
      (map Pretty.str ls))

    val _ = trace_msg ctxt (pretty "SMT problem:" o split_lines) input

    val (res, err) = with_timeout ctxt (run ctxt cmd args) input
    val _ = trace_msg ctxt (pretty "SMT solver:") err

    val ls = rev (dropwhile (equal "") (rev res))
    val _ = trace_msg ctxt (pretty "SMT result:") ls
  in ls end

end

fun invoke translate_config command arguments ctxt thms =
  thms
  |> SMT_Translate.translate translate_config ctxt
  |>> run_solver ctxt command arguments
  |> (fn (ls, recon) => {context=ctxt, output=ls, recon=recon})

fun gen_solver name solver ctxt prems =
  let
    val {command, arguments, interface, reconstruct} = solver ctxt
    val comments = ("solver: " ^ name) ::
      ("timeout: " ^ string_of_int (Config.get ctxt timeout)) ::
      "arguments:" :: arguments
  in
    SMT_Additional_Facts.add_facts prems
    |> SMT_Normalize.normalize ctxt 
    ||> invoke (interface comments) command arguments ctxt
    ||> reconstruct
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

fun select_solver name context =
  if is_none (lookup_solver (Context.theory_of context) name)
  then error ("SMT solver not registered: " ^ quote name)
  else Selected_Solver.map (K name) context

fun raw_solver_of context name =
  (case lookup_solver (Context.theory_of context) name of
    NONE => error "No SMT solver selected"
  | SOME (s, _) => s)

fun solver_of context =
  let val name = solver_name_of context
  in gen_solver name (raw_solver_of context name) end



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

  val has_topsort = Term.exists_type (Term.exists_subtype (fn
      TFree (_, []) => true
    | TVar (_, []) => true
    | _ => false))
in
fun smt_tac' pass_exns ctxt rules =
  Tactic.rtac @{thm ccontr} THEN'
  SUBPROOF (fn {context, prems, ...} =>
    let val thms = rules @ prems
    in
      if exists (has_topsort o Thm.prop_of) thms
      then fail_tac (trace_msg context I)
        "SMT: proof state contains the universal sort {}"
      else SAFE pass_exns (Tactic.rtac o smt_solver thms) context 1
    end) ctxt

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
  setup_fixed_certificates #>
  Attrib.setup (Binding.name "smt_certificates")
    (Scan.lift (OuterParse.$$$ "=" |-- Args.name) >>
      (Thm.declaration_attribute o K o select_certificates))
    "SMT certificates" #>
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
