(*  Title:      HOL/Tools/SMT/smt_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT_SOLVER =
sig
  exception SMT of string
  exception SMT_COUNTEREXAMPLE of bool * term list

  type interface = {
    extra_norm: SMT_Normalize.extra_norm,
    translate: SMT_Translate.config }
  type solver_config = {
    command: {env_var: string, remote_name: string option},
    arguments: string list,
    interface: interface,
    reconstruct: (string list * SMT_Translate.recon) -> Proof.context ->
      thm * Proof.context }

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
  val add_solver: string * (Proof.context -> solver_config) ->
    Context.generic -> Context.generic
  val all_solver_names_of: Context.generic -> string list
  val add_solver_info: string * solver_info -> Context.generic ->
    Context.generic
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
  extra_norm: SMT_Normalize.extra_norm,
  translate: SMT_Translate.config }

type solver_config = {
  command: {env_var: string, remote_name: string option},
  arguments: string list,
  interface: interface,
  reconstruct: (string list * SMT_Translate.recon) -> Proof.context ->
    thm * Proof.context }



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

val get_certificates_path =
  Option.map (Cache_IO.cache_path_of) o Certificates.get

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

fun trace_recon_data ctxt {typs, terms, ...} =
  let
    fun pretty_eq n p = Pretty.block [Pretty.str n, Pretty.str " = ", p]
    fun pretty_typ (n, T) = pretty_eq n (Syntax.pretty_typ ctxt T)
    fun pretty_term (n, t) = pretty_eq n (Syntax.pretty_term ctxt t)
  in
    trace_msg ctxt (fn () => Pretty.string_of (Pretty.big_list "SMT names:" [
      Pretty.big_list "sorts:" (map pretty_typ (Symtab.dest typs)),
      Pretty.big_list "functions:" (map pretty_term (Symtab.dest terms))])) ()
  end

fun invoke translate_config comments command arguments thms ctxt =
  thms
  |> SMT_Translate.translate translate_config ctxt comments
  ||> tap (trace_recon_data ctxt)
  |>> run_solver ctxt command arguments
  |> rpair ctxt

fun discharge_definitions thm =
  if Thm.nprems_of thm = 0 then thm
  else discharge_definitions (@{thm reflexive} RS thm)

fun gen_solver name solver ctxt prems =
  let
    val {command, arguments, interface, reconstruct} = solver ctxt
    val comments = ("solver: " ^ name) ::
      ("timeout: " ^ string_of_int (Config.get ctxt timeout)) ::
      "arguments:" :: arguments
    val {extra_norm, translate} = interface
  in
    (prems, ctxt)
    |-> SMT_Normalize.normalize extra_norm
    |-> invoke translate comments command arguments
    |-> reconstruct
    |-> (fn thm => fn ctxt' => thm
    |> singleton (ProofContext.export ctxt' ctxt)
    |> discharge_definitions)
  end



(* solver store *)

type solver = Proof.context -> thm list -> thm
type solver_info = Context.generic -> Pretty.T list

structure Solvers = Generic_Data
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
  if is_none (lookup_solver context name)
  then error ("SMT solver not registered: " ^ quote name)
  else Selected_Solver.map (K name) context

fun raw_solver_of context name =
  (case lookup_solver context name of
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
  CONVERSION (SMT_Normalize.atomize_conv ctxt)
  THEN' Tactic.rtac @{thm ccontr}
  THEN' SUBPROOF (fn {context, prems, ...} =>
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


fun print_setup context =
  let
    val t = string_of_int (Config.get_generic context timeout)
    val names = sort_strings (all_solver_names_of context)
    val ns = if null names then [no_solver] else names
    val take_info = (fn (_, []) => NONE | info => SOME info)
    val infos =
      Solvers.get context
      |> Symtab.dest
      |> map_filter (fn (n, (_, info)) => take_info (n, info context))
      |> sort (prod_ord string_ord (K EQUAL))
      |> map (fn (n, ps) => Pretty.big_list (n ^ ":") ps)
    val certs_filename =
      (case get_certificates_path context of
        SOME path => Path.implode path
      | NONE => "(disabled)")
    val fixed = if Config.get_generic context fixed_certificates then "true"
      else "false"
  in
    Pretty.writeln (Pretty.big_list "SMT setup:" [
      Pretty.str ("Current SMT solver: " ^ solver_name_of context),
      Pretty.str_list "Available SMT solvers: "  "" ns,
      Pretty.str ("Current timeout: " ^ t ^ " seconds"),
      Pretty.str ("Certificates cache: " ^ certs_filename),
      Pretty.str ("Fixed certificates: " ^ fixed),
      Pretty.big_list "Solver-specific settings:" infos])
  end

val _ = OuterSyntax.improper_command "smt_status"
  "Show the available SMT solvers and the currently selected solver."
  OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.keep (fn state =>
      print_setup (Context.Proof (Toplevel.context_of state)))))

end
