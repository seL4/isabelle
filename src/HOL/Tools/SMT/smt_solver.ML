(*  Title:      HOL/Tools/SMT/smt_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT_SOLVER =
sig
  datatype failure =
    Counterexample of bool * term list |
    Time_Out |
    Other_Failure of string
  val string_of_failure: Proof.context -> failure -> string
  exception SMT of failure

  type interface = {
    extra_norm: SMT_Normalize.extra_norm,
    translate: SMT_Translate.config }
  datatype outcome = Unsat | Sat | Unknown
  type solver_config = {
    name: string,
    env_var: string,
    is_remote: bool,
    options: Proof.context -> string list,
    interface: interface,
    outcome: string -> string list -> outcome * string list,
    cex_parser: (Proof.context -> SMT_Translate.recon -> string list ->
      term list) option,
    reconstruct: (Proof.context -> SMT_Translate.recon -> string list ->
      (int list * thm) * Proof.context) option }

  (*options*)
  val oracle: bool Config.T
  val datatypes: bool Config.T
  val timeout: int Config.T
  val with_timeout: Proof.context -> ('a -> 'b) -> 'a -> 'b
  val trace: bool Config.T
  val trace_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val trace_used_facts: bool Config.T

  (*certificates*)
  val fixed_certificates: bool Config.T
  val select_certificates: string -> Context.generic -> Context.generic

  (*solvers*)
  type solver = Proof.context -> (int * thm) list -> int list * thm
  val add_solver: solver_config -> theory -> theory
  val set_solver_options: string -> string -> Context.generic ->
    Context.generic
  val all_solver_names_of: Context.generic -> string list
  val solver_name_of: Context.generic -> string
  val select_solver: string -> Context.generic -> Context.generic
  val solver_of: Context.generic -> solver

  (*filter*)
  val smt_filter: Proof.state -> int -> ('a * thm) list ->
    'a list * failure option

  (*tactic*)
  val smt_tac': bool -> Proof.context -> thm list -> int -> Tactical.tactic
  val smt_tac: Proof.context -> thm list -> int -> Tactical.tactic

  (*setup*)
  val setup: theory -> theory
  val print_setup: Context.generic -> unit
end

structure SMT_Solver: SMT_SOLVER =
struct

datatype failure =
  Counterexample of bool * term list |
  Time_Out |
  Other_Failure of string

fun string_of_failure ctxt (Counterexample (real, ex)) =
      let
        val msg = if real then "Counterexample found"
          else "Potential counterexample found"
      in
        if null ex then msg ^ "."
        else Pretty.string_of (Pretty.big_list (msg ^ ":")
          (map (Syntax.pretty_term ctxt) ex))
      end
  | string_of_failure _ Time_Out = "Time out."
  | string_of_failure _ (Other_Failure msg) = msg

exception SMT of failure

type interface = {
  extra_norm: SMT_Normalize.extra_norm,
  translate: SMT_Translate.config }

datatype outcome = Unsat | Sat | Unknown

type solver_config = {
  name: string,
  env_var: string,
  is_remote: bool,
  options: Proof.context -> string list,
  interface: interface,
  outcome: string -> string list -> outcome * string list,
  cex_parser: (Proof.context -> SMT_Translate.recon -> string list ->
    term list) option,
  reconstruct: (Proof.context -> SMT_Translate.recon -> string list ->
    (int list * thm) * Proof.context) option }



(* SMT options *)

val (oracle, setup_oracle) = Attrib.config_bool "smt_oracle" (K true)

val (datatypes, setup_datatypes) = Attrib.config_bool "smt_datatypes" (K false)

val (timeout, setup_timeout) = Attrib.config_int "smt_timeout" (K 30)

fun with_timeout ctxt f x =
  TimeLimit.timeLimit (Time.fromSeconds (Config.get ctxt timeout)) f x
  handle TimeLimit.TimeOut => raise SMT Time_Out

val (trace, setup_trace) = Attrib.config_bool "smt_trace" (K false)

fun trace_msg ctxt f x =
  if Config.get ctxt trace then tracing (f x) else ()

val (trace_used_facts, setup_trace_used_facts) =
  Attrib.config_bool "smt_trace_used_facts" (K false)


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

fun choose (env_var, is_remote, remote_name) =
  let
    val local_solver = getenv env_var
    val remote_url = getenv "REMOTE_SMT_URL"
  in
    if local_solver <> ""
    then 
     (tracing ("Invoking local SMT solver " ^ quote local_solver ^ " ...");
      [local_solver])
    else if is_remote
    then
     (tracing ("Invoking remote SMT solver " ^ quote remote_name ^ " at " ^
        quote remote_url ^ " ...");
      [getenv "REMOTE_SMT", remote_name])
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

    val ls = rev (snd (chop_while (equal "") (rev res)))
    val _ = trace_msg ctxt (pretty "SMT result:") ls
  in ls end

end

fun trace_recon_data ctxt ({typs, terms, ...} : SMT_Translate.recon) =
  let
    fun pretty_eq n p = Pretty.block [Pretty.str n, Pretty.str " = ", p]
    fun pretty_typ (n, T) = pretty_eq n (Syntax.pretty_typ ctxt T)
    fun pretty_term (n, t) = pretty_eq n (Syntax.pretty_term ctxt t)
  in
    trace_msg ctxt (fn () => Pretty.string_of (Pretty.big_list "SMT names:" [
      Pretty.big_list "sorts:" (map pretty_typ (Symtab.dest typs)),
      Pretty.big_list "functions:" (map pretty_term (Symtab.dest terms))])) ()
  end

fun invoke translate_config name cmd more_opts options irules ctxt =
  let
    val args = more_opts @ options ctxt
    val comments = ("solver: " ^ name) ::
      ("timeout: " ^ string_of_int (Config.get ctxt timeout)) ::
      "arguments:" :: args
  in
    irules
    |> SMT_Translate.translate translate_config ctxt comments
    ||> tap (trace_recon_data ctxt)
    |>> run_solver ctxt cmd args
    |> rpair ctxt
  end

fun discharge_definitions thm =
  if Thm.nprems_of thm = 0 then thm
  else discharge_definitions (@{thm reflexive} RS thm)

fun set_has_datatypes with_datatypes translate =
  let
    val {prefixes, header, strict, builtins, serialize} = translate
    val {builtin_typ, builtin_num, builtin_fun, has_datatypes} = builtins
    val with_datatypes' = has_datatypes andalso with_datatypes
    val builtins' = {builtin_typ=builtin_typ, builtin_num=builtin_num,
      builtin_fun=builtin_fun, has_datatypes=with_datatypes}
    val translate' = {prefixes=prefixes, header=header, strict=strict,
      builtins=builtins', serialize=serialize}
  in (with_datatypes', translate') end

fun gen_solver name info ctxt irules =
  let
    val {env_var, is_remote, options, more_options, interface, reconstruct} =
      info
    val {extra_norm, translate} = interface
    val (with_datatypes, translate') =
      set_has_datatypes (Config.get ctxt datatypes) translate
  in
    (irules, ctxt)
    |-> SMT_Normalize.normalize extra_norm with_datatypes
    |-> invoke translate' name (env_var, is_remote, name) more_options options
    |-> reconstruct
    |-> (fn (idxs, thm) => fn ctxt' => thm
    |> singleton (ProofContext.export ctxt' ctxt)
    |> discharge_definitions
    |> pair idxs)
  end



(* solver store *)

type solver = Proof.context -> (int * thm) list -> int list * thm

type solver_info = {
  env_var: string,
  is_remote: bool,
  options: Proof.context -> string list,
  more_options: string list,
  interface: interface,
  reconstruct: string list * SMT_Translate.recon -> Proof.context ->
    (int list * thm) * Proof.context }

structure Solvers = Generic_Data
(
  type T = solver_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
    handle Symtab.DUP name => error ("Duplicate SMT solver: " ^ quote name)
)

val no_solver = "(none)"

fun set_solver_options name opts = Solvers.map (Symtab.map_entry name (fn
  {env_var, is_remote, options, interface, reconstruct, ...} =>
  {env_var=env_var, is_remote=is_remote, options=options,
   more_options=String.tokens (Symbol.is_ascii_blank o str) opts,
   interface=interface, reconstruct=reconstruct}))

local
  fun finish outcome cex_parser reconstruct ocl (output, recon) ctxt =
    (case outcome output of
      (Unsat, ls) =>
        if not (Config.get ctxt oracle) andalso is_some reconstruct
        then the reconstruct ctxt recon ls
        else (([], ocl ()), ctxt)
    | (result, ls) =>
        let val ts = (case cex_parser of SOME f => f ctxt recon ls | _ => [])
        in raise SMT (Counterexample (result = Sat, ts)) end)
in

fun add_solver cfg =
  let
    val {name, env_var, is_remote, options, interface, outcome, cex_parser,
      reconstruct} = cfg

    fun core_oracle () = @{cprop False}

    fun solver ocl = { env_var=env_var, is_remote=is_remote, options=options,
      more_options=[], interface=interface,
      reconstruct=finish (outcome name) cex_parser reconstruct ocl }
  in
    Thm.add_oracle (Binding.name name, core_oracle) #-> (fn (_, ocl) =>
    Context.theory_map (Solvers.map (Symtab.update_new (name, solver ocl)))) #>
    Attrib.setup (Binding.name (name ^ "_options"))
      (Scan.lift (Parse.$$$ "=" |-- Args.name) >>
        (Thm.declaration_attribute o K o set_solver_options name))
      ("Additional command line options for SMT solver " ^ quote name)
  end

end

val all_solver_names_of = Symtab.keys o Solvers.get
val lookup_solver = Symtab.lookup o Solvers.get



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
  | SOME s => s)

fun solver_of context =
  let val name = solver_name_of context
  in gen_solver name (raw_solver_of context name) end



(* SMT filter *)

val has_topsort = Term.exists_type (Term.exists_subtype (fn
    TFree (_, []) => true
  | TVar (_, []) => true
  | _ => false))

fun smt_solver ctxt irules =
  (* without this test, we would run into problems when atomizing the rules: *)
  if exists (has_topsort o Thm.prop_of o snd) irules
  then raise SMT (Other_Failure "proof state contains the universal sort {}")
  else solver_of (Context.Proof ctxt) ctxt irules

fun smt_filter st i xrules =
  let
    val {context, facts, goal} = Proof.goal st
    val cprop =
      Thm.cprem_of goal i
      |> Thm.rhs_of o SMT_Normalize.atomize_conv context
      |> Thm.capply @{cterm Trueprop} o Thm.capply @{cterm Not} o Thm.dest_arg
    val irs = map (pair ~1) (Thm.assume cprop :: facts)
  in
    split_list xrules
    ||>> solver_of (Context.Proof context) context o append irs o map_index I
    |>> uncurry (map_filter o try o nth) o apsnd (distinct (op =))
    |> rpair NONE o fst
  end
  handle SMT fail => ([], SOME fail)



(* SMT tactic *)

local
  fun fail_tac f msg st = (f msg; Tactical.no_tac st)

  fun SAFE pass_exns tac ctxt i st =
    if pass_exns then tac ctxt i st
    else (tac ctxt i st handle SMT fail => fail_tac
      (trace_msg ctxt (prefix "SMT: ") o string_of_failure ctxt) fail st)
in

fun smt_tac' pass_exns ctxt rules =
  CONVERSION (SMT_Normalize.atomize_conv ctxt)
  THEN' Tactic.rtac @{thm ccontr}
  THEN' SUBPROOF (fn {context, prems, ...} =>
    let fun solve cx = snd (smt_solver cx (map (pair ~1) (rules @ prems)))
    in SAFE pass_exns (Tactic.rtac o solve) context 1 end) ctxt

val smt_tac = smt_tac' false

end

val smt_method =
  Scan.optional Attrib.thms [] >>
  (fn thms => fn ctxt => METHOD (fn facts =>
    HEADGOAL (smt_tac ctxt (thms @ facts))))



(* setup *)

val setup =
  Attrib.setup @{binding smt_solver}
    (Scan.lift (Parse.$$$ "=" |-- Args.name) >>
      (Thm.declaration_attribute o K o select_solver))
    "SMT solver configuration" #>
  setup_oracle #>
  setup_datatypes #>
  setup_timeout #>
  setup_trace #>
  setup_trace_used_facts #>
  setup_fixed_certificates #>
  Attrib.setup @{binding smt_certificates}
    (Scan.lift (Parse.$$$ "=" |-- Args.name) >>
      (Thm.declaration_attribute o K o select_certificates))
    "SMT certificates" #>
  Method.setup @{binding smt} smt_method
    "Applies an SMT solver to the current goal."


fun print_setup context =
  let
    val t = string_of_int (Config.get_generic context timeout)
    val names = sort_strings (all_solver_names_of context)
    val ns = if null names then [no_solver] else names
    val n = solver_name_of context
    val opts =
      (case Symtab.lookup (Solvers.get context) n of
        NONE => []
      | SOME {more_options, options, ...} =>
          more_options @ options (Context.proof_of context))
    val certs_filename =
      (case get_certificates_path context of
        SOME path => Path.implode path
      | NONE => "(disabled)")
    val fixed = if Config.get_generic context fixed_certificates then "true"
      else "false"
  in
    Pretty.writeln (Pretty.big_list "SMT setup:" [
      Pretty.str ("Current SMT solver: " ^ n),
      Pretty.str ("Current SMT solver options: " ^ space_implode " " opts),
      Pretty.str_list "Available SMT solvers: "  "" ns,
      Pretty.str ("Current timeout: " ^ t ^ " seconds"),
      Pretty.str ("With proofs: " ^
        (if Config.get_generic context oracle then "false" else "true")),
      Pretty.str ("Certificates cache: " ^ certs_filename),
      Pretty.str ("Fixed certificates: " ^ fixed)])
  end

val _ =
  Outer_Syntax.improper_command "smt_status"
    "show the available SMT solvers and the currently selected solver"
    Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.keep (fn state =>
      print_setup (Context.Proof (Toplevel.context_of state)))))

end
