(*  Title:      HOL/Tools/SMT/smt_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT_SOLVER =
sig
  datatype failure =
    Counterexample of bool * term list |
    Time_Out |
    Out_Of_Memory |
    Other_Failure of string
  val string_of_failure: Proof.context -> string -> failure -> string
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
  val filter_only: bool Config.T
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
  type solver = bool option -> Proof.context -> (int * thm) list ->
    int list * thm
  val add_solver: solver_config -> theory -> theory
  val set_solver_options: string -> string -> Context.generic ->
    Context.generic
  val all_solver_names_of: Context.generic -> string list
  val solver_name_of: Context.generic -> string
  val select_solver: string -> Context.generic -> Context.generic
  val solver_of: Context.generic -> solver
  val is_locally_installed: Proof.context -> bool

  (*filter*)
  val smt_filter: bool -> Time.time -> Proof.state -> ('a * thm) list -> int ->
    {outcome: failure option, used_facts: 'a list,
    run_time_in_msecs: int option}

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
  Out_Of_Memory |
  Other_Failure of string

fun string_of_failure ctxt _ (Counterexample (real, ex)) =
      let
        val msg = (if real then "C" else "Potential c") ^ "ounterexample found"
      in
        if null ex then msg ^ "."
        else Pretty.string_of (Pretty.big_list (msg ^ ":")
          (map (Syntax.pretty_term ctxt) ex))
      end
  | string_of_failure _ name Time_Out = name ^ " timed out."
  | string_of_failure _ name Out_Of_Memory = name ^ " ran out of memory."
  | string_of_failure _ _ (Other_Failure msg) = msg

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

val (filter_only, setup_filter_only) =
  Attrib.config_bool "smt_filter_only" (K false)

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

fun get_local_solver env_var =
  let val local_solver = getenv env_var
  in if local_solver <> "" then SOME local_solver else NONE end

local

fun choose (rm, env_var, is_remote, name) =
  let
    val force_local = (case rm of SOME false => true | _ => false)
    val force_remote = (case rm of SOME true => true | _ => false)
    val lsolver = get_local_solver env_var
    val remote_url = getenv "REMOTE_SMT_URL"
    val trace = if is_some rm then K () else tracing
  in
    if not force_remote andalso is_some lsolver
    then 
     (trace ("Invoking local SMT solver " ^ quote (the lsolver) ^ " ...");
      [the lsolver])
    else if not force_local andalso is_remote
    then
     (trace ("Invoking remote SMT solver " ^ quote name ^ " at " ^
        quote remote_url ^ " ...");
      [getenv "REMOTE_SMT", name])
    else if force_remote
    then error ("The SMT solver " ^ quote name ^ " is not remotely available.")
    else error ("The SMT solver " ^ quote name ^ " has not been found " ^
      "on this computer. Please set the Isabelle environment variable " ^
      quote env_var ^ ".")
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

fun trace_assms ctxt = trace_msg ctxt (Pretty.string_of o
  Pretty.big_list "SMT assertions:" o map (Display.pretty_thm ctxt o snd))

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
    |> tap (trace_assms ctxt)
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

fun trace_assumptions ctxt irules idxs =
  let
    val thms = filter (fn i => i >= 0) idxs
      |> map_filter (AList.lookup (op =) irules)
  in
    if Config.get ctxt trace_used_facts andalso length thms > 0
    then
      tracing (Pretty.string_of (Pretty.big_list "SMT used facts:"
        (map (Display.pretty_thm ctxt) thms)))
    else ()
  end

fun gen_solver name info rm ctxt irules =
  let
    val {env_var, is_remote, options, more_options, interface, reconstruct} =
      info
    val {extra_norm, translate} = interface
    val (with_datatypes, translate') =
      set_has_datatypes (Config.get ctxt datatypes) translate
    val cmd = (rm, env_var, is_remote, name)
  in
    (irules, ctxt)
    |-> SMT_Normalize.normalize extra_norm with_datatypes
    |-> invoke translate' name cmd more_options options
    |-> reconstruct
    |-> (fn (idxs, thm) => fn ctxt' => thm
    |> singleton (ProofContext.export ctxt' ctxt)
    |> discharge_definitions
    |> tap (fn _ => trace_assumptions ctxt irules idxs)
    |> pair idxs)
  end



(* solver store *)

type solver = bool option -> Proof.context -> (int * thm) list -> int list * thm

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

fun is_locally_installed ctxt =
  let
    val name = solver_name_of (Context.Proof ctxt)
    val {env_var, ...} = raw_solver_of (Context.Proof ctxt) name
  in is_some (get_local_solver env_var) end



(* SMT filter *)

val has_topsort = Term.exists_type (Term.exists_subtype (fn
    TFree (_, []) => true
  | TVar (_, []) => true
  | _ => false))

fun smt_solver rm ctxt irules =
  (* without this test, we would run into problems when atomizing the rules: *)
  if exists (has_topsort o Thm.prop_of o snd) irules
  then raise SMT (Other_Failure "proof state contains the universal sort {}")
  else solver_of (Context.Proof ctxt) rm ctxt irules

fun smt_filter run_remote time_limit st xrules i =
  let
    val {context, facts, goal} = Proof.goal st
    val ctxt =
      context
      |> Config.put timeout (Time.toSeconds time_limit)
      |> Config.put oracle false
      |> Config.put filter_only true
    val cprop =
      Thm.cprem_of goal i
      |> Thm.rhs_of o SMT_Normalize.atomize_conv ctxt
      |> Thm.capply @{cterm Trueprop} o Thm.capply @{cterm Not} o Thm.dest_arg
    val irs = map (pair ~1) (Thm.assume cprop :: facts)
    val rm = SOME run_remote
  in
    split_list xrules
    ||> distinct (op =) o fst o smt_solver rm ctxt o append irs o map_index I
    |-> map_filter o try o nth
    |> (fn xs => {outcome=NONE, used_facts=xs, run_time_in_msecs=NONE})
  end
  handle SMT fail => {outcome=SOME fail, used_facts=[], run_time_in_msecs=NONE}
  (* FIXME: measure runtime *)



(* SMT tactic *)

fun smt_tac' pass_exns ctxt rules =
  CONVERSION (SMT_Normalize.atomize_conv ctxt)
  THEN' Tactic.rtac @{thm ccontr}
  THEN' SUBPROOF (fn {context=cx, prems, ...} =>
    let
      fun solve () = snd (smt_solver NONE cx (map (pair ~1) (rules @ prems)))
      val name = solver_name_of (Context.Proof cx)
      val trace = trace_msg cx (prefix "SMT: " o string_of_failure cx name)
    in
      (if pass_exns then SOME (solve ())
       else (SOME (solve ()) handle SMT fail => (trace fail; NONE)))
      |> (fn SOME thm => Tactic.rtac thm 1 | _ => Tactical.no_tac)
    end) ctxt

val smt_tac = smt_tac' false

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
  setup_filter_only #>
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
