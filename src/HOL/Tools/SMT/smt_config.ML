(*  Title:      HOL/Tools/SMT/smt_config.ML
    Author:     Sascha Boehme, TU Muenchen

Configuration options and diagnostic tools for SMT.
*)

signature SMT_CONFIG =
sig
  (*solver*)
  type solver_info = {
    name: string,
    class: SMT_Utils.class,
    avail: unit -> bool,
    options: Proof.context -> string list }
  val add_solver: solver_info -> Context.generic -> Context.generic
  val set_solver_options: string * string -> Context.generic -> Context.generic
  val available_solvers_of: Proof.context -> string list
  val select_solver: string -> Context.generic -> Context.generic
  val solver_of: Proof.context -> string
  val solver_class_of: Proof.context -> SMT_Utils.class
  val solver_options_of: Proof.context -> string list

  (*options*)
  val oracle: bool Config.T
  val datatypes: bool Config.T
  val timeout: real Config.T
  val random_seed: int Config.T
  val fixed: bool Config.T
  val verbose: bool Config.T
  val traceN: string
  val trace: bool Config.T
  val trace_used_facts: bool Config.T
  val monomorph_limit: int Config.T
  val infer_triggers: bool Config.T
  val drop_bad_facts: bool Config.T
  val filter_only_facts: bool Config.T
  val debug_files: string Config.T

  (*tools*)
  val with_timeout: Proof.context -> ('a -> 'b) -> 'a -> 'b

  (*diagnostics*)
  val trace_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val verbose_msg: Proof.context -> ('a -> string) -> 'a -> unit

  (*certificates*)
  val select_certificates: string -> Context.generic -> Context.generic
  val certificates_of: Proof.context -> Cache_IO.cache option

  (*setup*)
  val setup: theory -> theory
  val print_setup: Proof.context -> unit
end

structure SMT_Config: SMT_CONFIG =
struct

(* solver *)

type solver_info = {
  name: string,
  class: SMT_Utils.class,
  avail: unit -> bool,
  options: Proof.context -> string list }

structure Solvers = Generic_Data
(
  type T = (solver_info * string list) Symtab.table * string option
  val empty = (Symtab.empty, NONE)
  val extend = I
  fun merge ((ss1, s), (ss2, _)) = (Symtab.merge (K true) (ss1, ss2), s (* FIXME merge options!? *))
)

fun set_solver_options (name, options) =
  let val opts = String.tokens (Symbol.is_ascii_blank o str) options
  in Solvers.map (apfst (Symtab.map_entry name (apsnd (K opts)))) end

fun add_solver (info as {name, ...} : solver_info) context =
  if Symtab.defined (fst (Solvers.get context)) name then
    error ("Solver already registered: " ^ quote name)
  else
    context
    |> Solvers.map (apfst (Symtab.update (name, (info, []))))
    |> Context.map_theory (Attrib.setup (Binding.name (name ^ "_options"))
        (Scan.lift (Parse.$$$ "=" |-- Args.name) >>
          (Thm.declaration_attribute o K o set_solver_options o pair name))
        ("Additional command line options for SMT solver " ^ quote name))

fun all_solvers_of ctxt = Symtab.keys (fst (Solvers.get (Context.Proof ctxt)))

fun solver_name_of ctxt = snd (Solvers.get (Context.Proof ctxt))

fun is_available ctxt name =
  (case Symtab.lookup (fst (Solvers.get (Context.Proof ctxt))) name of
    SOME ({avail, ...}, _) => avail ()
  | NONE => false)

fun available_solvers_of ctxt =
  filter (is_available ctxt) (all_solvers_of ctxt)

fun warn_solver name =
  warning ("The SMT solver " ^ quote name ^ " is not installed.")

fun select_solver name context =
  let
    val ctxt = Context.proof_of context
    val upd = Solvers.map (apsnd (K (SOME name)))
  in
    if not (member (op =) (all_solvers_of ctxt) name) then
      error ("Trying to select unknown solver: " ^ quote name)
    else if not (is_available ctxt name) then (warn_solver name; upd context)
    else upd context
  end

fun no_solver_err () = error "No SMT solver selected"

fun solver_of ctxt =
  (case solver_name_of ctxt of
    SOME name => name
  | NONE => no_solver_err ())

fun solver_info_of default select ctxt =
  (case Solvers.get (Context.Proof ctxt) of
    (solvers, SOME name) => select (Symtab.lookup solvers name)
  | (_, NONE) => default ())

fun solver_class_of ctxt =
  solver_info_of no_solver_err (#class o fst o the) ctxt

fun solver_options_of ctxt =
  let
    fun all_options NONE = []
      | all_options (SOME ({options, ...} : solver_info, opts)) =
          opts @ options ctxt
  in solver_info_of (K []) all_options ctxt end

val setup_solver =
  Attrib.setup @{binding smt_solver}
    (Scan.lift (Parse.$$$ "=" |-- Args.name) >>
      (Thm.declaration_attribute o K o select_solver))
    "SMT solver configuration"


(* options *)

val oracleN = "smt_oracle"
val (oracle, setup_oracle) = Attrib.config_bool oracleN (K true)

val datatypesN = "smt_datatypes"
val (datatypes, setup_datatypes) = Attrib.config_bool datatypesN (K false)

val timeoutN = "smt_timeout"
val (timeout, setup_timeout) = Attrib.config_real timeoutN (K 30.0)

val random_seedN = "smt_random_seed"
val (random_seed, setup_random_seed) = Attrib.config_int random_seedN (K 1)

val fixedN = "smt_fixed"
val (fixed, setup_fixed) = Attrib.config_bool fixedN (K false)

val verboseN = "smt_verbose"
val (verbose, setup_verbose) = Attrib.config_bool verboseN (K true)

val traceN = "smt_trace"
val (trace, setup_trace) = Attrib.config_bool traceN (K false)

val trace_used_factsN = "smt_trace_used_facts"
val (trace_used_facts, setup_trace_used_facts) =
  Attrib.config_bool trace_used_factsN (K false)

val monomorph_limitN = "smt_monomorph_limit"
val (monomorph_limit, setup_monomorph_limit) =
  Attrib.config_int monomorph_limitN (K 10)

val infer_triggersN = "smt_infer_triggers"
val (infer_triggers, setup_infer_triggers) =
  Attrib.config_bool infer_triggersN (K false)

val drop_bad_factsN = "smt_drop_bad_facts"
val (drop_bad_facts, setup_drop_bad_facts) =
  Attrib.config_bool drop_bad_factsN (K false)

val filter_only_factsN = "smt_filter_only_facts"
val (filter_only_facts, setup_filter_only_facts) =
  Attrib.config_bool filter_only_factsN (K false)

val debug_filesN = "smt_debug_files"
val (debug_files, setup_debug_files) =
  Attrib.config_string debug_filesN (K "")

val setup_options =
  setup_oracle #>
  setup_datatypes #>
  setup_timeout #>
  setup_random_seed #>
  setup_fixed #>
  setup_trace #>
  setup_verbose #>
  setup_monomorph_limit #>
  setup_infer_triggers #>
  setup_drop_bad_facts #>
  setup_filter_only_facts #>
  setup_trace_used_facts #>
  setup_debug_files


(* diagnostics *)

fun cond_trace flag f x = if flag then tracing ("SMT: " ^ f x) else ()

fun verbose_msg ctxt = cond_trace (Config.get ctxt verbose)

fun trace_msg ctxt = cond_trace (Config.get ctxt trace)


(* tools *)

fun with_timeout ctxt f x =
  TimeLimit.timeLimit (seconds (Config.get ctxt timeout)) f x
  handle TimeLimit.TimeOut => raise SMT_Failure.SMT SMT_Failure.Time_Out


(* certificates *)

structure Certificates = Generic_Data
(
  type T = Cache_IO.cache option
  val empty = NONE
  val extend = I
  fun merge (s, _) = s  (* FIXME merge options!? *)
)

val get_certificates_path =
  Option.map (Cache_IO.cache_path_of) o Certificates.get o Context.Proof

fun select_certificates name context = context |> Certificates.put (
  if name = "" then NONE
  else
    Path.explode name
    |> Path.append (Thy_Load.master_directory (Context.theory_of context))
    |> SOME o Cache_IO.make)

val certificates_of = Certificates.get o Context.Proof

val setup_certificates =
  Attrib.setup @{binding smt_certificates}
    (Scan.lift (Parse.$$$ "=" |-- Args.name) >>
      (Thm.declaration_attribute o K o select_certificates))
    "SMT certificates configuration"


(* setup *)

val setup =
  setup_solver #>
  setup_options #>
  setup_certificates

fun print_setup ctxt =
  let
    fun string_of_bool b = if b then "true" else "false"

    val names = available_solvers_of ctxt
    val ns = if null names then ["(none)"] else sort_strings names
    val n = the_default "(none)" (solver_name_of ctxt)
    val opts = solver_options_of ctxt
    
    val t = string_of_real (Config.get ctxt timeout)

    val certs_filename =
      (case get_certificates_path ctxt of
        SOME path => Path.implode path
      | NONE => "(disabled)")
  in
    Pretty.writeln (Pretty.big_list "SMT setup:" [
      Pretty.str ("Current SMT solver: " ^ n),
      Pretty.str ("Current SMT solver options: " ^ space_implode " " opts),
      Pretty.str_list "Available SMT solvers: "  "" ns,
      Pretty.str ("Current timeout: " ^ t ^ " seconds"),
      Pretty.str ("With proofs: " ^
        string_of_bool (not (Config.get ctxt oracle))),
      Pretty.str ("Certificates cache: " ^ certs_filename),
      Pretty.str ("Fixed certificates: " ^
        string_of_bool (Config.get ctxt fixed))])
  end

val _ =
  Outer_Syntax.improper_command "smt_status"
    ("show the available SMT solvers, the currently selected SMT solver, " ^
      "and the values of SMT configuration options")
    Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.keep (fn state =>
      print_setup (Toplevel.context_of state))))

end
