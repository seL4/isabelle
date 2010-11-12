(*  Title:      HOL/Tools/SMT/smt_config.ML
    Author:     Sascha Boehme, TU Muenchen

Configuration options and diagnostic tools for SMT.
*)

signature SMT_CONFIG =
sig
  (*solver*)
  val add_solver: string -> Context.generic -> Context.generic
  val set_solver_options: string * string -> Context.generic -> Context.generic
  val select_solver: string -> Context.generic -> Context.generic
  val solver_of: Proof.context -> string
  val solver_options_of: Proof.context -> string list

  (*options*)
  val oracle: bool Config.T
  val datatypes: bool Config.T
  val timeout: real Config.T
  val fixed: bool Config.T
  val verbose: bool Config.T
  val traceN: string
  val trace: bool Config.T
  val trace_used_facts: bool Config.T
  val monomorph_limit: int Config.T
  val drop_bad_facts: bool Config.T
  val filter_only_facts: bool Config.T

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

structure Solvers = Generic_Data
(
  type T = string list Symtab.table * string option
  val empty = (Symtab.empty, NONE)
  val extend = I
  fun merge ((ss1, s), (ss2, _)) = (Symtab.merge (K true) (ss1, ss2), s)
)

fun set_solver_options (name, options) =
  let val opts = String.tokens (Symbol.is_ascii_blank o str) options
  in Solvers.map (apfst (Symtab.map_entry name (K opts))) end

fun add_solver name context =
  if Symtab.defined (fst (Solvers.get context)) name then
    error ("Solver already registered: " ^ quote name)
  else
    context
    |> Solvers.map (apfst (Symtab.update (name, [])))
    |> Context.map_theory (Attrib.setup (Binding.name (name ^ "_options"))
        (Scan.lift (Parse.$$$ "=" |-- Args.name) >>
          (Thm.declaration_attribute o K o set_solver_options o pair name))
        ("Additional command line options for SMT solver " ^ quote name))

fun select_solver name context =
  if Symtab.defined (fst (Solvers.get context)) name then
    Solvers.map (apsnd (K (SOME name))) context
  else error ("Trying to select unknown solver: " ^ quote name)

val lookup_solver = snd o Solvers.get o Context.Proof

fun solver_of ctxt =
  (case lookup_solver ctxt of
    SOME name => name
  | NONE => error "No SMT solver selected")

fun solver_options_of ctxt =
  (case lookup_solver ctxt of
    NONE => []
  | SOME name =>
      Symtab.lookup_list (fst (Solvers.get (Context.Proof ctxt))) name)

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

val drop_bad_factsN = "smt_drop_bad_facts"
val (drop_bad_facts, setup_drop_bad_facts) =
  Attrib.config_bool drop_bad_factsN (K false)

val filter_only_factsN = "smt_filter_only_facts"
val (filter_only_facts, setup_filter_only_facts) =
  Attrib.config_bool filter_only_factsN (K false)

val setup_options =
  setup_oracle #>
  setup_datatypes #>
  setup_timeout #>
  setup_fixed #>
  setup_trace #>
  setup_verbose #>
  setup_monomorph_limit #>
  setup_drop_bad_facts #>
  setup_filter_only_facts #>
  setup_trace_used_facts


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
  fun merge (s, _) = s
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

    val (names, sel) = Solvers.get (Context.Proof ctxt) |> apfst Symtab.keys
    val ns = if null names then ["(none)"] else sort_strings names
    val n = the_default "(none)" sel
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
