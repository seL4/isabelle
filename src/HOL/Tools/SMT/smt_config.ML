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
  val is_available: Proof.context -> string -> bool
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
  val trace: bool Config.T
  val trace_used_facts: bool Config.T
  val monomorph_limit: int Config.T
  val monomorph_instances: int Config.T
  val monomorph_full: bool Config.T
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

(* FIXME just one data slot (record) per program unit *)
structure Solvers = Generic_Data
(
  type T = (solver_info * string list) Symtab.table * string option
  val empty = (Symtab.empty, NONE)
  val extend = I
  fun merge ((ss1, s1), (ss2, s2)) =
    (Symtab.merge (K true) (ss1, ss2), merge_options (s1, s2))
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
        (Scan.lift (@{keyword "="} |-- Args.name) >>
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

fun warn_solver context name =
  Context_Position.if_visible_proof context
    warning ("The SMT solver " ^ quote name ^ " is not installed.")

fun select_solver name context =
  let
    val ctxt = Context.proof_of context
    val upd = Solvers.map (apsnd (K (SOME name)))
  in
    if not (member (op =) (all_solvers_of ctxt) name) then
      error ("Trying to select unknown solver: " ^ quote name)
    else if not (is_available ctxt name) then
      (warn_solver context name; upd context)
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
    (Scan.lift (@{keyword "="} |-- Args.name) >>
      (Thm.declaration_attribute o K o select_solver))
    "SMT solver configuration"


(* options *)

val oracle = Attrib.setup_config_bool @{binding smt_oracle} (K true)
val datatypes = Attrib.setup_config_bool @{binding smt_datatypes} (K false)
val timeout = Attrib.setup_config_real @{binding smt_timeout} (K 30.0)
val random_seed = Attrib.setup_config_int @{binding smt_random_seed} (K 1)
val fixed = Attrib.setup_config_bool @{binding smt_fixed} (K false)
val verbose = Attrib.setup_config_bool @{binding smt_verbose} (K true)
val trace = Attrib.setup_config_bool @{binding smt_trace} (K false)
val trace_used_facts = Attrib.setup_config_bool @{binding smt_trace_used_facts} (K false)
val monomorph_limit = Attrib.setup_config_int @{binding smt_monomorph_limit} (K 10)
val monomorph_instances = Attrib.setup_config_int @{binding smt_monomorph_instances} (K 500)
val monomorph_full = Attrib.setup_config_bool @{binding smt_monomorph_full} (K true)
val infer_triggers = Attrib.setup_config_bool @{binding smt_infer_triggers} (K false)
val drop_bad_facts = Attrib.setup_config_bool @{binding smt_drop_bad_facts} (K false)
val filter_only_facts = Attrib.setup_config_bool @{binding smt_filter_only_facts} (K false)
val debug_files = Attrib.setup_config_string @{binding smt_debug_files} (K "")


(* diagnostics *)

fun cond_trace flag f x = if flag then tracing ("SMT: " ^ f x) else ()

fun verbose_msg ctxt = cond_trace (Config.get ctxt verbose)

fun trace_msg ctxt = cond_trace (Config.get ctxt trace)


(* tools *)

fun with_timeout ctxt f x =
  TimeLimit.timeLimit (seconds (Config.get ctxt timeout)) f x
  handle TimeLimit.TimeOut => raise SMT_Failure.SMT SMT_Failure.Time_Out


(* certificates *)

(* FIXME just one data slot (record) per program unit *)
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
    (Scan.lift (@{keyword "="} |-- Args.name) >>
      (Thm.declaration_attribute o K o select_certificates))
    "SMT certificates configuration"


(* setup *)

val setup =
  setup_solver #>
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
        SOME path => Path.print path
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
