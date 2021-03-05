(*  Title:      HOL/Tools/SMT/smt_config.ML
    Author:     Sascha Boehme, TU Muenchen

Configuration options and diagnostic tools for SMT.
*)

signature SMT_CONFIG =
sig
  (*solver*)
  type solver_info = {
    name: string,
    class: Proof.context -> SMT_Util.class,
    avail: unit -> bool,
    options: Proof.context -> string list }
  val add_solver: solver_info -> Context.generic -> Context.generic
  val set_solver_options: string * string -> Context.generic -> Context.generic
  val is_available: Proof.context -> string -> bool
  val available_solvers_of: Proof.context -> string list
  val select_solver: string -> Context.generic -> Context.generic
  val solver_of: Proof.context -> string
  val solver_class_of: Proof.context -> SMT_Util.class
  val solver_options_of: Proof.context -> string list

  (*options*)
  val oracle: bool Config.T
  val timeout: real Config.T
  val reconstruction_step_timeout: real Config.T
  val random_seed: int Config.T
  val read_only_certificates: bool Config.T
  val verbose: bool Config.T
  val trace: bool Config.T
  val statistics: bool Config.T
  val monomorph_limit: int Config.T
  val monomorph_instances: int Config.T
  val explicit_application: int Config.T
  val higher_order: bool Config.T
  val nat_as_int: bool Config.T
  val infer_triggers: bool Config.T
  val debug_files: string Config.T
  val sat_solver: string Config.T
  val compress_verit_proofs: Proof.context -> bool

  (*tools*)
  val get_timeout: Proof.context -> Time.time option
  val with_time_limit: Proof.context -> real Config.T -> ('a -> 'b) -> 'a -> 'b
  val with_timeout: Proof.context -> ('a -> 'b) -> 'a -> 'b

  (*diagnostics*)
  val trace_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val verbose_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val statistics_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val verit_msg: Proof.context -> (unit -> 'a) -> unit
  val verit_arith_msg: Proof.context -> (unit -> 'a) -> unit
  val spy_verit: Proof.context -> bool
  val spy_Z3: Proof.context -> bool

  (*certificates*)
  val select_certificates: string -> Context.generic -> Context.generic
  val certificates_of: Proof.context -> Cache_IO.cache option

  (*setup*)
  val print_setup: Proof.context -> unit
end;

structure SMT_Config: SMT_CONFIG =
struct

(* solver *)

type solver_info = {
  name: string,
  class: Proof.context -> SMT_Util.class,
  avail: unit -> bool,
  options: Proof.context -> string list}

type data = {
  solvers: (solver_info * string list) Symtab.table,
  solver: string option,
  certs: Cache_IO.cache option}

fun mk_data solvers solver certs: data = {solvers=solvers, solver=solver, certs=certs}

val empty_data = mk_data Symtab.empty NONE NONE

fun solvers_of ({solvers, ...}: data) = solvers
fun solver_of ({solver, ...}: data) = solver
fun certs_of ({certs, ...}: data) = certs

fun map_solvers f ({solvers, solver, certs}: data) = mk_data (f solvers) solver certs
fun map_solver f ({solvers, solver, certs}: data) = mk_data solvers (f solver) certs
fun put_certs c ({solvers, solver, ...}: data) = mk_data solvers solver c

fun merge_data ({solvers=ss1,solver=s1,certs=c1}: data, {solvers=ss2,solver=s2,certs=c2}: data) =
  mk_data (Symtab.merge (K true) (ss1, ss2)) (merge_options (s1, s2)) (merge_options (c1, c2))

structure Data = Generic_Data
(
  type T = data
  val empty = empty_data
  val extend = I
  val merge = merge_data
)

fun set_solver_options (name, options) =
  let val opts = String.tokens (Symbol.is_ascii_blank o str) options
  in Data.map (map_solvers (Symtab.map_entry name (apsnd (K opts)))) end

fun add_solver (info as {name, ...} : solver_info) context =
  if Symtab.defined (solvers_of (Data.get context)) name then
    error ("Solver already registered: " ^ quote name)
  else
    context
    |> Data.map (map_solvers (Symtab.update (name, (info, []))))
    |> Context.map_theory (Attrib.setup (Binding.name (name ^ "_options"))
        (Scan.lift (\<^keyword>\<open>=\<close> |-- Args.name) >>
          (Thm.declaration_attribute o K o set_solver_options o pair name))
        ("additional command line options for SMT solver " ^ quote name))

fun all_solvers_of ctxt = Symtab.keys (solvers_of (Data.get (Context.Proof ctxt)))

fun solver_name_of ctxt = solver_of (Data.get (Context.Proof ctxt))

fun is_available ctxt name =
  (case Symtab.lookup (solvers_of (Data.get (Context.Proof ctxt))) name of
    SOME ({avail, ...}, _) => avail ()
  | NONE => false)

fun available_solvers_of ctxt =
  filter (is_available ctxt) (all_solvers_of ctxt)

fun warn_solver (Context.Proof ctxt) name =
      if Context_Position.is_visible ctxt then
        warning ("The SMT solver " ^ quote name ^ " is not installed")
      else ()
  | warn_solver _ _ = ()

fun select_solver name context =
  let
    val ctxt = Context.proof_of context
    val upd = Data.map (map_solver (K (SOME name)))
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
  (case solver_name_of ctxt of
    NONE => default ()
  | SOME name => select (Symtab.lookup (solvers_of (Data.get (Context.Proof ctxt))) name))

fun solver_class_of ctxt =
  let fun class_of ({class, ...}: solver_info, _) = class ctxt
  in solver_info_of no_solver_err (class_of o the) ctxt end

fun solver_options_of ctxt =
  let
    fun all_options NONE = []
      | all_options (SOME ({options, ...} : solver_info, opts)) =
          opts @ options ctxt
  in solver_info_of (K []) all_options ctxt end

val setup_solver =
  Attrib.setup \<^binding>\<open>smt_solver\<close>
    (Scan.lift (\<^keyword>\<open>=\<close> |-- Args.name) >>
      (Thm.declaration_attribute o K o select_solver))
    "SMT solver configuration"


(* options *)

val oracle = Attrib.setup_config_bool \<^binding>\<open>smt_oracle\<close> (K true)
val timeout = Attrib.setup_config_real \<^binding>\<open>smt_timeout\<close> (K 0.0)
val reconstruction_step_timeout = Attrib.setup_config_real \<^binding>\<open>smt_reconstruction_step_timeout\<close> (K 10.0)
val random_seed = Attrib.setup_config_int \<^binding>\<open>smt_random_seed\<close> (K 1)
val read_only_certificates = Attrib.setup_config_bool \<^binding>\<open>smt_read_only_certificates\<close> (K false)
val verbose = Attrib.setup_config_bool \<^binding>\<open>smt_verbose\<close> (K true)
val trace = Attrib.setup_config_bool \<^binding>\<open>smt_trace\<close> (K false)
val trace_verit = Attrib.setup_config_bool \<^binding>\<open>smt_debug_verit\<close> (K false)
val spy_verit_attr = Attrib.setup_config_bool \<^binding>\<open>smt_spy_verit\<close> (K false)
val spy_z3 = Attrib.setup_config_bool \<^binding>\<open>smt_spy_z3\<close> (K false)
val trace_arith_verit = Attrib.setup_config_bool \<^binding>\<open>smt_debug_arith_verit\<close> (K false)
val trace_verit_compression = Attrib.setup_config_bool \<^binding>\<open>verit_compress_proofs\<close> (K true)
val statistics = Attrib.setup_config_bool \<^binding>\<open>smt_statistics\<close> (K false)
val monomorph_limit = Attrib.setup_config_int \<^binding>\<open>smt_monomorph_limit\<close> (K 10)
val monomorph_instances = Attrib.setup_config_int \<^binding>\<open>smt_monomorph_instances\<close> (K 500)
val explicit_application = Attrib.setup_config_int \<^binding>\<open>smt_explicit_application\<close> (K 1)
val higher_order = Attrib.setup_config_bool \<^binding>\<open>smt_higher_order\<close> (K false)
val nat_as_int = Attrib.setup_config_bool \<^binding>\<open>smt_nat_as_int\<close> (K false)
val infer_triggers = Attrib.setup_config_bool \<^binding>\<open>smt_infer_triggers\<close> (K false)
val debug_files = Attrib.setup_config_string \<^binding>\<open>smt_debug_files\<close> (K "")
val sat_solver = Attrib.setup_config_string \<^binding>\<open>smt_sat_solver\<close> (K "cdclite")


(* diagnostics *)

fun cond_trace flag f x = if flag then tracing ("SMT: " ^ f x) else ()

fun verbose_msg ctxt = cond_trace (Config.get ctxt verbose)
fun trace_msg ctxt = cond_trace (Config.get ctxt trace)
fun statistics_msg ctxt = cond_trace (Config.get ctxt statistics)

fun verit_msg ctxt (x : unit -> 'a) = if (Config.get ctxt trace_verit) then ignore(x ()) else ()
fun verit_arith_msg ctxt (x : unit -> 'a) = if (Config.get ctxt trace_arith_verit) then ignore(x ()) else ()

fun spy_verit ctxt  = Config.get ctxt spy_verit_attr
fun spy_Z3 ctxt  = Config.get ctxt spy_z3
fun compress_verit_proofs ctxt  = Config.get ctxt trace_verit_compression


(* tools *)

fun get_timeout ctxt =
  let val t = seconds (Config.get ctxt timeout);
  in if Timeout.ignored t then NONE else SOME (Timeout.scale_time t) end;

fun with_time_limit ctxt timeout_config f x =
  Timeout.apply (seconds (Config.get ctxt timeout_config)) f x
    handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out

fun with_timeout ctxt = with_time_limit ctxt timeout


(* certificates *)

val certificates_of = certs_of o Data.get o Context.Proof

val get_certificates_path = Option.map (Cache_IO.cache_path_of) o certificates_of

fun select_certificates name context = context |> Data.map (put_certs (
  if name = "" then NONE
  else
    (Resources.master_directory (Context.theory_of context) + Path.explode name)
    |> SOME o Cache_IO.unsynchronized_init))

val setup_certificates =
  Attrib.setup \<^binding>\<open>smt_certificates\<close>
    (Scan.lift (\<^keyword>\<open>=\<close> |-- Args.name) >>
      (Thm.declaration_attribute o K o select_certificates))
    "SMT certificates configuration"


(* setup *)

val _ = Theory.setup (
  setup_solver #>
  setup_certificates)

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
        string_of_bool (Config.get ctxt read_only_certificates))])
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>smt_status\<close>
    "show the available SMT solvers, the currently selected SMT solver, \
    \and the values of SMT configuration options"
    (Scan.succeed (Toplevel.keep (print_setup o Toplevel.context_of)))

end;
