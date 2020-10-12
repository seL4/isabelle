(*  Title:      HOL/Tools/SMT/smt_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT_SOLVER =
sig
  (*configuration*)
  datatype outcome = Unsat | Sat | Unknown | Time_Out

  type parsed_proof =
    {outcome: SMT_Failure.failure option,
     fact_ids: (int * ((string * ATP_Problem_Generate.stature) * thm)) list option,
     atp_proof: unit -> (term, string) ATP_Proof.atp_step list}

  type solver_config =
    {name: string,
     class: Proof.context -> SMT_Util.class,
     avail: unit -> bool,
     command: unit -> string list,
     options: Proof.context -> string list,
     smt_options: (string * string) list,
     default_max_relevant: int,
     outcome: string -> string list -> outcome * string list,
     parse_proof: (Proof.context -> SMT_Translate.replay_data ->
       ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
       parsed_proof) option,
     replay: (Proof.context -> SMT_Translate.replay_data -> string list -> thm) option}

  (*registry*)
  val add_solver: solver_config -> theory -> theory
  val default_max_relevant: Proof.context -> string -> int

  (*filter*)
  val smt_filter: Proof.context -> thm -> ((string * ATP_Problem_Generate.stature) * thm) list ->
    int -> Time.time -> parsed_proof

  (*tactic*)
  val smt_tac: Proof.context -> thm list -> int -> tactic
  val smt_tac': Proof.context -> thm list -> int -> tactic
end;

structure SMT_Solver: SMT_SOLVER =
struct

(* interface to external solvers *)

local

fun make_command command options problem_path proof_path =
  Bash.strings (command () @ options) ^ " " ^
    File.bash_platform_path problem_path ^
    " > " ^ File.bash_path proof_path ^ " 2>&1"

fun with_trace ctxt msg f x =
  let val _ = SMT_Config.trace_msg ctxt (fn () => msg) ()
  in f x end

fun run ctxt name mk_cmd input =
  (case SMT_Config.certificates_of ctxt of
    NONE =>
      if not (SMT_Config.is_available ctxt name) then
        error ("The SMT solver " ^ quote name ^ " is not installed")
      else if Config.get ctxt SMT_Config.debug_files = "" then
        with_trace ctxt ("Invoking SMT solver " ^ quote name ^ " ...") (Cache_IO.run mk_cmd) input
      else
        let
          val base_path = Path.explode (Config.get ctxt SMT_Config.debug_files)
          val in_path = Path.ext "smt_in" base_path
          val out_path = Path.ext "smt_out" base_path
        in Cache_IO.raw_run mk_cmd input in_path out_path end
  | SOME certs =>
      (case Cache_IO.lookup certs input of
        (NONE, key) =>
          if Config.get ctxt SMT_Config.read_only_certificates then
            error ("Bad certificate cache: missing certificate")
          else
            Cache_IO.run_and_cache certs key mk_cmd input
      | (SOME output, _) =>
          with_trace ctxt ("Using cached certificate from " ^
            Path.print (Cache_IO.cache_path_of certs) ^ " ...") I output))

(* Z3 returns 1 if "get-proof" or "get-model" fails. veriT returns 255. *)
val normal_return_codes = [0, 1, 255]

fun run_solver ctxt name mk_cmd input =
  let
    fun pretty tag lines = Pretty.string_of (Pretty.big_list tag (map Pretty.str lines))

    val _ = SMT_Config.trace_msg ctxt (pretty "Problem:" o split_lines) input

    val ({elapsed, ...}, {redirected_output = res, output = err, return_code}) =
      Timing.timing (SMT_Config.with_timeout ctxt (run ctxt name mk_cmd)) input
    val _ = SMT_Config.trace_msg ctxt (pretty "Solver:") err

    val output = drop_suffix (equal "") res
    val _ = SMT_Config.trace_msg ctxt (pretty "Result:") output
    val _ = SMT_Config.trace_msg ctxt (pretty "Time (ms):") [\<^make_string> (Time.toMilliseconds elapsed)]
    val _ = SMT_Config.statistics_msg ctxt (pretty "Time (ms):") [\<^make_string> (Time.toMilliseconds elapsed)]

    val _ = member (op =) normal_return_codes return_code orelse
      raise SMT_Failure.SMT (SMT_Failure.Abnormal_Termination return_code)
  in output end

fun trace_assms ctxt =
  SMT_Config.trace_msg ctxt (Pretty.string_of o
    Pretty.big_list "Assertions:" o map (Thm.pretty_thm ctxt o snd))

fun trace_replay_data ({context = ctxt, typs, terms, ...} : SMT_Translate.replay_data) =
  let
    fun pretty_eq n p = Pretty.block [Pretty.str n, Pretty.str " = ", p]
    fun p_typ (n, T) = pretty_eq n (Syntax.pretty_typ ctxt T)
    fun p_term (n, t) = pretty_eq n (Syntax.pretty_term ctxt t)
  in
    SMT_Config.trace_msg ctxt (fn () =>
      Pretty.string_of (Pretty.big_list "Names:" [
        Pretty.big_list "sorts:" (map p_typ (Symtab.dest typs)),
        Pretty.big_list "functions:" (map p_term (Symtab.dest terms))])) ()
  end

in

fun invoke name command smt_options ithms ctxt =
  let
    val options = SMT_Config.solver_options_of ctxt
    val comments = [space_implode " " options]

    val (str, replay_data as {context = ctxt', ...}) =
      ithms
      |> tap (trace_assms ctxt)
      |> SMT_Translate.translate ctxt smt_options comments
      ||> tap trace_replay_data
  in (run_solver ctxt' name (make_command command options) str, replay_data) end

end


(* configuration *)

datatype outcome = Unsat | Sat | Unknown | Time_Out

type parsed_proof =
  {outcome: SMT_Failure.failure option,
   fact_ids: (int * ((string * ATP_Problem_Generate.stature) * thm)) list option,
   atp_proof: unit -> (term, string) ATP_Proof.atp_step list}

type solver_config =
  {name: string,
   class: Proof.context -> SMT_Util.class,
   avail: unit -> bool,
   command: unit -> string list,
   options: Proof.context -> string list,
   smt_options: (string * string) list,
   default_max_relevant: int,
   outcome: string -> string list -> outcome * string list,
   parse_proof: (Proof.context -> SMT_Translate.replay_data ->
     ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
     parsed_proof) option,
   replay: (Proof.context -> SMT_Translate.replay_data -> string list -> thm) option}


(* check well-sortedness *)

val has_topsort = Term.exists_type (Term.exists_subtype (fn
    TFree (_, []) => true
  | TVar (_, []) => true
  | _ => false))

(* top sorts cause problems with atomization *)
fun check_topsort ctxt thm =
  if has_topsort (Thm.prop_of thm) then (SMT_Normalize.drop_fact_warning ctxt thm; TrueI) else thm


(* registry *)

type solver_info = {
  command: unit -> string list,
  smt_options: (string * string) list,
  default_max_relevant: int,
  parse_proof: Proof.context -> SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    parsed_proof,
  replay: Proof.context -> SMT_Translate.replay_data -> string list -> thm}

structure Solvers = Generic_Data
(
  type T = solver_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

local
  fun parse_proof outcome parse_proof0 outer_ctxt replay_data xfacts prems concl output =
    (case outcome output of
      (Unsat, lines) =>
        (case parse_proof0 of
          SOME pp => pp outer_ctxt replay_data xfacts prems concl lines
        | NONE => {outcome = NONE, fact_ids = NONE, atp_proof = K []})
    | (Time_Out, _) => raise SMT_Failure.SMT (SMT_Failure.Time_Out)
    | (result, _) => raise SMT_Failure.SMT (SMT_Failure.Counterexample (result = Sat)))

  fun replay outcome replay0 oracle outer_ctxt
      (replay_data as {context = ctxt, ...} : SMT_Translate.replay_data) output =
    (case outcome output of
      (Unsat, lines) =>
        if Config.get ctxt SMT_Config.oracle then
          oracle ()
        else
          (case replay0 of
            SOME replay => replay outer_ctxt replay_data lines
          | NONE => error "No proof reconstruction for solver -- \
            \declare [[smt_oracle]] to allow oracle")
    | (Time_Out, _) => raise SMT_Failure.SMT (SMT_Failure.Time_Out)
    | (result, _) => raise SMT_Failure.SMT (SMT_Failure.Counterexample (result = Sat)))

  val cfalse = Thm.cterm_of \<^context> \<^prop>\<open>False\<close>
in

fun add_solver ({name, class, avail, command, options, smt_options, default_max_relevant, outcome,
    parse_proof = parse_proof0, replay = replay0} : solver_config) =
  let
    fun solver oracle = {
      command = command,
      smt_options = smt_options,
      default_max_relevant = default_max_relevant,
      parse_proof = parse_proof (outcome name) parse_proof0,
      replay = replay (outcome name) replay0 oracle}

    val info = {name = name, class = class, avail = avail, options = options}
  in
    Thm.add_oracle (Binding.name name, K cfalse) #-> (fn (_, oracle) =>
    Context.theory_map (Solvers.map (Symtab.update_new (name, solver oracle)))) #>
    Context.theory_map (SMT_Config.add_solver info)
  end

end

fun get_info ctxt name = the (Symtab.lookup (Solvers.get (Context.Proof ctxt)) name)

fun name_and_info_of ctxt =
  let val name = SMT_Config.solver_of ctxt
  in (name, get_info ctxt name) end

val default_max_relevant = #default_max_relevant oo get_info

fun apply_solver_and_replay ctxt thms0 =
  let
    val thms = map (check_topsort ctxt) thms0
    val (name, {command, smt_options, replay, ...}) = name_and_info_of ctxt
    val (output, replay_data) =
      invoke name command smt_options (SMT_Normalize.normalize ctxt thms) ctxt
  in replay ctxt replay_data output end


(* filter (for Sledgehammer) *)

fun smt_filter ctxt0 goal xfacts i time_limit =
  let
    val ctxt = ctxt0 |> Config.put SMT_Config.timeout (Time.toReal time_limit)

    val ({context = ctxt, prems, concl, ...}, _) = Subgoal.focus ctxt i NONE goal
    fun negate ct = Thm.dest_comb ct ||> Thm.apply \<^cterm>\<open>Not\<close> |-> Thm.apply
    val cprop =
      (case try negate (Thm.rhs_of (SMT_Normalize.atomize_conv ctxt concl)) of
        SOME ct => ct
      | NONE => raise SMT_Failure.SMT (SMT_Failure.Other_Failure "cannot atomize goal"))

    val conjecture = Thm.assume cprop
    val facts = map snd xfacts
    val thms = conjecture :: prems @ facts
    val thms' = map (check_topsort ctxt) thms

    val (name, {command, smt_options, parse_proof, ...}) = name_and_info_of ctxt
    val (output, replay_data) =
      invoke name command smt_options (SMT_Normalize.normalize ctxt thms') ctxt
  in
    parse_proof ctxt replay_data xfacts (map Thm.prop_of prems) (Thm.term_of concl) output
  end
  handle SMT_Failure.SMT fail => {outcome = SOME fail, fact_ids = NONE, atp_proof = K []}


(* SMT tactic *)

local
  fun str_of ctxt fail =
    "Solver " ^ SMT_Config.solver_of ctxt ^ ": " ^ SMT_Failure.string_of_failure fail

  fun safe_solve ctxt facts = SOME (apply_solver_and_replay ctxt facts)
    handle
      SMT_Failure.SMT (fail as SMT_Failure.Counterexample _) =>
        (SMT_Config.verbose_msg ctxt (str_of ctxt) fail; NONE)
    | SMT_Failure.SMT (fail as SMT_Failure.Time_Out) =>
        (SMT_Config.verbose_msg ctxt (K ("SMT: Solver " ^ quote (SMT_Config.solver_of ctxt) ^ ": " ^
          SMT_Failure.string_of_failure fail ^ " (setting the " ^
          "configuration option " ^ quote (Config.name_of SMT_Config.timeout) ^ " might help)")) ();
         NONE)
    | SMT_Failure.SMT fail => error (str_of ctxt fail)

  fun resolve ctxt (SOME thm) = resolve_tac ctxt [thm] 1
    | resolve _ NONE = no_tac

  fun tac prove ctxt rules =
    CONVERSION (SMT_Normalize.atomize_conv ctxt)
    THEN' resolve_tac ctxt @{thms ccontr}
    THEN' SUBPROOF (fn {context = ctxt', prems, ...} =>
      resolve ctxt' (prove ctxt' (rules @ prems))) ctxt
in

val smt_tac = tac safe_solve
val smt_tac' = tac (SOME oo apply_solver_and_replay)

end

end;
