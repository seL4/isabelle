(*  Title:      HOL/Tools/SMT2/smt2_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT2_SOLVER =
sig
  (*configuration*)
  datatype outcome = Unsat | Sat | Unknown

  type parsed_proof =
    {outcome: SMT2_Failure.failure option,
     fact_ids: (int * ((string * ATP_Problem_Generate.stature) * thm)) list,
     atp_proof: unit -> (term, string) ATP_Proof.atp_step list}

  type solver_config =
    {name: string,
     class: Proof.context -> SMT2_Util.class,
     avail: unit -> bool,
     command: unit -> string list,
     options: Proof.context -> string list,
     default_max_relevant: int,
     can_filter: bool,
     outcome: string -> string list -> outcome * string list,
     parse_proof: (Proof.context -> SMT2_Translate.replay_data -> string list ->
       (int * (int * thm)) list * Z3_New_Proof.z3_step list) option,
     replay: (Proof.context -> SMT2_Translate.replay_data -> string list -> thm) option}

  (*registry*)
  val add_solver: solver_config -> theory -> theory
  val default_max_relevant: Proof.context -> string -> int

  (*filter*)
  val smt2_filter: Proof.context -> thm ->
    ((string * ATP_Problem_Generate.stature) * (int option * thm)) list -> int -> Time.time ->
    parsed_proof

  (*tactic*)
  val smt2_tac: Proof.context -> thm list -> int -> tactic
  val smt2_tac': Proof.context -> thm list -> int -> tactic
end

structure SMT2_Solver: SMT2_SOLVER =
struct


(* interface to external solvers *)

local

fun make_command command options problem_path proof_path =
  "(exec 2>&1;" :: map File.shell_quote (command () @ options) @
  [File.shell_path problem_path, ")", ">", File.shell_path proof_path]
  |> space_implode " "

fun with_trace ctxt msg f x =
  let val _ = SMT2_Config.trace_msg ctxt (fn () => msg) ()
  in f x end

fun run ctxt name mk_cmd input =
  (case SMT2_Config.certificates_of ctxt of
    NONE =>
      if not (SMT2_Config.is_available ctxt name) then
        error ("The SMT solver " ^ quote name ^ " is not installed")
      else if Config.get ctxt SMT2_Config.debug_files = "" then
        with_trace ctxt ("Invoking SMT solver " ^ quote name ^ " ...") (Cache_IO.run mk_cmd) input
      else
        let
          val base_path = Path.explode (Config.get ctxt SMT2_Config.debug_files)
          val in_path = Path.ext "smt2_in" base_path
          val out_path = Path.ext "smt2_out" base_path
        in Cache_IO.raw_run mk_cmd input in_path out_path end
  | SOME certs =>
      (case Cache_IO.lookup certs input of
        (NONE, key) =>
          if Config.get ctxt SMT2_Config.read_only_certificates then
            error ("Bad certificate cache: missing certificate")
          else
            Cache_IO.run_and_cache certs key mk_cmd input
      | (SOME output, _) =>
          with_trace ctxt ("Using cached certificate from " ^
            File.shell_path (Cache_IO.cache_path_of certs) ^ " ...") I output))

(* Z3 returns 1 if "get-model" or "get-model" fails *)
val normal_return_codes = [0, 1]

fun run_solver ctxt name mk_cmd input =
  let
    fun pretty tag ls = Pretty.string_of (Pretty.big_list tag (map Pretty.str ls))

    val _ = SMT2_Config.trace_msg ctxt (pretty "Problem:" o split_lines) input

    val {redirected_output = res, output = err, return_code} =
      SMT2_Config.with_timeout ctxt (run ctxt name mk_cmd) input
    val _ = SMT2_Config.trace_msg ctxt (pretty "Solver:") err

    val output = fst (take_suffix (equal "") res)
    val _ = SMT2_Config.trace_msg ctxt (pretty "Result:") output

    val _ = member (op =) normal_return_codes return_code orelse
      raise SMT2_Failure.SMT (SMT2_Failure.Abnormal_Termination return_code)
  in output end

fun trace_assms ctxt =
  SMT2_Config.trace_msg ctxt (Pretty.string_of o
    Pretty.big_list "Assertions:" o map (Display.pretty_thm ctxt o snd))

fun trace_replay_data ({context = ctxt, typs, terms, ...} : SMT2_Translate.replay_data) =
  let
    fun pretty_eq n p = Pretty.block [Pretty.str n, Pretty.str " = ", p]
    fun p_typ (n, T) = pretty_eq n (Syntax.pretty_typ ctxt T)
    fun p_term (n, t) = pretty_eq n (Syntax.pretty_term ctxt t)
  in
    SMT2_Config.trace_msg ctxt (fn () =>
      Pretty.string_of (Pretty.big_list "Names:" [
        Pretty.big_list "sorts:" (map p_typ (Symtab.dest typs)),
        Pretty.big_list "functions:" (map p_term (Symtab.dest terms))])) ()
  end

in

fun invoke name command ithms ctxt =
  let
    val options = SMT2_Config.solver_options_of ctxt
    val comments = [space_implode " " options]

    val (str, replay_data as {context = ctxt', ...}) =
      ithms
      |> tap (trace_assms ctxt)
      |> SMT2_Translate.translate ctxt comments
      ||> tap trace_replay_data
  in (run_solver ctxt' name (make_command command options) str, replay_data) end

end


(* configuration *)

datatype outcome = Unsat | Sat | Unknown

type parsed_proof =
  {outcome: SMT2_Failure.failure option,
   fact_ids: (int * ((string * ATP_Problem_Generate.stature) * thm)) list,
   atp_proof: unit -> (term, string) ATP_Proof.atp_step list}

type solver_config =
  {name: string,
   class: Proof.context -> SMT2_Util.class,
   avail: unit -> bool,
   command: unit -> string list,
   options: Proof.context -> string list,
   default_max_relevant: int,
   can_filter: bool,
   outcome: string -> string list -> outcome * string list,
   parse_proof: (Proof.context -> SMT2_Translate.replay_data -> string list ->
     (int * (int * thm)) list * Z3_New_Proof.z3_step list) option,
   replay: (Proof.context -> SMT2_Translate.replay_data -> string list -> thm) option}


(* check well-sortedness *)

val has_topsort = Term.exists_type (Term.exists_subtype (fn
    TFree (_, []) => true
  | TVar (_, []) => true
  | _ => false))

(* top sorts cause problems with atomization *)
fun check_topsort ctxt thm =
  if has_topsort (Thm.prop_of thm) then (SMT2_Normalize.drop_fact_warning ctxt thm; TrueI) else thm


(* registry *)

type solver_info = {
  command: unit -> string list,
  default_max_relevant: int,
  can_filter: bool,
  parse_proof: Proof.context -> SMT2_Translate.replay_data -> string list ->
    (int * (int * thm)) list * Z3_New_Proof.z3_step list,
  replay: Proof.context -> SMT2_Translate.replay_data -> string list -> thm}

structure Solvers = Generic_Data
(
  type T = solver_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

local
  fun parse_proof outcome parse_proof0 outer_ctxt replay_data output =
    (case outcome output of
      (Unsat, ls) =>
        (case parse_proof0 of SOME pp => pp outer_ctxt replay_data ls | NONE => ([], []))
    | (result, _) => raise SMT2_Failure.SMT (SMT2_Failure.Counterexample (result = Sat)))

  fun replay outcome replay0 oracle outer_ctxt
      (replay_data as {context = ctxt, ...} : SMT2_Translate.replay_data) output =
    (case outcome output of
      (Unsat, ls) =>
        if not (Config.get ctxt SMT2_Config.oracle) andalso is_some replay0
        then the replay0 outer_ctxt replay_data ls
        else oracle ()
    | (result, _) => raise SMT2_Failure.SMT (SMT2_Failure.Counterexample (result = Sat)))

  val cfalse = Thm.cterm_of @{theory} @{prop False}
in

fun add_solver ({name, class, avail, command, options, default_max_relevant, can_filter,
    outcome, parse_proof = parse_proof0, replay = replay0} : solver_config) =
  let
    fun solver oracle = {
      command = command,
      default_max_relevant = default_max_relevant,
      can_filter = can_filter,
      parse_proof = parse_proof (outcome name) parse_proof0,
      replay = replay (outcome name) replay0 oracle}

    val info = {name = name, class = class, avail = avail, options = options}
  in
    Thm.add_oracle (Binding.name name, K cfalse) #-> (fn (_, oracle) =>
    Context.theory_map (Solvers.map (Symtab.update_new (name, solver oracle)))) #>
    Context.theory_map (SMT2_Config.add_solver info)
  end

end

fun get_info ctxt name = the (Symtab.lookup (Solvers.get (Context.Proof ctxt)) name)

fun name_and_info_of ctxt =
  let val name = SMT2_Config.solver_of ctxt
  in (name, get_info ctxt name) end

val default_max_relevant = #default_max_relevant oo get_info
val can_filter = #can_filter o snd o name_and_info_of

fun apply_solver_and_replay ctxt wthms0 =
  let
    val wthms = map (apsnd (check_topsort ctxt)) wthms0
    val (name, {command, replay, ...}) = name_and_info_of ctxt
    val (output, replay_data) = invoke name command (SMT2_Normalize.normalize ctxt wthms) ctxt
  in replay ctxt replay_data output end


(* filter *)

val no_id = ~1

fun smt2_filter ctxt0 goal xwfacts i time_limit =
  let
    val ctxt = ctxt0 |> Config.put SMT2_Config.timeout (Time.toReal time_limit)

    val ({context = ctxt, prems, concl, ...}, _) = Subgoal.focus ctxt i goal
    fun negate ct = Thm.dest_comb ct ||> Thm.apply @{cterm Not} |-> Thm.apply
    val cprop =
      (case try negate (Thm.rhs_of (SMT2_Normalize.atomize_conv ctxt concl)) of
        SOME ct => ct
      | NONE => raise SMT2_Failure.SMT (SMT2_Failure.Other_Failure "goal is not a HOL term"))

    val wconjecture = (NONE, Thm.assume cprop)
    val wprems = map (pair NONE) prems
    val wfacts = map snd xwfacts
    val wthms = wconjecture :: wprems @ wfacts
    val iwthms = map_index I wthms

    val conjecture_i = 0
    val prems_i = 1
    val facts_i = prems_i + length wprems

    val wthms' = map (apsnd (check_topsort ctxt)) wthms
    val (name, {command, parse_proof, ...}) = name_and_info_of ctxt
    val (output, replay_data as {rewrite_rules, ...}) =
      invoke name command (SMT2_Normalize.normalize ctxt wthms') ctxt
  in
    parse_proof ctxt replay_data output
    |> (fn (iidths0, z3_proof) =>
      let
        val iidths = if can_filter ctxt then iidths0 else map (apsnd (apfst (K no_id))) iwthms

        fun id_of_index i = the_default no_id (Option.map fst (AList.lookup (op =) iidths i))

        val conjecture_id = id_of_index conjecture_i
        val prem_ids = map id_of_index (prems_i upto facts_i - 1)
        val helper_ids = map_filter (try (fn (~1, idth) => idth)) iidths
        val fact_ids = map_filter (fn (i, (id, _)) =>
          try (apsnd (apsnd snd o nth xwfacts)) (id, i - facts_i)) iidths
        val fact_helper_ts =
          map (fn (_, th) => (ATP_Util.short_thm_name ctxt th, prop_of th)) helper_ids @
          map (fn (_, ((s, _), th)) => (s, prop_of th)) fact_ids
        val fact_helper_ids =
          map (apsnd (ATP_Util.short_thm_name ctxt)) helper_ids @ map (apsnd (fst o fst)) fact_ids
      in
        {outcome = NONE, fact_ids = fact_ids,
         atp_proof = fn () => Z3_New_Isar.atp_proof_of_z3_proof ctxt rewrite_rules
           (map Thm.prop_of prems) (Thm.term_of concl) fact_helper_ts prem_ids conjecture_id
           fact_helper_ids z3_proof}
      end)
  end
  handle SMT2_Failure.SMT fail => {outcome = SOME fail, fact_ids = [], atp_proof = K []}


(* SMT tactic *)

local
  fun str_of ctxt fail =
    "Solver " ^ SMT2_Config.solver_of ctxt ^ ": " ^ SMT2_Failure.string_of_failure fail

  fun safe_solve ctxt wfacts = SOME (apply_solver_and_replay ctxt wfacts)
    handle
      SMT2_Failure.SMT (fail as SMT2_Failure.Counterexample _) =>
        (SMT2_Config.verbose_msg ctxt (str_of ctxt) fail; NONE)
    | SMT2_Failure.SMT (fail as SMT2_Failure.Time_Out) =>
        error ("SMT: Solver " ^ quote (SMT2_Config.solver_of ctxt) ^ ": " ^
          SMT2_Failure.string_of_failure fail ^ " (setting the " ^
          "configuration option " ^ quote (Config.name_of SMT2_Config.timeout) ^ " might help)")
    | SMT2_Failure.SMT fail => error (str_of ctxt fail)

  fun resolve (SOME thm) = rtac thm 1
    | resolve NONE = no_tac

  fun tac prove ctxt rules =
    CONVERSION (SMT2_Normalize.atomize_conv ctxt)
    THEN' rtac @{thm ccontr}
    THEN' SUBPROOF (fn {context = ctxt, prems, ...} =>
      resolve (prove ctxt (map (pair NONE) (rules @ prems)))) ctxt
in

val smt2_tac = tac safe_solve
val smt2_tac' = tac (SOME oo apply_solver_and_replay)

end

end
