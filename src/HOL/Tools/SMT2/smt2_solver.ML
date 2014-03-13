(*  Title:      HOL/Tools/SMT2/smt2_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT2_SOLVER =
sig
  (*configuration*)
  datatype outcome = Unsat | Sat | Unknown
  type solver_config = {
    name: string,
    class: Proof.context -> SMT2_Utils.class,
    avail: unit -> bool,
    command: unit -> string list,
    options: Proof.context -> string list,
    default_max_relevant: int,
    supports_filter: bool,
    outcome: string -> string list -> outcome * string list,
    cex_parser: (Proof.context -> SMT2_Translate.replay_data -> string list ->
      term list * term list) option,
    replay: (Proof.context -> SMT2_Translate.replay_data -> string list ->
      (int list * Z3_New_Proof.z3_step list) * thm) option }

  (*registry*)
  val add_solver: solver_config -> theory -> theory
  val solver_name_of: Proof.context -> string
  val available_solvers_of: Proof.context -> string list
  val apply_solver: Proof.context -> (int * (int option * thm)) list ->
    (int list * Z3_New_Proof.z3_step list) * thm
  val default_max_relevant: Proof.context -> string -> int

  (*filter*)
  val smt2_filter: Proof.context -> thm list -> thm -> ('a * (int option * thm)) list -> int ->
    Time.time -> {outcome: SMT2_Failure.failure option, used_facts: ('a * thm) list,
      z3_steps: Z3_New_Proof.z3_step list}

  (*tactic*)
  val smt2_tac: Proof.context -> thm list -> int -> tactic
  val smt2_tac': Proof.context -> thm list -> int -> tactic
end

structure SMT2_Solver: SMT2_SOLVER =
struct


(* interface to external solvers *)

local

fun make_cmd command options problem_path proof_path = space_implode " " (
  "(exec 2>&1;" :: map File.shell_quote (command @ options) @
  [File.shell_path problem_path, ")", ">", File.shell_path proof_path])

fun trace_and ctxt msg f x =
  let val _ = SMT2_Config.trace_msg ctxt (fn () => msg) ()
  in f x end

fun run ctxt name mk_cmd input =
  (case SMT2_Config.certificates_of ctxt of
    NONE =>
      if not (SMT2_Config.is_available ctxt name) then
        error ("The SMT solver " ^ quote name ^ " is not installed.")
      else if Config.get ctxt SMT2_Config.debug_files = "" then
        trace_and ctxt ("Invoking SMT solver " ^ quote name ^ " ...")
          (Cache_IO.run mk_cmd) input
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
          trace_and ctxt ("Using cached certificate from " ^
            File.shell_path (Cache_IO.cache_path_of certs) ^ " ...")
            I output))

fun run_solver ctxt name mk_cmd input =
  let
    fun pretty tag ls = Pretty.string_of (Pretty.big_list tag
      (map Pretty.str ls))

    val _ = SMT2_Config.trace_msg ctxt (pretty "Problem:" o split_lines) input

    val {redirected_output=res, output=err, return_code} =
      SMT2_Config.with_timeout ctxt (run ctxt name mk_cmd) input
    val _ = SMT2_Config.trace_msg ctxt (pretty "Solver:") err

    val output = fst (take_suffix (equal "") res)
    val _ = SMT2_Config.trace_msg ctxt (pretty "Result:") output

    val _ = return_code <> 0 andalso
      raise SMT2_Failure.SMT (SMT2_Failure.Abnormal_Termination return_code)
  in output end

fun trace_assms ctxt =
  SMT2_Config.trace_msg ctxt (Pretty.string_of o
    Pretty.big_list "Assertions:" o map (Display.pretty_thm ctxt o snd))

fun trace_replay_data ({context=ctxt, typs, terms, ...} : SMT2_Translate.replay_data) =
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
    val cmd = command ()
    val comments = [space_implode " " (cmd @ options)]

    val (str, replay_data as {context=ctxt', ...}) =
      ithms
      |> tap (trace_assms ctxt)
      |> SMT2_Translate.translate ctxt comments
      ||> tap trace_replay_data
  in (run_solver ctxt' name (make_cmd cmd options) str, replay_data) end

end


(* configuration *)

datatype outcome = Unsat | Sat | Unknown

type solver_config = {
  name: string,
  class: Proof.context -> SMT2_Utils.class,
  avail: unit -> bool,
  command: unit -> string list,
  options: Proof.context -> string list,
  default_max_relevant: int,
  supports_filter: bool,
  outcome: string -> string list -> outcome * string list,
  cex_parser: (Proof.context -> SMT2_Translate.replay_data -> string list ->
    term list * term list) option,
  replay: (Proof.context -> SMT2_Translate.replay_data -> string list ->
    (int list * Z3_New_Proof.z3_step list) * thm) option }


(* registry *)

type solver_info = {
  command: unit -> string list,
  default_max_relevant: int,
  supports_filter: bool,
  replay: Proof.context -> string list * SMT2_Translate.replay_data ->
    (int list * Z3_New_Proof.z3_step list) * thm }

structure Solvers = Generic_Data
(
  type T = solver_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

local
  fun finish outcome cex_parser replay ocl outer_ctxt
      (output, (replay_data as {context=ctxt, ...} : SMT2_Translate.replay_data)) =
    (case outcome output of
      (Unsat, ls) =>
        if not (Config.get ctxt SMT2_Config.oracle) andalso is_some replay
        then the replay outer_ctxt replay_data ls
        else (([], []), ocl ())
    | (result, ls) =>
        let
          val (ts, us) =
            (case cex_parser of SOME f => f ctxt replay_data ls | _ => ([], []))
        in
          raise SMT2_Failure.SMT (SMT2_Failure.Counterexample {
            is_real_cex = (result = Sat),
            free_constraints = ts,
            const_defs = us})
        end)

  val cfalse = Thm.cterm_of @{theory} (@{const Trueprop} $ @{const False})
in

fun add_solver cfg =
  let
    val {name, class, avail, command, options, default_max_relevant,
      supports_filter, outcome, cex_parser, replay} = cfg

    fun core_oracle () = cfalse

    fun solver ocl = {
      command = command,
      default_max_relevant = default_max_relevant,
      supports_filter = supports_filter,
      replay = finish (outcome name) cex_parser replay ocl }

    val info = {name=name, class=class, avail=avail, options=options}
  in
    Thm.add_oracle (Binding.name name, core_oracle) #-> (fn (_, ocl) =>
    Context.theory_map (Solvers.map (Symtab.update_new (name, solver ocl)))) #>
    Context.theory_map (SMT2_Config.add_solver info)
  end

end

fun get_info ctxt name =
  the (Symtab.lookup (Solvers.get (Context.Proof ctxt)) name)

val solver_name_of = SMT2_Config.solver_of

val available_solvers_of = SMT2_Config.available_solvers_of

fun name_and_info_of ctxt =
  let val name = solver_name_of ctxt
  in (name, get_info ctxt name) end

fun apply_solver ctxt0 iwthms =
  let
    val (ithms, ctxt) = SMT2_Normalize.normalize iwthms ctxt0
    val (name, {command, replay, ...}) = name_and_info_of ctxt
  in
    invoke name command ithms ctxt
    |> replay ctxt
  end

val default_max_relevant = #default_max_relevant oo get_info

val supports_filter = #supports_filter o snd o name_and_info_of 


(* check well-sortedness *)

val has_topsort = Term.exists_type (Term.exists_subtype (fn
    TFree (_, []) => true
  | TVar (_, []) => true
  | _ => false))

(* without this test, we would run into problems when atomizing the rules: *)
fun check_topsort ctxt thm =
  if has_topsort (Thm.prop_of thm) then
    (SMT2_Normalize.drop_fact_warning ctxt thm; TrueI)
  else
    thm

fun check_topsorts ctxt iwthms = map (apsnd (apsnd (check_topsort ctxt))) iwthms


(* filter *)

val cnot = Thm.cterm_of @{theory} @{const Not}

fun smt2_filter ctxt facts goal xwthms i time_limit =
  let
    val ctxt =
      ctxt
      |> Config.put SMT2_Config.oracle false
      |> Config.put SMT2_Config.filter_only_facts true
      |> Config.put SMT2_Config.timeout (Time.toReal time_limit)

    val ({context=ctxt, prems, concl, ...}, _) = Subgoal.focus ctxt i goal
    fun negate ct = Thm.dest_comb ct ||> Thm.apply cnot |-> Thm.apply
    val cprop =
      (case try negate (Thm.rhs_of (SMT2_Normalize.atomize_conv ctxt concl)) of
        SOME ct => ct
      | NONE => raise SMT2_Failure.SMT (SMT2_Failure.Other_Failure (
          "goal is not a HOL term")))

    val xthms = map (apsnd snd) xwthms

    val filter_thms = if supports_filter ctxt then map_filter (try (nth xthms)) else K xthms
  in
    map snd xwthms
    |> map_index I
    |> append (map (pair ~1 o pair NONE) (Thm.assume cprop :: prems @ facts))
    |> check_topsorts ctxt
    |> apply_solver ctxt
    |> fst
    |> (fn (is, z3_steps) => {outcome = NONE, used_facts = filter_thms is, z3_steps = z3_steps})
  end
  handle SMT2_Failure.SMT fail => {outcome = SOME fail, used_facts = [], z3_steps = []}


(* SMT tactic *)

local
  fun trace_assumptions ctxt iwthms idxs =
    let
      val wthms =
        idxs
        |> filter (fn i => i >= 0)
        |> map_filter (AList.lookup (op =) iwthms)
    in
      if Config.get ctxt SMT2_Config.trace_used_facts andalso length wthms > 0
      then
        tracing (Pretty.string_of (Pretty.big_list "SMT used facts:"
          (map (Display.pretty_thm ctxt o snd) wthms)))
      else ()
    end

  fun solve ctxt iwthms =
    iwthms
    |> check_topsorts ctxt
    |> apply_solver ctxt
    |>> apfst (trace_assumptions ctxt iwthms)
    |> snd

  fun str_of ctxt fail =
    SMT2_Failure.string_of_failure ctxt fail
    |> prefix ("Solver " ^ SMT2_Config.solver_of ctxt ^ ": ")

  fun safe_solve ctxt iwthms = SOME (solve ctxt iwthms)
    handle
      SMT2_Failure.SMT (fail as SMT2_Failure.Counterexample _) =>
        (SMT2_Config.verbose_msg ctxt (str_of ctxt) fail; NONE)
    | SMT2_Failure.SMT (fail as SMT2_Failure.Time_Out) =>
        error ("SMT: Solver " ^ quote (SMT2_Config.solver_of ctxt) ^ ": " ^
          SMT2_Failure.string_of_failure ctxt fail ^ " (setting the " ^
          "configuration option " ^ quote (Config.name_of SMT2_Config.timeout) ^ " might help)")
    | SMT2_Failure.SMT fail => error (str_of ctxt fail)

  fun tag_rules thms = map_index (apsnd (pair NONE)) thms
  fun tag_prems thms = map (pair ~1 o pair NONE) thms

  fun resolve (SOME thm) = rtac thm 1
    | resolve NONE = no_tac

  fun tac prove ctxt rules =
    CONVERSION (SMT2_Normalize.atomize_conv ctxt)
    THEN' rtac @{thm ccontr}
    THEN' SUBPROOF (fn {context, prems, ...} =>
      resolve (prove context (tag_rules rules @ tag_prems prems))) ctxt
in

val smt2_tac = tac safe_solve
val smt2_tac' = tac (SOME oo solve)

end

end
