(*  Title:      HOL/Tools/SMT/smt_solver.ML
    Author:     Sascha Boehme, TU Muenchen

SMT solvers registry and SMT tactic.
*)

signature SMT_SOLVER =
sig
  (*configuration*)
  datatype outcome = Unsat | Sat | Unknown
  type solver_config = {
    name: string,
    class: SMT_Utils.class,
    avail: unit -> bool,
    command: unit -> string list,
    options: Proof.context -> string list,
    default_max_relevant: int,
    supports_filter: bool,
    outcome: string -> string list -> outcome * string list,
    cex_parser: (Proof.context -> SMT_Translate.recon -> string list ->
      term list * term list) option,
    reconstruct: (Proof.context -> SMT_Translate.recon -> string list ->
      int list * thm) option }

  (*registry*)
  val add_solver: solver_config -> theory -> theory
  val solver_name_of: Proof.context -> string
  val available_solvers_of: Proof.context -> string list
  val apply_solver: Proof.context -> (int * (int option * thm)) list ->
    int list * thm
  val default_max_relevant: Proof.context -> string -> int

  (*filter*)
  type 'a smt_filter_data =
    ('a * thm) list * ((int * thm) list * Proof.context)
  val smt_filter_preprocess: Proof.state ->
    ('a * (int option * thm)) list -> int -> 'a smt_filter_data
  val smt_filter_apply: Time.time -> 'a smt_filter_data ->
    {outcome: SMT_Failure.failure option, used_facts: ('a * thm) list}

  (*tactic*)
  val smt_tac: Proof.context -> thm list -> int -> tactic
  val smt_tac': Proof.context -> thm list -> int -> tactic

  (*setup*)
  val setup: theory -> theory
end

structure SMT_Solver: SMT_SOLVER =
struct


(* interface to external solvers *)

local

fun make_cmd command options problem_path proof_path = space_implode " " (
  map File.shell_quote (command () @ options) @
  [File.shell_path problem_path, "2>&1", ">", File.shell_path proof_path])

fun trace_and ctxt msg f x =
  let val _ = SMT_Config.trace_msg ctxt (fn () => msg) ()
  in f x end

fun run ctxt name mk_cmd input =
  (case SMT_Config.certificates_of ctxt of
    NONE =>
      if not (SMT_Config.is_available ctxt name) then
        error ("The SMT solver " ^ quote name ^ " is not installed.")
      else if Config.get ctxt SMT_Config.debug_files = "" then
        trace_and ctxt ("Invoking SMT solver " ^ quote name ^ " ...")
          (Cache_IO.run mk_cmd) input
      else
        let
          val base_path = Path.explode (Config.get ctxt SMT_Config.debug_files)
          val in_path = Path.ext "smt_in" base_path
          val out_path = Path.ext "smt_out" base_path
        in Cache_IO.raw_run mk_cmd input in_path out_path end
  | SOME certs =>
      (case Cache_IO.lookup certs input of
        (NONE, key) =>
          if Config.get ctxt SMT_Config.fixed then
            error ("Bad certificates cache: missing certificate")
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

    val _ = SMT_Config.trace_msg ctxt (pretty "Problem:" o split_lines) input

    val {redirected_output=res, output=err, return_code} =
      SMT_Config.with_timeout ctxt (run ctxt name mk_cmd) input
    val _ = SMT_Config.trace_msg ctxt (pretty "Solver:") err

    val ls = rev (snd (chop_while (equal "") (rev res)))
    val _ = SMT_Config.trace_msg ctxt (pretty "Result:") ls

    val _ = null ls andalso return_code <> 0 andalso
      raise SMT_Failure.SMT (SMT_Failure.Abnormal_Termination return_code)
  in ls end

fun trace_assms ctxt =
  SMT_Config.trace_msg ctxt (Pretty.string_of o
    Pretty.big_list "Assertions:" o map (Display.pretty_thm ctxt o snd))

fun trace_recon_data ({context=ctxt, typs, terms, ...} : SMT_Translate.recon) =
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

fun invoke name command ithms ctxt =
  let
    val options = SMT_Config.solver_options_of ctxt
    val comments = ("solver: " ^ name) ::
      ("timeout: " ^ string_of_real (Config.get ctxt SMT_Config.timeout)) ::
      ("random seed: " ^
        string_of_int (Config.get ctxt SMT_Config.random_seed)) ::
      "arguments:" :: options

    val (str, recon as {context=ctxt', ...}) =
      ithms
      |> tap (trace_assms ctxt)
      |> SMT_Translate.translate ctxt comments
      ||> tap trace_recon_data
  in (run_solver ctxt' name (make_cmd command options) str, recon) end

end


(* configuration *)

datatype outcome = Unsat | Sat | Unknown

type solver_config = {
  name: string,
  class: SMT_Utils.class,
  avail: unit -> bool,
  command: unit -> string list,
  options: Proof.context -> string list,
  default_max_relevant: int,
  supports_filter: bool,
  outcome: string -> string list -> outcome * string list,
  cex_parser: (Proof.context -> SMT_Translate.recon -> string list ->
    term list * term list) option,
  reconstruct: (Proof.context -> SMT_Translate.recon -> string list ->
    int list * thm) option }


(* registry *)

type solver_info = {
  command: unit -> string list,
  default_max_relevant: int,
  supports_filter: bool,
  reconstruct: Proof.context -> string list * SMT_Translate.recon ->
    int list * thm }

structure Solvers = Generic_Data
(
  type T = solver_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

local
  fun finish outcome cex_parser reconstruct ocl outer_ctxt
      (output, (recon as {context=ctxt, ...} : SMT_Translate.recon)) =
    (case outcome output of
      (Unsat, ls) =>
        if not (Config.get ctxt SMT_Config.oracle) andalso is_some reconstruct
        then the reconstruct outer_ctxt recon ls
        else ([], ocl ())
    | (result, ls) =>
        let
          val (ts, us) =
            (case cex_parser of SOME f => f ctxt recon ls | _ => ([], []))
         in
          raise SMT_Failure.SMT (SMT_Failure.Counterexample {
            is_real_cex = (result = Sat),
            free_constraints = ts,
            const_defs = us})
        end)

  val cfalse = Thm.cterm_of @{theory} (@{const Trueprop} $ @{const False})
in

fun add_solver cfg =
  let
    val {name, class, avail, command, options, default_max_relevant,
      supports_filter, outcome, cex_parser, reconstruct} = cfg

    fun core_oracle () = cfalse

    fun solver ocl = {
      command = command,
      default_max_relevant = default_max_relevant,
      supports_filter = supports_filter,
      reconstruct = finish (outcome name) cex_parser reconstruct ocl }

    val info = {name=name, class=class, avail=avail, options=options}
  in
    Thm.add_oracle (Binding.name name, core_oracle) #-> (fn (_, ocl) =>
    Context.theory_map (Solvers.map (Symtab.update_new (name, solver ocl)))) #>
    Context.theory_map (SMT_Config.add_solver info)
  end

end

fun get_info ctxt name =
  the (Symtab.lookup (Solvers.get (Context.Proof ctxt)) name)

val solver_name_of = SMT_Config.solver_of

val available_solvers_of = SMT_Config.available_solvers_of

fun name_and_info_of ctxt =
  let val name = solver_name_of ctxt
  in (name, get_info ctxt name) end

fun gen_preprocess ctxt iwthms = SMT_Normalize.normalize iwthms ctxt

fun gen_apply (ithms, ctxt) =
  let val (name, {command, reconstruct, ...}) = name_and_info_of ctxt
  in
    (ithms, ctxt)
    |-> invoke name command
    |> reconstruct ctxt
    |>> distinct (op =)
  end

fun apply_solver ctxt = gen_apply o gen_preprocess ctxt

val default_max_relevant = #default_max_relevant oo get_info

val supports_filter = #supports_filter o snd o name_and_info_of 


(* check well-sortedness *)

val has_topsort = Term.exists_type (Term.exists_subtype (fn
    TFree (_, []) => true
  | TVar (_, []) => true
  | _ => false))

(* without this test, we would run into problems when atomizing the rules: *)
fun check_topsort iwthms =
  if exists (has_topsort o Thm.prop_of o snd o snd) iwthms then
    raise SMT_Failure.SMT (SMT_Failure.Other_Failure ("proof state " ^
      "contains the universal sort {}"))
  else ()


(* filter *)

val cnot = Thm.cterm_of @{theory} @{const Not}

fun mk_result outcome xrules = { outcome = outcome, used_facts = xrules }

type 'a smt_filter_data = ('a * thm) list * ((int * thm) list * Proof.context)

fun smt_filter_preprocess st xwthms i =
  let
    val ctxt =
      Proof.context_of st
      |> Config.put SMT_Config.oracle false
      |> Config.put SMT_Config.drop_bad_facts true
      |> Config.put SMT_Config.filter_only_facts true

    val {facts, goal, ...} = Proof.goal st
    val ({context=ctxt', prems, concl, ...}, _) = Subgoal.focus ctxt i goal
    fun negate ct = Thm.dest_comb ct ||> Thm.apply cnot |-> Thm.apply
    val cprop =
      (case try negate (Thm.rhs_of (SMT_Normalize.atomize_conv ctxt' concl)) of
        SOME ct => ct
      | NONE => raise SMT_Failure.SMT (SMT_Failure.Other_Failure (
          "goal is not a HOL term")))
  in
    map snd xwthms
    |> map_index I
    |> append (map (pair ~1 o pair NONE) (Thm.assume cprop :: prems @ facts))
    |> tap check_topsort
    |> gen_preprocess ctxt'
    |> pair (map (apsnd snd) xwthms)
  end

fun smt_filter_apply time_limit (xthms, (ithms, ctxt)) =
  let
    val ctxt' =
      ctxt
      |> Config.put SMT_Config.timeout (Time.toReal time_limit)

    fun filter_thms false = K xthms
      | filter_thms true = map_filter (try (nth xthms)) o fst
  in
    (ithms, ctxt')
    |> gen_apply
    |> filter_thms (supports_filter ctxt')
    |> mk_result NONE
  end
  handle SMT_Failure.SMT fail => mk_result (SOME fail) []


(* SMT tactic *)

local
  fun trace_assumptions ctxt iwthms idxs =
    let
      val wthms =
        idxs
        |> filter (fn i => i >= 0)
        |> map_filter (AList.lookup (op =) iwthms)
    in
      if Config.get ctxt SMT_Config.trace_used_facts andalso length wthms > 0
      then
        tracing (Pretty.string_of (Pretty.big_list "SMT used facts:"
          (map (Display.pretty_thm ctxt o snd) wthms)))
      else ()
    end

  fun solve ctxt iwthms =
    iwthms
    |> tap check_topsort
    |> apply_solver ctxt
    |>> trace_assumptions ctxt iwthms
    |> snd

  fun str_of ctxt fail =
    SMT_Failure.string_of_failure ctxt fail
    |> prefix ("Solver " ^ SMT_Config.solver_of ctxt ^ ": ")

  fun safe_solve ctxt iwthms = SOME (solve ctxt iwthms)
    handle
      SMT_Failure.SMT (fail as SMT_Failure.Counterexample _) =>
        (SMT_Config.verbose_msg ctxt (str_of ctxt) fail; NONE)
    | SMT_Failure.SMT (fail as SMT_Failure.Time_Out) =>
        error ("SMT: Solver " ^ quote (SMT_Config.solver_of ctxt) ^ ": " ^
          SMT_Failure.string_of_failure ctxt fail ^ " (setting the " ^
          "configuration option " ^ quote (Config.name_of SMT_Config.timeout) ^ " might help)")
    | SMT_Failure.SMT fail => error (str_of ctxt fail)

  fun tag_rules thms = map_index (apsnd (pair NONE)) thms
  fun tag_prems thms = map (pair ~1 o pair NONE) thms

  fun resolve (SOME thm) = Tactic.rtac thm 1
    | resolve NONE = no_tac

  fun tac prove ctxt rules =
    CONVERSION (SMT_Normalize.atomize_conv ctxt)
    THEN' Tactic.rtac @{thm ccontr}
    THEN' SUBPROOF (fn {context, prems, ...} =>
      resolve (prove context (tag_rules rules @ tag_prems prems))) ctxt
in

val smt_tac = tac safe_solve
val smt_tac' = tac (SOME oo solve)

end


val smt_method =
  Scan.optional Attrib.thms [] >>
  (fn thms => fn ctxt => METHOD (fn facts =>
    HEADGOAL (smt_tac ctxt (thms @ facts))))


(* setup *)

val setup =
  Method.setup @{binding smt} smt_method
    "Applies an SMT solver to the current goal."

end
