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
    env_var: string,
    is_remote: bool,
    options: Proof.context -> string list,
    class: SMT_Utils.class,
    outcome: string -> string list -> outcome * string list,
    cex_parser: (Proof.context -> SMT_Translate.recon -> string list ->
      term list * term list) option,
    reconstruct: (Proof.context -> SMT_Translate.recon -> string list ->
      int list * thm) option,
    default_max_relevant: int }

  (*registry*)
  type solver = bool option -> Proof.context ->
    (int * (int option * thm)) list -> int list * thm
  val add_solver: solver_config -> theory -> theory
  val solver_name_of: Proof.context -> string
  val solver_of: Proof.context -> solver
  val available_solvers_of: Proof.context -> string list
  val is_locally_installed: Proof.context -> string -> bool
  val is_remotely_available: Proof.context -> string -> bool
  val default_max_relevant: Proof.context -> string -> int

  (*filter*)
  val smt_filter: bool -> Time.time -> Proof.state ->
    ('a * (int option * thm)) list -> int ->
    {outcome: SMT_Failure.failure option, used_facts: ('a * thm) list,
    run_time_in_msecs: int option}

  (*tactic*)
  val smt_tac': bool -> Proof.context -> thm list -> int -> Tactical.tactic
  val smt_tac: Proof.context -> thm list -> int -> Tactical.tactic

  (*setup*)
  val setup: theory -> theory
end

structure SMT_Solver: SMT_SOLVER =
struct

structure C = SMT_Config


(* configuration *)

datatype outcome = Unsat | Sat | Unknown

type solver_config = {
  name: string,
  env_var: string,
  is_remote: bool,
  options: Proof.context -> string list,
  class: SMT_Utils.class,
  outcome: string -> string list -> outcome * string list,
  cex_parser: (Proof.context -> SMT_Translate.recon -> string list ->
    term list * term list) option,
  reconstruct: (Proof.context -> SMT_Translate.recon -> string list ->
    int list * thm) option,
  default_max_relevant: int }


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
  (case C.certificates_of ctxt of
    NONE =>
      if Config.get ctxt C.debug_files = "" then
        Cache_IO.run (make_cmd (choose cmd) args) input
      else
        let
          val base_path = Path.explode (Config.get ctxt C.debug_files)
          val in_path = Path.ext "smt_in" base_path
          val out_path = Path.ext "smt_out" base_path
        in
          Cache_IO.raw_run (make_cmd (choose cmd) args) input in_path out_path 
        end
  | SOME certs =>
      (case Cache_IO.lookup certs input of
        (NONE, key) =>
          if Config.get ctxt C.fixed then
            error ("Bad certificates cache: missing certificate")
          else
            Cache_IO.run_and_cache certs key (make_cmd (choose cmd) args) input
      | (SOME output, _) =>
         (tracing ("Using cached certificate from " ^
            File.shell_path (Cache_IO.cache_path_of certs) ^ " ...");
          output)))

in

fun run_solver ctxt cmd args input =
  let
    fun pretty tag ls = Pretty.string_of (Pretty.big_list tag
      (map Pretty.str ls))

    val _ = C.trace_msg ctxt (pretty "Problem:" o split_lines) input

    val {redirected_output=res, output=err, return_code} =
      C.with_timeout ctxt (run ctxt cmd args) input
    val _ = C.trace_msg ctxt (pretty "Solver:") err

    val ls = rev (snd (chop_while (equal "") (rev res)))
    val _ = C.trace_msg ctxt (pretty "Result:") ls

    val _ = null ls andalso return_code <> 0 andalso
      raise SMT_Failure.SMT (SMT_Failure.Abnormal_Termination return_code)
  in ls end

end

fun trace_assms ctxt = C.trace_msg ctxt (Pretty.string_of o
  Pretty.big_list "Assertions:" o map (Display.pretty_thm ctxt o snd))

fun trace_recon_data ({context=ctxt, typs, terms, ...} : SMT_Translate.recon) =
  let
    fun pretty_eq n p = Pretty.block [Pretty.str n, Pretty.str " = ", p]
    fun p_typ (n, T) = pretty_eq n (Syntax.pretty_typ ctxt T)
    fun p_term (n, t) = pretty_eq n (Syntax.pretty_term ctxt t)
  in
    C.trace_msg ctxt (fn () =>
      Pretty.string_of (Pretty.big_list "Names:" [
        Pretty.big_list "sorts:" (map p_typ (Symtab.dest typs)),
        Pretty.big_list "functions:" (map p_term (Symtab.dest terms))])) ()
  end

fun invoke name cmd options ithms ctxt =
  let
    val args = C.solver_options_of ctxt @ options ctxt
    val comments = ("solver: " ^ name) ::
      ("timeout: " ^ string_of_real (Config.get ctxt C.timeout)) ::
      ("random seed: " ^ string_of_int (Config.get ctxt C.random_seed)) ::
      "arguments:" :: args

    val (str, recon as {context=ctxt', ...}) =
      ithms
      |> tap (trace_assms ctxt)
      |> SMT_Translate.translate ctxt comments
      ||> tap trace_recon_data
  in (run_solver ctxt' cmd args str, recon) end

fun trace_assumptions ctxt iwthms idxs =
  let
    val wthms =
      idxs
      |> filter (fn i => i >= 0)
      |> map_filter (AList.lookup (op =) iwthms)
  in
    if Config.get ctxt C.trace_used_facts andalso length wthms > 0
    then
      tracing (Pretty.string_of (Pretty.big_list "SMT used facts:"
        (map (Display.pretty_thm ctxt o snd) wthms)))
    else ()
  end



(* registry *)

type solver = bool option -> Proof.context -> (int * (int option * thm)) list ->
  int list * thm

type solver_info = {
  env_var: string,
  is_remote: bool,
  options: Proof.context -> string list,
  reconstruct: Proof.context -> string list * SMT_Translate.recon ->
    int list * thm,
  default_max_relevant: int }

fun gen_solver name (info : solver_info) rm ctxt iwthms =
  let
    val {env_var, is_remote, options, reconstruct, ...} = info
    val cmd = (rm, env_var, is_remote, name)
  in
    SMT_Normalize.normalize ctxt iwthms
    |> rpair ctxt
    |-> SMT_Monomorph.monomorph
    |-> invoke name cmd options
    |> reconstruct ctxt
    |> (fn (idxs, thm) => thm
    |> tap (fn _ => trace_assumptions ctxt iwthms idxs)
    |> pair idxs)
  end

structure Solvers = Generic_Data
(
  type T = solver_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
    handle Symtab.DUP name => error ("Duplicate SMT solver: " ^ quote name)
)

local
  fun finish outcome cex_parser reconstruct ocl outer_ctxt
      (output, (recon as {context=ctxt, ...} : SMT_Translate.recon)) =
    (case outcome output of
      (Unsat, ls) =>
        if not (Config.get ctxt C.oracle) andalso is_some reconstruct
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
    val {name, env_var, is_remote, options, class, outcome, cex_parser,
      reconstruct, default_max_relevant} = cfg

    fun core_oracle () = cfalse

    fun solver ocl = { env_var=env_var, is_remote=is_remote, options=options,
      reconstruct=finish (outcome name) cex_parser reconstruct ocl,
      default_max_relevant=default_max_relevant }
  in
    Thm.add_oracle (Binding.name name, core_oracle) #-> (fn (_, ocl) =>
    Context.theory_map (Solvers.map (Symtab.update_new (name, solver ocl)))) #>
    Context.theory_map (C.add_solver (name, class))
  end

end

fun get_info ctxt name =
  the (Symtab.lookup (Solvers.get (Context.Proof ctxt)) name)

fun name_and_solver_of ctxt =
  let val name = C.solver_of ctxt
  in (name, get_info ctxt name) end

val solver_name_of = fst o name_and_solver_of
fun solver_of ctxt =
  let val (name, raw_solver) = name_and_solver_of ctxt
  in gen_solver name raw_solver end

val available_solvers_of = Symtab.keys o Solvers.get o Context.Proof

fun is_locally_installed ctxt name =
  let val {env_var, ...} = get_info ctxt name
  in is_some (get_local_solver env_var) end

val is_remotely_available = #is_remote oo get_info

val default_max_relevant = #default_max_relevant oo get_info


(* filter *)

val has_topsort = Term.exists_type (Term.exists_subtype (fn
    TFree (_, []) => true
  | TVar (_, []) => true
  | _ => false))

fun smt_solver rm ctxt iwthms =
  (* without this test, we would run into problems when atomizing the rules: *)
  if exists (has_topsort o Thm.prop_of o snd o snd) iwthms then
    raise SMT_Failure.SMT (SMT_Failure.Other_Failure ("proof state " ^
      "contains the universal sort {}"))
  else solver_of ctxt rm ctxt iwthms

val cnot = Thm.cterm_of @{theory} @{const Not}

fun mk_result outcome xrules =
  { outcome = outcome, used_facts = xrules, run_time_in_msecs = NONE }

fun smt_filter run_remote time_limit st xwrules i =
  let
    val ctxt =
      Proof.context_of st
      |> Config.put C.oracle false
      |> Config.put C.timeout (Time.toReal time_limit)
      |> Config.put C.drop_bad_facts true
      |> Config.put C.filter_only_facts true

    val {facts, goal, ...} = Proof.goal st
    val ({context=ctxt', prems, concl, ...}, _) = Subgoal.focus ctxt i goal
    fun negate ct = Thm.dest_comb ct ||> Thm.capply cnot |-> Thm.capply
    val cprop = negate (Thm.rhs_of (SMT_Normalize.atomize_conv ctxt' concl))

    val (xs, wthms) = split_list xwrules
    val xrules = xs ~~ map snd wthms
  in
    wthms
    |> map_index I
    |> append (map (pair ~1 o pair NONE) (Thm.assume cprop :: prems @ facts))
    |> smt_solver (SOME run_remote) ctxt'
    |> distinct (op =) o fst
    |> map_filter (try (nth xrules))
    |> (if solver_name_of ctxt = "z3" (* FIXME *) then I else K xrules)
    |> mk_result NONE
  end
  handle SMT_Failure.SMT fail => mk_result (SOME fail) []
  (* FIXME: measure runtime *)



(* SMT tactic *)

fun smt_tac' pass_exns ctxt rules =
  CONVERSION (SMT_Normalize.atomize_conv ctxt)
  THEN' Tactic.rtac @{thm ccontr}
  THEN' SUBPROOF (fn {context=ctxt', prems, ...} =>
    let
      fun solve iwthms = snd (smt_solver NONE ctxt' iwthms)
      val tag = "Solver " ^ C.solver_of ctxt' ^ ": "
      val str_of = prefix tag o SMT_Failure.string_of_failure ctxt'
      fun safe_solve iwthms =
        if pass_exns then SOME (solve iwthms)
        else (SOME (solve iwthms)
          handle
            SMT_Failure.SMT (fail as SMT_Failure.Counterexample _) =>
              (C.verbose_msg ctxt' str_of fail; NONE)
          | SMT_Failure.SMT fail => (C.trace_msg ctxt' str_of fail; NONE))
    in
      safe_solve (map (pair ~1 o pair NONE) (rules @ prems))
      |> (fn SOME thm => Tactic.rtac thm 1 | _ => Tactical.no_tac)
    end) ctxt

val smt_tac = smt_tac' false

val smt_method =
  Scan.optional Attrib.thms [] >>
  (fn thms => fn ctxt => METHOD (fn facts =>
    HEADGOAL (smt_tac ctxt (thms @ facts))))



(* setup *)

val setup =
  Method.setup @{binding smt} smt_method
    "Applies an SMT solver to the current goal."

end
