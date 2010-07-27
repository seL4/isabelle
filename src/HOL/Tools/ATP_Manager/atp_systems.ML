(*  Title:      HOL/Tools/ATP_Manager/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature ATP_SYSTEMS =
sig
  val trace : bool Unsynchronized.ref
  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val measure_runtime : bool Config.T
  val refresh_systems_on_tptp : unit -> unit
  val default_atps_param_value : unit -> string
  val setup : theory -> theory
end;

structure ATP_Systems : ATP_SYSTEMS =
struct

open Metis_Clauses
open Sledgehammer_Util
open Sledgehammer_Fact_Filter
open Sledgehammer_TPTP_Format
open Sledgehammer_Proof_Reconstruct
open ATP_Manager

val trace = Unsynchronized.ref false
fun trace_msg msg = if !trace then tracing (msg ()) else ()

(** generic ATP **)

(* external problem files *)

val (dest_dir, dest_dir_setup) = Attrib.config_string "atp_dest_dir" (K "");
  (*Empty string means create files in Isabelle's temporary files directory.*)

val (problem_prefix, problem_prefix_setup) =
  Attrib.config_string "atp_problem_prefix" (K "prob");

val (measure_runtime, measure_runtime_setup) =
  Attrib.config_bool "atp_measure_runtime" (K false);


(* prover configuration *)

type prover_config =
  {home_var: string,
   executable: string,
   arguments: bool -> Time.time -> string,
   proof_delims: (string * string) list,
   known_failures: (failure * string) list,
   max_new_relevant_facts_per_iter: int,
   prefers_theory_relevant: bool,
   explicit_forall: bool}


(* basic template *)

val remotify = prefix "remote_"

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path)

(* Splits by the first possible of a list of delimiters. *)
fun extract_proof delims output =
  case pairself (find_first (fn s => String.isSubstring s output))
                (ListPair.unzip delims) of
    (SOME begin_delim, SOME end_delim) =>
    (output |> first_field begin_delim |> the |> snd
            |> first_field end_delim |> the |> fst
            |> first_field "\n" |> the |> snd
     handle Option.Option => "")
  | _ => ""

fun extract_proof_and_outcome complete res_code proof_delims known_failures
                              output =
  case map_filter (fn (failure, pattern) =>
                      if String.isSubstring pattern output then SOME failure
                      else NONE) known_failures of
    [] => (case extract_proof proof_delims output of
             "" => ("", SOME UnknownError)
           | proof => if res_code = 0 then (proof, NONE)
                      else ("", SOME UnknownError))
  | (failure :: _) =>
    ("", SOME (if failure = IncompleteUnprovable andalso complete then
                 Unprovable
               else
                 failure))

fun string_for_failure Unprovable = "The ATP problem is unprovable."
  | string_for_failure IncompleteUnprovable =
    "The ATP cannot prove the problem."
  | string_for_failure CantConnect = "Can't connect to remote ATP."
  | string_for_failure TimedOut = "Timed out."
  | string_for_failure OutOfResources = "The ATP ran out of resources."
  | string_for_failure OldSpass =
    (* FIXME: Change the error message below to point to the Isabelle download
       page once the package is there. *)
    "Warning: Sledgehammer requires a more recent version of SPASS with \
    \support for the TPTP syntax. To install it, download and untar the \
    \package \"http://isabelle.in.tum.de/~blanchet/spass-3.7.tgz\" and add the \
    \\"spass-3.7\" directory's full path to \"" ^
    Path.implode (Path.expand (Path.appends
        (Path.variable "ISABELLE_HOME_USER" ::
         map Path.basic ["etc", "components"]))) ^
    "\" on a line of its own."
  | string_for_failure MalformedInput =
    "Internal Sledgehammer error: The ATP problem is malformed. Please report \
    \this to the Isabelle developers."
  | string_for_failure MalformedOutput = "Error: The ATP output is malformed."
  | string_for_failure UnknownError = "Error: An unknown ATP error occurred."


(* Clause preparation *)

fun make_clause_table xs =
  fold (Termtab.update o `(prop_of o snd)) xs Termtab.empty

(* Remove existing axiom clauses from the conjecture clauses, as this can
   dramatically boost an ATP's performance (for some reason). *)
fun subtract_cls ax_clauses =
  filter_out (Termtab.defined (make_clause_table ax_clauses) o prop_of)

fun combformula_for_prop thy =
  let
    val do_term = combterm_from_term thy
    fun do_quant bs q s T t' =
      do_formula ((s, T) :: bs) t'
      #>> (fn phi => AQuant (q, [`make_bound_var s], phi))
    and do_conn bs c t1 t2 =
      do_formula bs t1 ##>> do_formula bs t2
      #>> (fn (phi1, phi2) => AConn (c, [phi1, phi2]))
    and do_formula bs t =
      case t of
        @{const Not} $ t1 =>
        do_formula bs t1 #>> (fn phi => AConn (ANot, [phi]))
      | Const (@{const_name All}, _) $ Abs (s, T, t') =>
        do_quant bs AForall s T t'
      | Const (@{const_name Ex}, _) $ Abs (s, T, t') =>
        do_quant bs AExists s T t'
      | @{const "op &"} $ t1 $ t2 => do_conn bs AAnd t1 t2
      | @{const "op |"} $ t1 $ t2 => do_conn bs AOr t1 t2
      | @{const "op -->"} $ t1 $ t2 => do_conn bs AImplies t1 t2
      | Const (@{const_name "op ="}, Type (_, [@{typ bool}, _])) $ t1 $ t2 =>
        do_conn bs AIff t1 t2
      | _ => (fn ts => do_term bs (Envir.eta_contract t)
                       |>> APred ||> union (op =) ts)
  in do_formula [] end

(* Converts an elim-rule into an equivalent theorem that does not have the
   predicate variable. Leaves other theorems unchanged. We simply instantiate
   the conclusion variable to False. (Cf. "transform_elim_term" in
   "ATP_Systems".) *)
(* FIXME: test! *)
fun transform_elim_term t =
  case Logic.strip_imp_concl t of
    @{const Trueprop} $ Var (z, @{typ bool}) =>
    subst_Vars [(z, @{const True})] t
  | Var (z, @{typ prop}) => subst_Vars [(z, @{prop True})] t
  | _ => t

(* Removes the lambdas from an equation of the form "t = (%x. u)".
   (Cf. "extensionalize_theorem" in "Clausifier".) *)
fun extensionalize_term t =
  let
    fun aux j (Const (@{const_name "op ="}, Type (_, [Type (_, [_, T']), _]))
               $ t2 $ Abs (s, var_T, t')) =
        let val var_t = Var (("x", j), var_T) in
          Const (@{const_name "op ="}, T' --> T' --> HOLogic.boolT)
            $ betapply (t2, var_t) $ subst_bound (var_t, t')
          |> aux (j + 1)
        end
      | aux _ t = t
  in aux (maxidx_of_term t + 1) t end

(* FIXME: Guarantee freshness *)
fun concealed_bound_name j = "Sledgehammer" ^ Int.toString j
fun conceal_bounds Ts t =
  subst_bounds (map (Free o apfst concealed_bound_name)
                    (length Ts - 1 downto 0 ~~ rev Ts), t)
fun reveal_bounds Ts =
  subst_atomic (map (fn (j, T) => (Free (concealed_bound_name j, T), Bound j))
                    (0 upto length Ts - 1 ~~ Ts))

fun introduce_combinators_in_term ctxt kind t =
  let
    val thy = ProofContext.theory_of ctxt
    fun aux Ts t =
      case t of
        @{const Not} $ t1 => @{const Not} $ aux Ts t1
      | (t0 as Const (@{const_name All}, _)) $ Abs (s, T, t') =>
        t0 $ Abs (s, T, aux (T :: Ts) t')
      | (t0 as Const (@{const_name Ex}, _)) $ Abs (s, T, t') =>
        t0 $ Abs (s, T, aux (T :: Ts) t')
      | (t0 as @{const "op &"}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
      | (t0 as @{const "op |"}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
      | (t0 as @{const "op -->"}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
      | (t0 as Const (@{const_name "op ="}, Type (_, [@{typ bool}, _])))
          $ t1 $ t2 =>
        t0 $ aux Ts t1 $ aux Ts t2
      | _ => if not (exists_subterm (fn Abs _ => true | _ => false) t) then
               t
             else
               let
                 val t = t |> conceal_bounds Ts
                           |> Envir.eta_contract
                 val ([t], ctxt') = Variable.import_terms true [t] ctxt
               in
                 t |> cterm_of thy
                   |> Clausifier.introduce_combinators_in_cterm
                   |> singleton (Variable.export ctxt' ctxt)
                   |> prop_of |> Logic.dest_equals |> snd
                   |> reveal_bounds Ts
               end
  in t |> not (Meson.is_fol_term thy t) ? aux [] end
  handle THM _ =>
         (* A type variable of sort "{}" will make abstraction fail. *)
         case kind of
           Axiom => HOLogic.true_const
         | Conjecture => HOLogic.false_const

(* making axiom and conjecture clauses *)
fun make_clause ctxt (formula_name, kind, t) =
  let
    val thy = ProofContext.theory_of ctxt
    (* ### FIXME: perform other transformations previously done by
       "Clausifier.to_nnf", e.g. "HOL.If" *)
    val t = t |> transform_elim_term
              |> Object_Logic.atomize_term thy
              |> extensionalize_term
              |> introduce_combinators_in_term ctxt kind
    val (combformula, ctypes_sorts) = combformula_for_prop thy t []
  in
    FOLFormula {formula_name = formula_name, combformula = combformula,
                kind = kind, ctypes_sorts = ctypes_sorts}
  end

fun make_axiom_clause ctxt (name, th) =
  (name, make_clause ctxt (name, Axiom, prop_of th))
fun make_conjecture_clauses ctxt ts =
  map2 (fn j => fn t => make_clause ctxt (Int.toString j, Conjecture, t))
       (0 upto length ts - 1) ts

(** Helper clauses **)

fun count_combterm (CombConst ((s, _), _, _)) =
    Symtab.map_entry s (Integer.add 1)
  | count_combterm (CombVar _) = I
  | count_combterm (CombApp (t1, t2)) = fold count_combterm [t1, t2]
fun count_combformula (AQuant (_, _, phi)) = count_combformula phi
  | count_combformula (AConn (_, phis)) = fold count_combformula phis
  | count_combformula (APred tm) = count_combterm tm
fun count_fol_formula (FOLFormula {combformula, ...}) =
  count_combformula combformula

val optional_helpers =
  [(["c_COMBI", "c_COMBK"], @{thms COMBI_def COMBK_def}),
   (["c_COMBB", "c_COMBC"], @{thms COMBB_def COMBC_def}),
   (["c_COMBS"], @{thms COMBS_def})]
val optional_typed_helpers =
  [(["c_True", "c_False"], @{thms True_or_False}),
   (["c_If"], @{thms if_True if_False True_or_False})]
val mandatory_helpers = @{thms fequal_imp_equal equal_imp_fequal}

val init_counters =
  Symtab.make (maps (maps (map (rpair 0) o fst))
                    [optional_helpers, optional_typed_helpers])

fun get_helper_clauses ctxt is_FO full_types conjectures axclauses =
  let
    val ct = fold (fold count_fol_formula) [conjectures, axclauses]
                  init_counters
    fun is_needed c = the (Symtab.lookup ct c) > 0
    val cnfs =
      (optional_helpers
       |> full_types ? append optional_typed_helpers
       |> maps (fn (ss, ths) =>
                   if exists is_needed ss then map (`Thm.get_name_hint) ths
                   else [])) @
      (if is_FO then [] else map (`Thm.get_name_hint) mandatory_helpers)
  in map (snd o make_axiom_clause ctxt) cnfs end

fun s_not (@{const Not} $ t) = t
  | s_not t = @{const Not} $ t

(* prepare for passing to writer,
   create additional clauses based on the information from extra_cls *)
fun prepare_clauses ctxt full_types hyp_ts concl_t axcls extra_cls =
  let
    val thy = ProofContext.theory_of ctxt
    val goal_t = Logic.list_implies (hyp_ts, concl_t)
    val is_FO = Meson.is_fol_term thy goal_t
    val _ = trace_msg (fn _ => Syntax.string_of_term ctxt goal_t)
    val axtms = map (prop_of o snd) extra_cls
    val subs = tfree_classes_of_terms [goal_t]
    val supers = tvar_classes_of_terms axtms
    val tycons = type_consts_of_terms thy (goal_t :: axtms)
    (* TFrees in conjecture clauses; TVars in axiom clauses *)
    val conjectures =
      map (s_not o HOLogic.dest_Trueprop) hyp_ts @
        [HOLogic.dest_Trueprop concl_t]
      |> make_conjecture_clauses ctxt
    val extra_clauses = map (snd o make_axiom_clause ctxt) extra_cls
    val (clnames, axiom_clauses) =
      ListPair.unzip (map (make_axiom_clause ctxt) axcls)
    (* FIXME: Should it read "extra_clauses" or "axiom_clauses" in the
       "get_helper_clauses" call? *)
    val helper_clauses =
      get_helper_clauses ctxt is_FO full_types conjectures extra_clauses
    val (supers', arity_clauses) = make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in
    (Vector.fromList clnames,
      (conjectures, axiom_clauses, extra_clauses, helper_clauses,
       class_rel_clauses, arity_clauses))
  end

fun extract_clause_sequence output =
  let
    val tokens_of = String.tokens (not o Char.isAlphaNum)
    fun extract_num ("clause" :: (ss as _ :: _)) =
    Int.fromString (List.last ss)
      | extract_num _ = NONE
  in output |> split_lines |> map_filter (extract_num o tokens_of) end

val set_ClauseFormulaRelationN = "set_ClauseFormulaRelation"

val parse_clause_formula_pair =
  $$ "(" |-- scan_integer --| $$ "," -- Symbol.scan_id --| $$ ")"
  --| Scan.option ($$ ",")
val parse_clause_formula_relation =
  Scan.this_string set_ClauseFormulaRelationN |-- $$ "("
  |-- Scan.repeat parse_clause_formula_pair
val extract_clause_formula_relation =
  Substring.full
  #> Substring.position set_ClauseFormulaRelationN
  #> snd #> Substring.string #> strip_spaces #> explode
  #> parse_clause_formula_relation #> fst

fun repair_conjecture_shape_and_theorem_names output conjecture_shape
                                              thm_names =
  if String.isSubstring set_ClauseFormulaRelationN output then
    (* This is a hack required for keeping track of axioms after they have been
       clausified by SPASS's Flotter tool. The "SPASS_TPTP" script is also part
       of this hack. *)
    let
      val j0 = hd conjecture_shape
      val seq = extract_clause_sequence output
      val name_map = extract_clause_formula_relation output
      fun renumber_conjecture j =
        AList.find (op =) name_map (conjecture_prefix ^ Int.toString (j - j0))
        |> the_single
        |> (fn s => find_index (curry (op =) s) seq + 1)
    in
      (conjecture_shape |> map renumber_conjecture,
       seq |> map (the o AList.lookup (op =) name_map)
           |> map (fn s => case try (unprefix axiom_prefix) s of
                             SOME s' => undo_ascii_of s'
                           | NONE => "")
           |> Vector.fromList)
    end
  else
    (conjecture_shape, thm_names)


(* generic TPTP-based provers *)

fun generic_tptp_prover
        (name, {home_var, executable, arguments, proof_delims, known_failures,
                max_new_relevant_facts_per_iter, prefers_theory_relevant,
                explicit_forall})
        ({debug, overlord, full_types, explicit_apply, relevance_threshold,
          relevance_convergence, theory_relevant, defs_relevant, isar_proof,
          isar_shrink_factor, ...} : params)
        minimize_command timeout
        ({subgoal, goal, relevance_override, axiom_clauses, filtered_clauses}
         : problem) =
  let
    (* get clauses and prepare them for writing *)
    val (ctxt, (_, th)) = goal;
    val thy = ProofContext.theory_of ctxt
    (* ### FIXME: (1) preprocessing for "if" etc. *)
    val (params, hyp_ts, concl_t) = strip_subgoal th subgoal
    val the_filtered_clauses =
      case filtered_clauses of
        SOME fcls => fcls
      | NONE => relevant_facts full_types relevance_threshold
                    relevance_convergence defs_relevant
                    max_new_relevant_facts_per_iter
                    (the_default prefers_theory_relevant theory_relevant)
                    relevance_override goal hyp_ts concl_t
    val the_axiom_clauses = axiom_clauses |> the_default the_filtered_clauses
    val (internal_thm_names, clauses) =
      prepare_clauses ctxt full_types hyp_ts concl_t the_axiom_clauses
                      the_filtered_clauses

    (* path to unique problem file *)
    val the_dest_dir = if overlord then getenv "ISABELLE_HOME_USER"
                       else Config.get ctxt dest_dir;
    val the_problem_prefix = Config.get ctxt problem_prefix;
    fun prob_pathname nr =
      let
        val probfile =
          Path.basic ((if overlord then "prob_" ^ name
                       else the_problem_prefix ^ serial_string ())
                      ^ "_" ^ string_of_int nr)
      in
        if the_dest_dir = "" then File.tmp_path probfile
        else if File.exists (Path.explode the_dest_dir)
        then Path.append (Path.explode the_dest_dir) probfile
        else error ("No such directory: " ^ the_dest_dir ^ ".")
      end;

    val home = getenv home_var
    val command = Path.explode (home ^ "/" ^ executable)
    (* write out problem file and call prover *)
    fun command_line complete probfile =
      let
        val core = File.shell_path command ^ " " ^ arguments complete timeout ^
                   " " ^ File.shell_path probfile
      in
        (if Config.get ctxt measure_runtime then
           "TIMEFORMAT='%3U'; { time " ^ core ^ " ; }"
         else
           "exec " ^ core) ^ " 2>&1"
      end
    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n");
        val (output, t) = s |> split |> split_last |> apfst cat_lines;
        fun as_num f = f >> (fst o read_int);
        val num = as_num (Scan.many1 Symbol.is_ascii_digit);
        val digit = Scan.one Symbol.is_ascii_digit;
        val num3 = as_num (digit ::: digit ::: (digit >> single));
        val time = num --| Scan.$$ "." -- num3 >> (fn (a, b) => a * 1000 + b);
        val as_time = the_default 0 o Scan.read Symbol.stopper time o explode;
      in (output, as_time t) end;
    fun run_on probfile =
      if home = "" then
        error ("The environment variable " ^ quote home_var ^ " is not set.")
      else if File.exists command then
        let
          fun do_run complete =
            let
              val command = command_line complete probfile
              val ((output, msecs), res_code) =
                bash_output command
                |>> (if overlord then
                       prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n")
                     else
                       I)
                |>> (if Config.get ctxt measure_runtime then split_time
                     else rpair 0)
              val (proof, outcome) =
                extract_proof_and_outcome complete res_code proof_delims
                                          known_failures output
            in (output, msecs, proof, outcome) end
          val readable_names = debug andalso overlord
          val (pool, conjecture_offset) =
            write_tptp_file thy readable_names explicit_forall full_types
                            explicit_apply probfile clauses
          val conjecture_shape =
            conjecture_offset + 1 upto conjecture_offset + length hyp_ts + 1
          val result =
            do_run false
            |> (fn (_, msecs0, _, SOME _) =>
                   do_run true
                   |> (fn (output, msecs, proof, outcome) =>
                          (output, msecs0 + msecs, proof, outcome))
                 | result => result)
        in ((pool, conjecture_shape), result) end
      else
        error ("Bad executable: " ^ Path.implode command ^ ".");

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun cleanup probfile =
      if the_dest_dir = "" then try File.rm probfile else NONE
    fun export probfile (_, (output, _, _, _)) =
      if the_dest_dir = "" then
        ()
      else
        File.write (Path.explode (Path.implode probfile ^ "_proof")) output

    val ((pool, conjecture_shape), (output, msecs, proof, outcome)) =
      with_path cleanup export run_on (prob_pathname subgoal)
    val (conjecture_shape, internal_thm_names) =
      repair_conjecture_shape_and_theorem_names output conjecture_shape
                                                internal_thm_names

    val (message, used_thm_names) =
      case outcome of
        NONE =>
        proof_text isar_proof
            (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
            (full_types, minimize_command, proof, internal_thm_names, th,
             subgoal)
      | SOME failure => (string_for_failure failure ^ "\n", [])
  in
    {outcome = outcome, message = message, pool = pool,
     used_thm_names = used_thm_names, atp_run_time_in_msecs = msecs,
     output = output, proof = proof, internal_thm_names = internal_thm_names,
     conjecture_shape = conjecture_shape,
     filtered_clauses = the_filtered_clauses}
  end

fun tptp_prover name p = (name, generic_tptp_prover (name, p));

fun to_generous_secs time = (Time.toMilliseconds time + 999) div 1000

(* E prover *)

val tstp_proof_delims =
  ("# SZS output start CNFRefutation.", "# SZS output end CNFRefutation")

val e_config : prover_config =
  {home_var = "E_HOME",
   executable = "eproof",
   arguments = fn _ => fn timeout =>
     "--tstp-in --tstp-out -l5 -xAutoDev -tAutoDev --silent --cpu-limit=" ^
     string_of_int (to_generous_secs timeout),
   proof_delims = [tstp_proof_delims],
   known_failures =
     [(Unprovable, "SZS status: CounterSatisfiable"),
      (Unprovable, "SZS status CounterSatisfiable"),
      (TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded"),
      (OutOfResources,
       "# Cannot determine problem status within resource limit"),
      (OutOfResources, "SZS status: ResourceOut"),
      (OutOfResources, "SZS status ResourceOut")],
   max_new_relevant_facts_per_iter = 80 (* FIXME *),
   prefers_theory_relevant = false,
   explicit_forall = false}
val e = tptp_prover "e" e_config


(* The "-VarWeight=3" option helps the higher-order problems, probably by
   counteracting the presence of "hAPP". *)
val spass_config : prover_config =
  {home_var = "ISABELLE_ATP_MANAGER",
   executable = "SPASS_TPTP",
   (* "div 2" accounts for the fact that SPASS is often run twice. *)
   arguments = fn complete => fn timeout =>
     ("-Auto -PGiven=0 -PProblem=0 -Splits=0 -FullRed=0 -DocProof \
      \-VarWeight=3 -TimeLimit=" ^
      string_of_int (to_generous_secs timeout div 2))
     |> not complete ? prefix "-SOS=1 ",
   proof_delims = [("Here is a proof", "Formulae used in the proof")],
   known_failures =
     [(IncompleteUnprovable, "SPASS beiseite: Completion found"),
      (TimedOut, "SPASS beiseite: Ran out of time"),
      (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
      (MalformedInput, "Undefined symbol"),
      (MalformedInput, "Free Variable"),
      (OldSpass, "tptp2dfg")],
   max_new_relevant_facts_per_iter = 26 (* FIXME *),
   prefers_theory_relevant = true,
   explicit_forall = true}
val spass = tptp_prover "spass" spass_config

(* Vampire *)

val vampire_config : prover_config =
  {home_var = "VAMPIRE_HOME",
   executable = "vampire",
   arguments = fn _ => fn timeout =>
     "--output_syntax tptp --mode casc -t " ^
     string_of_int (to_generous_secs timeout),
   proof_delims =
     [("=========== Refutation ==========",
       "======= End of refutation ======="),
      ("% SZS output start Refutation", "% SZS output end Refutation")],
   known_failures =
     [(Unprovable, "UNPROVABLE"),
      (IncompleteUnprovable, "CANNOT PROVE"),
      (Unprovable, "Satisfiability detected"),
      (OutOfResources, "Refutation not found")],
   max_new_relevant_facts_per_iter = 40 (* FIXME *),
   prefers_theory_relevant = false,
   explicit_forall = false}
val vampire = tptp_prover "vampire" vampire_config

(* Remote prover invocation via SystemOnTPTP *)

val systems = Synchronized.var "atp_systems" ([]: string list);

fun get_systems () =
  case bash_output "\"$ISABELLE_ATP_MANAGER/SystemOnTPTP\" -w" of
    (answer, 0) => split_lines answer
  | (answer, _) =>
    error ("Failed to get available systems at SystemOnTPTP:\n" ^
           perhaps (try (unsuffix "\n")) answer)

fun refresh_systems_on_tptp () =
  Synchronized.change systems (fn _ => get_systems ())

fun get_system prefix = Synchronized.change_result systems (fn systems =>
  (if null systems then get_systems () else systems)
  |> `(find_first (String.isPrefix prefix)));

fun the_system prefix =
  (case get_system prefix of
    NONE => error ("System " ^ quote prefix ^ " not available at SystemOnTPTP.")
  | SOME sys => sys);

val remote_known_failures =
  [(CantConnect, "HTTP-Error"),
   (TimedOut, "says Timeout"),
   (MalformedOutput, "Remote script could not extract proof")]

fun remote_config atp_prefix args
        ({proof_delims, known_failures, max_new_relevant_facts_per_iter,
          prefers_theory_relevant, explicit_forall, ...} : prover_config)
        : prover_config =
  {home_var = "ISABELLE_ATP_MANAGER",
   executable = "SystemOnTPTP",
   arguments = fn _ => fn timeout =>
     args ^ " -t " ^ string_of_int (to_generous_secs timeout) ^ " -s " ^
     the_system atp_prefix,
   proof_delims = insert (op =) tstp_proof_delims proof_delims,
   known_failures = remote_known_failures @ known_failures,
   max_new_relevant_facts_per_iter = max_new_relevant_facts_per_iter,
   prefers_theory_relevant = prefers_theory_relevant,
   explicit_forall = explicit_forall}

fun remote_tptp_prover prover atp_prefix args config =
  tptp_prover (remotify (fst prover)) (remote_config atp_prefix args config)

val remote_e = remote_tptp_prover e "EP---" "" e_config
val remote_spass = remote_tptp_prover spass "SPASS---" "-x" spass_config
val remote_vampire = remote_tptp_prover vampire "Vampire---9" "" vampire_config

fun maybe_remote (name, _) ({home_var, ...} : prover_config) =
  name |> getenv home_var = "" ? remotify

fun default_atps_param_value () =
  space_implode " " [maybe_remote e e_config, maybe_remote spass spass_config,
                     remotify (fst vampire)]

val provers = [e, spass, vampire, remote_e, remote_spass, remote_vampire]
val prover_setup = fold add_prover provers

val setup =
  dest_dir_setup
  #> problem_prefix_setup
  #> measure_runtime_setup
  #> prover_setup

end;
