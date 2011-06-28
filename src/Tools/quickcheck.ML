(*  Title:      Tools/quickcheck.ML
    Author:     Stefan Berghofer, Florian Haftmann, Lukas Bulwahn, TU Muenchen

Generic counterexample search engine.
*)

signature QUICKCHECK =
sig
  val quickcheckN: string
  val genuineN: string
  val noneN: string
  val unknownN: string
  val setup: theory -> theory
  (* configuration *)
  val auto: bool Unsynchronized.ref
  val tester : string Config.T
  val size : int Config.T
  val iterations : int Config.T
  val no_assms : bool Config.T
  val report : bool Config.T
  val timing : bool Config.T
  val quiet : bool Config.T
  val timeout : real Config.T
  val finite_types : bool Config.T
  val finite_type_size : int Config.T
  datatype expectation = No_Expectation | No_Counterexample | Counterexample;
  datatype test_params = Test_Params of {default_type: typ list, expect : expectation};
  val test_params_of : Proof.context -> test_params
  val map_test_params : (typ list * expectation -> typ list * expectation)
    -> Context.generic -> Context.generic
  datatype report = Report of
    { iterations : int, raised_match_errors : int,
      satisfied_assms : int list, positive_concl_tests : int }
  (* quickcheck's result *)
  datatype result =
    Result of
     {counterexample : (string * term) list option,
      evaluation_terms : (term * term) list option,
      timings : (string * int) list,
      reports : (int * report) list}
  val empty_result : result
  val add_timing : (string * int) -> result Unsynchronized.ref -> unit
  val counterexample_of : result -> (string * term) list option
  val timings_of : result -> (string * int) list
  (* registering generators *)
  val add_generator:
    string * (Proof.context -> (term * term list) list -> int list -> term list option * report option)
      -> Context.generic -> Context.generic
  val add_tester:
    string * (Proof.context -> bool * bool -> (string * typ) list -> (term * term list) list -> result list)
      -> Context.generic -> Context.generic
  val add_batch_generator:
    string * (Proof.context -> term list -> (int -> term list option) list)
      -> Context.generic -> Context.generic
  val add_batch_validator:
    string * (Proof.context -> term list -> (int -> bool) list)
      -> Context.generic -> Context.generic
  (* basic operations *)
  val limit : Time.time -> (bool * bool) -> (unit -> 'a) -> (unit -> 'a) -> unit -> 'a  
  val instantiate_goals: Proof.context -> (string * typ) list -> (term * term list) list
    -> (typ option * (term * term list)) list list
  val collect_results: ('a -> result) -> 'a list -> result list -> result list
  (* testing terms and proof states *)
  val test_term: Proof.context -> bool * bool -> term * term list -> result
  val test_goal_terms:
    Proof.context -> bool * bool -> (string * typ) list -> (term * term list) list  
      -> result list
  val quickcheck: (string * string list) list -> int -> Proof.state -> (string * term) list option
  (* testing a batch of terms *)
  val test_terms:
    Proof.context -> term list -> (string * term) list option list option * (string * int) list
  val validate_terms: Proof.context -> term list -> bool list option * (string * int) list
end;

structure Quickcheck : QUICKCHECK =
struct

val quickcheckN = "quickcheck"
val quickcheck_paramsN = "quickcheck_params"

val genuineN = "genuine"
val noneN = "none"
val unknownN = "unknown"

(* preferences *)

val auto = Unsynchronized.ref false;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
  (Unsynchronized.setmp auto true (fn () =>
    Preferences.bool_pref auto
      "auto-quickcheck"
      "Run Quickcheck automatically.") ());

(* quickcheck report *)

datatype report = Report of
  { iterations : int, raised_match_errors : int,
    satisfied_assms : int list, positive_concl_tests : int }

(* Quickcheck Result *)

datatype result = Result of
  { counterexample : (string * term) list option, evaluation_terms : (term * term) list option,
    timings : (string * int) list, reports : (int * report) list}

val empty_result =
  Result {counterexample = NONE, evaluation_terms = NONE, timings = [], reports = []}

fun counterexample_of (Result r) = #counterexample r

fun found_counterexample (Result r) = is_some (#counterexample r)

fun response_of (Result r) = case (#counterexample r, #evaluation_terms r) of
    (SOME ts, SOME evals) => SOME (ts, evals)
  | (NONE, NONE) => NONE

fun timings_of (Result r) = #timings r

fun set_reponse names eval_terms (SOME ts) (Result r) =
  let
    val (ts1, ts2) = chop (length names) ts
  in
    Result {counterexample = SOME (names ~~ ts1), evaluation_terms = SOME (eval_terms ~~ ts2),
      timings = #timings r, reports = #reports r}
  end
  | set_reponse _ _ NONE result = result


fun set_counterexample counterexample (Result r) =
  Result {counterexample = counterexample,  evaluation_terms = #evaluation_terms r,
    timings = #timings r, reports = #reports r}

fun set_evaluation_terms evaluation_terms (Result r) =
  Result {counterexample = #counterexample r,  evaluation_terms = evaluation_terms,
    timings = #timings r, reports = #reports r}

fun cons_timing timing (Result r) =
  Result {counterexample = #counterexample r, evaluation_terms = #evaluation_terms r,
    timings = cons timing (#timings r), reports = #reports r}

fun cons_report size (SOME report) (Result r) =
  Result {counterexample = #counterexample r, evaluation_terms = #evaluation_terms r,
    timings = #timings r, reports = cons (size, report) (#reports r)}
  | cons_report _ NONE result = result

fun add_timing timing result_ref =
  Unsynchronized.change result_ref (cons_timing timing)

fun add_report size report result_ref =
  Unsynchronized.change result_ref (cons_report size report)

fun add_response names eval_terms response result_ref =
  Unsynchronized.change result_ref (set_reponse names eval_terms response)

(* expectation *)

datatype expectation = No_Expectation | No_Counterexample | Counterexample;

fun merge_expectation (expect1, expect2) =
  if expect1 = expect2 then expect1 else No_Expectation

(* quickcheck configuration -- default parameters, test generators *)
val tester = Attrib.setup_config_string @{binding quickcheck_tester} (K "")
val size = Attrib.setup_config_int @{binding quickcheck_size} (K 10)
val iterations = Attrib.setup_config_int @{binding quickcheck_iterations} (K 100)
val no_assms = Attrib.setup_config_bool @{binding quickcheck_no_assms} (K false)
val report = Attrib.setup_config_bool @{binding quickcheck_report} (K true)
val timing = Attrib.setup_config_bool @{binding quickcheck_timing} (K false)
val quiet = Attrib.setup_config_bool @{binding quickcheck_quiet} (K false)
val timeout = Attrib.setup_config_real @{binding quickcheck_timeout} (K 30.0)
val finite_types = Attrib.setup_config_bool @{binding quickcheck_finite_types} (K true)
val finite_type_size = Attrib.setup_config_int @{binding quickcheck_finite_type_size} (K 3)

datatype test_params = Test_Params of
  {default_type: typ list, expect : expectation};

fun dest_test_params (Test_Params {default_type, expect}) = (default_type, expect);

fun make_test_params (default_type, expect) =
  Test_Params {default_type = default_type, expect = expect};

fun map_test_params' f (Test_Params {default_type, expect}) =
  make_test_params (f (default_type, expect));

fun merge_test_params
  (Test_Params {default_type = default_type1, expect = expect1},
    Test_Params {default_type = default_type2, expect = expect2}) =
  make_test_params
    (merge (op =) (default_type1, default_type2), merge_expectation (expect1, expect2));

structure Data = Generic_Data
(
  type T =
    (((string * (Proof.context -> (term * term list) list -> int list -> term list option * report option)) list
      * (string * (Proof.context -> bool * bool -> (string * typ) list -> (term * term list) list -> result list)) list)
      * ((string * (Proof.context -> term list -> (int -> term list option) list)) list
      * ((string * (Proof.context -> term list -> (int -> bool) list)) list)))
      * test_params;
  val empty = ((([], []), ([], [])), Test_Params {default_type = [], expect = No_Expectation});
  val extend = I;
  fun merge ((((generators1, testers1), (batch_generators1, batch_validators1)), params1),
    (((generators2, testers2), (batch_generators2, batch_validators2)), params2)) : T =
    (((AList.merge (op =) (K true) (generators1, generators2),
       AList.merge (op =) (K true) (testers1, testers2)),
      (AList.merge (op =) (K true) (batch_generators1, batch_generators2),
       AList.merge (op =) (K true) (batch_validators1, batch_validators2))),
      merge_test_params (params1, params2));
);

val test_params_of = snd o Data.get o Context.Proof;

val default_type = fst o dest_test_params o test_params_of

val expect = snd o dest_test_params o test_params_of

val map_test_params = Data.map o apsnd o map_test_params'

val add_generator = Data.map o apfst o apfst o apfst o AList.update (op =);

val add_tester = Data.map o apfst o apfst o apsnd o AList.update (op =);

val add_batch_generator = Data.map o apfst o apsnd o apfst o AList.update (op =);

val add_batch_validator = Data.map o apfst o apsnd o apsnd o AList.update (op =);

(* generating tests *)

fun gen_mk_tester lookup ctxt v =
  let
    val name = Config.get ctxt tester
    val tester = case lookup ctxt name
      of NONE => error ("No such quickcheck tester: " ^ name)
      | SOME tester => tester ctxt;
  in
    if Config.get ctxt quiet then
      try tester v
    else
      let
        val tester = Exn.interruptible_capture tester v
      in case Exn.get_result tester of
          NONE => SOME (Exn.release tester)
        | SOME tester => SOME tester
      end
  end

val mk_tester =
  gen_mk_tester (fn ctxt => AList.lookup (op =) ((fst o fst o fst o Data.get o Context.Proof) ctxt))
val mk_batch_tester =
  gen_mk_tester (fn ctxt => AList.lookup (op =) ((fst o snd o fst o Data.get o Context.Proof) ctxt))
val mk_batch_validator =
  gen_mk_tester (fn ctxt => AList.lookup (op =) ((snd o snd o fst o Data.get o Context.Proof) ctxt))

  
fun lookup_tester ctxt = AList.lookup (op =) ((snd o fst o fst o Data.get o Context.Proof) ctxt)

(* testing propositions *)

fun check_test_term t =
  let
    val _ = (null (Term.add_tvars t []) andalso null (Term.add_tfrees t [])) orelse
      error "Term to be tested contains type variables";
    val _ = null (Term.add_vars t []) orelse
      error "Term to be tested contains schematic variables";
  in () end

fun cpu_time description e =
  let val ({cpu, ...}, result) = Timing.timing e ()
  in (result, (description, Time.toMilliseconds cpu)) end

fun limit timeout (limit_time, is_interactive) f exc () =
  if limit_time then
      TimeLimit.timeLimit timeout f ()
    handle TimeLimit.TimeOut =>
      if is_interactive then exc () else raise TimeLimit.TimeOut
  else
    f ()

fun test_term ctxt (limit_time, is_interactive) (t, eval_terms) =
  let
    fun message s = if Config.get ctxt quiet then () else Output.urgent_message s
    val _ = check_test_term t
    val names = Term.add_free_names t []
    val current_size = Unsynchronized.ref 0
    val current_result = Unsynchronized.ref empty_result 
    fun excipit () =
      "Quickcheck ran out of time while testing at size " ^ string_of_int (!current_size)
    fun with_size test_fun k =
      if k > Config.get ctxt size then
        NONE
      else
        let
          val _ = message ("Test data size: " ^ string_of_int k)
          val _ = current_size := k
          val ((result, report), timing) =
            cpu_time ("size " ^ string_of_int k) (fn () => test_fun [1, k - 1])
          val _ = add_timing timing current_result
          val _ = add_report k report current_result
        in
          case result of NONE => with_size test_fun (k + 1) | SOME q => SOME q
        end;
  in
    limit (seconds (Config.get ctxt timeout)) (limit_time, is_interactive) (fn () =>
      let
        val (test_fun, comp_time) = cpu_time "quickcheck compilation"
          (fn () => mk_tester ctxt [(t, eval_terms)]);
        val _ = add_timing comp_time current_result
      in
        case test_fun of NONE => !current_result
          | SOME test_fun =>
            let
              val (response, exec_time) =
                cpu_time "quickcheck execution" (fn () => with_size test_fun 1)
              val _ = add_response names eval_terms response current_result
              val _ = add_timing exec_time current_result
            in
              !current_result
            end
       end)
     (fn () => (message (excipit ()); !current_result)) ()
  end;

fun validate_terms ctxt ts =
  let
    val _ = map check_test_term ts
    val size = Config.get ctxt size
    val (test_funs, comp_time) = cpu_time "quickcheck batch compilation"
      (fn () => mk_batch_validator ctxt ts) 
    fun with_size tester k =
      if k > size then true
      else if tester k then with_size tester (k + 1) else false
    val (results, exec_time) = cpu_time "quickcheck batch execution" (fn () =>
        Option.map (map (fn test_fun => TimeLimit.timeLimit (seconds (Config.get ctxt timeout))
              (fn () => with_size test_fun 1) ()
             handle TimeLimit.TimeOut => true)) test_funs)
  in
    (results, [comp_time, exec_time])
  end
  
fun test_terms ctxt ts =
  let
    val _ = map check_test_term ts
    val size = Config.get ctxt size
    val namess = map (fn t => Term.add_free_names t []) ts
    val (test_funs, comp_time) = cpu_time "quickcheck batch compilation" (fn () => mk_batch_tester ctxt ts) 
    fun with_size tester k =
      if k > size then NONE
      else case tester k of SOME ts => SOME ts | NONE => with_size tester (k + 1)
    val (results, exec_time) = cpu_time "quickcheck batch execution" (fn () =>
        Option.map (map (fn test_fun => TimeLimit.timeLimit (seconds (Config.get ctxt timeout))
              (fn () => with_size test_fun 1) ()
             handle TimeLimit.TimeOut => NONE)) test_funs)
  in
    (Option.map (map2 (fn names => Option.map (fn ts => names ~~ ts)) namess) results,
      [comp_time, exec_time])
  end

(* FIXME: this function shows that many assumptions are made upon the generation *)
(* In the end there is probably no generic quickcheck interface left... *)

fun test_term_with_increasing_cardinality ctxt (limit_time, is_interactive) ts =
  let
    val thy = Proof_Context.theory_of ctxt
    fun message s = if Config.get ctxt quiet then () else Output.urgent_message s
    val (ts', eval_terms) = split_list ts
    val _ = map check_test_term ts'
    val names = Term.add_free_names (hd ts') []
    val Ts = map snd (Term.add_frees (hd ts') [])
    val current_result = Unsynchronized.ref empty_result
    fun test_card_size test_fun (card, size) =
      (* FIXME: why decrement size by one? *)
      let
        val (ts, timing) = cpu_time ("size " ^ string_of_int size ^ " and card " ^ string_of_int card)
          (fn () => fst (test_fun [card, size - 1]))
        val _ = add_timing timing current_result
      in
        Option.map (pair card) ts
      end
    val enumeration_card_size =
      if forall (fn T => Sign.of_sort thy (T,  ["Enum.enum"])) Ts then
        (* size does not matter *)
        map (rpair 0) (1 upto (length ts))
      else
        (* size does matter *)
        map_product pair (1 upto (length ts)) (1 upto (Config.get ctxt size))
        |> sort (fn ((c1, s1), (c2, s2)) => int_ord ((c1 + s1), (c2 + s2)))
  in
    limit (seconds (Config.get ctxt timeout)) (limit_time, is_interactive) (fn () =>
      let
        val (test_fun, comp_time) = cpu_time "quickcheck compilation" (fn () => mk_tester ctxt ts)
        val _ = add_timing comp_time current_result
      in
        case test_fun of
          NONE => !current_result
        | SOME test_fun =>
          let
            val _ = case get_first (test_card_size test_fun) enumeration_card_size of
              SOME (card, ts) => add_response names (nth eval_terms (card - 1)) (SOME ts) current_result
            | NONE => ()
          in !current_result end
      end)
      (fn () => (message "Quickcheck ran out of time"; !current_result)) ()
  end

fun get_finite_types ctxt =
  fst (chop (Config.get ctxt finite_type_size)
    (map (Type o rpair []) ["Enum.finite_1", "Enum.finite_2", "Enum.finite_3",
     "Enum.finite_4", "Enum.finite_5"]))

exception WELLSORTED of string

fun monomorphic_term thy insts default_T =
  let
    fun subst (T as TFree (v, S)) =
      let
        val T' = AList.lookup (op =) insts v
          |> the_default default_T
      in if Sign.of_sort thy (T', S) then T'
        else raise (WELLSORTED ("For instantiation with default_type " ^
          Syntax.string_of_typ_global thy default_T ^
          ":\n" ^ Syntax.string_of_typ_global thy T' ^
          " to be substituted for variable " ^
          Syntax.string_of_typ_global thy T ^ " does not have sort " ^
          Syntax.string_of_sort_global thy S))
      end
      | subst T = T;
  in (map_types o map_atyps) subst end;

datatype wellsorted_error = Wellsorted_Error of string | Term of term * term list

fun instantiate_goals lthy insts goals =
  let
    fun map_goal_and_eval_terms f (check_goal, eval_terms) = (f check_goal, map f eval_terms)
    val thy = Proof_Context.theory_of lthy
    val default_insts =
      if Config.get lthy finite_types then (get_finite_types lthy) else (default_type lthy)
    val inst_goals =
      map (fn (check_goal, eval_terms) =>
        if not (null (Term.add_tfree_names check_goal [])) then
          map (fn T =>
            (pair (SOME T) o Term o apfst (Object_Logic.atomize_term thy))
              (map_goal_and_eval_terms (monomorphic_term thy insts T) (check_goal, eval_terms))
              handle WELLSORTED s => (SOME T, Wellsorted_Error s)) default_insts
        else
          [(NONE, Term (Object_Logic.atomize_term thy check_goal, eval_terms))]) goals
    val error_msg =
      cat_lines
        (maps (map_filter (fn (_, Term t) => NONE | (_, Wellsorted_Error s) => SOME s)) inst_goals)
    fun is_wellsorted_term (T, Term t) = SOME (T, t)
      | is_wellsorted_term (_, Wellsorted_Error s) = NONE
    val correct_inst_goals =
      case map (map_filter is_wellsorted_term) inst_goals of
        [[]] => error error_msg
      | xs => xs
    val _ = if Config.get lthy quiet then () else warning error_msg
  in
    correct_inst_goals
  end

fun collect_results f [] results = results
  | collect_results f (t :: ts) results =
    let
      val result = f t
    in
      if found_counterexample result then
        (result :: results)
      else
        collect_results f ts (result :: results)
    end  

fun test_goal_terms ctxt (limit_time, is_interactive) insts goals =
  let
    fun test_term' goal =
      case goal of
        [(NONE, t)] => test_term ctxt (limit_time, is_interactive) t
      | ts => test_term_with_increasing_cardinality ctxt (limit_time, is_interactive) (map snd ts)
    val correct_inst_goals = instantiate_goals ctxt insts goals
  in
    case lookup_tester ctxt (Config.get ctxt tester) of
      SOME test_goal_terms => test_goal_terms ctxt (limit_time, is_interactive) insts goals
    | NONE =>
        if Config.get ctxt finite_types then
          collect_results test_term' correct_inst_goals []
        else
          collect_results (test_term ctxt (limit_time, is_interactive)) (maps (map snd) correct_inst_goals) []
  end;

fun test_goal (time_limit, is_interactive) (insts, eval_terms) i state =
  let
    val lthy = Proof.context_of state;
    val thy = Proof.theory_of state;
    fun strip (Const ("all", _) $ Abs (_, _, t)) = strip t
      | strip t = t;
    val {goal = st, ...} = Proof.raw_goal state;
    val (gi, frees) = Logic.goal_params (prop_of st) i;
    val some_locale = case (Option.map #target o Named_Target.peek) lthy
     of NONE => NONE
      | SOME "" => NONE
      | SOME locale => SOME locale;
    val assms = if Config.get lthy no_assms then [] else case some_locale
     of NONE => Assumption.all_assms_of lthy
      | SOME locale => Assumption.local_assms_of lthy (Locale.init locale thy);
    val proto_goal = Logic.list_implies (map Thm.term_of assms, subst_bounds (frees, strip gi));
    val goals = case some_locale
     of NONE => [(proto_goal, eval_terms)]
      | SOME locale =>
        map (fn (_, phi) => (Morphism.term phi proto_goal, map (Morphism.term phi) eval_terms))
          (Locale.registrations_of (Context.Theory thy) (*FIXME*) locale);
  in
    test_goal_terms lthy (time_limit, is_interactive) insts goals
  end

(* pretty printing *)

fun tool_name auto = (if auto then "Auto " else "") ^ "Quickcheck"

fun pretty_counterex ctxt auto NONE = Pretty.str (tool_name auto ^ " found no counterexample.")
  | pretty_counterex ctxt auto (SOME (cex, eval_terms)) =
      Pretty.chunks ((Pretty.str (tool_name auto ^ " found a counterexample:\n") ::
        map (fn (s, t) =>
          Pretty.block [Pretty.str (s ^ " ="), Pretty.brk 1, Syntax.pretty_term ctxt t]) (rev cex))
        @ (if null eval_terms then []
           else (Pretty.str ("Evaluated terms:\n") ::
             map (fn (t, u) =>
               Pretty.block [Syntax.pretty_term ctxt t, Pretty.str " =", Pretty.brk 1, Syntax.pretty_term ctxt u])
               (rev eval_terms))));

fun pretty_report (Report {iterations = iterations, raised_match_errors = raised_match_errors,
    satisfied_assms = satisfied_assms, positive_concl_tests = positive_concl_tests}) =
  let
    fun pretty_stat s i = Pretty.block ([Pretty.str (s ^ ": " ^ string_of_int i)])
  in
     ([pretty_stat "iterations" iterations,
     pretty_stat "match exceptions" raised_match_errors]
     @ map_index
       (fn (i, n) => pretty_stat ("satisfied " ^ string_of_int (i + 1) ^ ". assumption") n)
       satisfied_assms
     @ [pretty_stat "positive conclusion tests" positive_concl_tests])
  end

fun pretty_reports ctxt (SOME reports) =
  Pretty.chunks (Pretty.fbrk :: Pretty.str "Quickcheck report:" ::
    maps (fn (size, report) =>
      Pretty.str ("size " ^ string_of_int size ^ ":") :: pretty_report report @ [Pretty.brk 1])
      (rev reports))
  | pretty_reports ctxt NONE = Pretty.str ""

fun pretty_timings timings =
  Pretty.chunks (Pretty.fbrk :: Pretty.str "timings:" ::
    maps (fn (label, time) =>
      Pretty.str (label ^ ": " ^ string_of_int time ^ " ms") :: Pretty.brk 1 :: []) (rev timings))

fun pretty_counterex_and_reports ctxt auto [] =
    Pretty.chunks [Pretty.strs (tool_name auto ::
        space_explode " " "is used in a locale where no interpretation is provided."),
      Pretty.strs (space_explode " " "Please provide an executable interpretation for the locale.")]
  | pretty_counterex_and_reports ctxt auto (result :: _) =
    Pretty.chunks (pretty_counterex ctxt auto (response_of result) ::
      (* map (pretty_reports ctxt) (reports_of result) :: *)
      (if Config.get ctxt timing then cons (pretty_timings (timings_of result)) else I) [])

(* Isar commands *)

fun read_nat s = case (Library.read_int o Symbol.explode) s
 of (k, []) => if k >= 0 then k
      else error ("Not a natural number: " ^ s)
  | (_, _ :: _) => error ("Not a natural number: " ^ s);

fun read_bool "false" = false
  | read_bool "true" = true
  | read_bool s = error ("Not a Boolean value: " ^ s)

fun read_real s =
  case (Real.fromString s) of
    SOME s => s
  | NONE => error ("Not a real number: " ^ s)

fun read_expectation "no_expectation" = No_Expectation
  | read_expectation "no_counterexample" = No_Counterexample
  | read_expectation "counterexample" = Counterexample
  | read_expectation s = error ("Not an expectation value: " ^ s)

fun valid_tester_name genctxt name =
  AList.defined (op =) (fst (fst (fst (Data.get genctxt)))) name orelse
    AList.defined (op =) (snd (fst (fst (Data.get genctxt)))) name

fun parse_tester name genctxt =
  if valid_tester_name genctxt name then
    Config.put_generic tester name genctxt
  else
    error ("Unknown tester: " ^ name)

fun parse_test_param ("tester", [arg]) = parse_tester arg
  | parse_test_param ("size", [arg]) = Config.put_generic size (read_nat arg)
  | parse_test_param ("iterations", [arg]) = Config.put_generic iterations (read_nat arg)
  | parse_test_param ("default_type", arg) = (fn gen_ctxt =>
    map_test_params
      ((apfst o K) (map (Proof_Context.read_typ (Context.proof_of gen_ctxt)) arg)) gen_ctxt)
  | parse_test_param ("no_assms", [arg]) = Config.put_generic no_assms (read_bool arg)
  | parse_test_param ("expect", [arg]) = map_test_params ((apsnd o K) (read_expectation arg))
  | parse_test_param ("report", [arg]) = Config.put_generic report (read_bool arg)
  | parse_test_param ("quiet", [arg]) = Config.put_generic quiet (read_bool arg)
  | parse_test_param ("timeout", [arg]) = Config.put_generic timeout (read_real arg)
  | parse_test_param ("finite_types", [arg]) = Config.put_generic finite_types (read_bool arg)
  | parse_test_param ("finite_type_size", [arg]) =
    Config.put_generic finite_type_size (read_nat arg)
  | parse_test_param (name, _) = fn genctxt =>
    if valid_tester_name genctxt name then
      Config.put_generic tester name genctxt
    else error ("Unknown tester or test parameter: " ^ name);

fun parse_test_param_inst (name, arg) ((insts, eval_terms), ctxt) =
      case try (Proof_Context.read_typ ctxt) name
       of SOME (TFree (v, _)) =>
         ((AList.update (op =) (v, Proof_Context.read_typ ctxt (the_single arg)) insts, eval_terms), ctxt)
        | NONE => (case name of
            "eval" => ((insts, eval_terms @ map (Syntax.read_term ctxt) arg), ctxt)
          | _ => ((insts, eval_terms), Context.proof_map (parse_test_param (name, arg)) ctxt));

fun quickcheck_params_cmd args = Context.theory_map (fold parse_test_param args);

fun check_expectation state results =
  (if exists found_counterexample results andalso expect (Proof.context_of state) = No_Counterexample
  then
    error ("quickcheck expected to find no counterexample but found one")
  else
    (if not (exists found_counterexample results) andalso expect (Proof.context_of state) = Counterexample
    then
      error ("quickcheck expected to find a counterexample but did not find one")
    else ()))

fun gen_quickcheck args i state =
  state
  |> Proof.map_context_result (fn ctxt => fold parse_test_param_inst args (([], []), ctxt))
  |> (fn ((insts, eval_terms), state') => test_goal (true, true) (insts, eval_terms) i state'
  |> tap (check_expectation state'))

fun quickcheck args i state = counterexample_of (hd (gen_quickcheck args i state))

fun quickcheck_cmd args i state =
  gen_quickcheck args i (Toplevel.proof_of state)
  |> Output.urgent_message o Pretty.string_of
     o pretty_counterex_and_reports (Toplevel.context_of state) false;

val parse_arg =
  Parse.name --
    (Scan.optional (Parse.$$$ "=" |--
      (((Parse.name || Parse.float_number) >> single) ||
        (Parse.$$$ "[" |-- Parse.list1 Parse.name --| Parse.$$$ "]"))) ["true"]);

val parse_args =
  Parse.$$$ "[" |-- Parse.list1 parse_arg --| Parse.$$$ "]" || Scan.succeed [];

val _ =
  Outer_Syntax.command quickcheck_paramsN "set parameters for random testing" Keyword.thy_decl
    (parse_args >> (fn args => Toplevel.theory (quickcheck_params_cmd args)));

val _ =
  Outer_Syntax.improper_command quickcheckN "try to find counterexample for subgoal" Keyword.diag
    (parse_args -- Scan.optional Parse.nat 1
      >> (fn (args, i) => Toplevel.no_timing o Toplevel.keep (quickcheck_cmd args i)));

(* automatic testing *)

fun try_quickcheck auto state =
  let
    val ctxt = Proof.context_of state;
    val i = 1;
    val res =
      state
      |> Proof.map_context (Config.put report false #> Config.put quiet true)
      |> try (test_goal (false, false) ([], []) i);
  in
    case res of
      NONE => (unknownN, state)
    | SOME results =>
        let
          val msg = pretty_counterex_and_reports ctxt auto results
        in
          if exists found_counterexample results then
            (genuineN,
             state
             |> (if auto then
                   Proof.goal_message (K (Pretty.chunks [Pretty.str "",
                       Pretty.mark Markup.hilite msg]))
                 else
                   tap (fn _ => Output.urgent_message (Pretty.string_of msg))))
          else
            (noneN, state)
        end
  end
  |> `(fn (outcome_code, _) => outcome_code = genuineN)

val setup = Try.register_tool (quickcheckN, (20, auto, try_quickcheck))

end;

val auto_quickcheck = Quickcheck.auto;
