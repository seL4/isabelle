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
  val batch_tester : string Config.T
  val size : int Config.T
  val iterations : int Config.T
  val depth : int Config.T
  val no_assms : bool Config.T
  val report : bool Config.T
  val timing : bool Config.T
  val potential : bool Config.T
  val quiet : bool Config.T
  val timeout : real Config.T
  val allow_function_inversion : bool Config.T;
  val finite_types : bool Config.T
  val finite_type_size : int Config.T
  val set_active_testers: string list -> Context.generic -> Context.generic
  datatype expectation = No_Expectation | No_Counterexample | Counterexample;
  datatype test_params = Test_Params of {default_type: typ list, expect : expectation};
  val test_params_of : Proof.context -> test_params
  val map_test_params : (typ list * expectation -> typ list * expectation)
    -> Context.generic -> Context.generic
  val default_type : Proof.context -> typ list
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
  val found_counterexample : result -> bool
  val add_timing : (string * int) -> result Unsynchronized.ref -> unit
  val add_response : string list -> term list -> term list option -> result Unsynchronized.ref -> unit
  val add_report : int -> report option -> result Unsynchronized.ref -> unit
  val counterexample_of : result -> (string * term) list option
  val timings_of : result -> (string * int) list
  (* registering testers & generators *) 
  type tester =
    Proof.context -> bool -> (string * typ) list -> (term * term list) list -> result list
  val add_tester : string * (bool Config.T * tester) -> Context.generic -> Context.generic
  val add_batch_generator :
    string * (Proof.context -> term list -> (int -> term list option) list)
      -> Context.generic -> Context.generic
  val add_batch_validator :
    string * (Proof.context -> term list -> (int -> bool) list)
      -> Context.generic -> Context.generic
  (* basic operations *)
  val message : Proof.context -> string -> unit
  val limit : Time.time -> (bool * bool) -> (unit -> 'a) -> (unit -> 'a) -> unit -> 'a
  (* testing terms and proof states *)
  val mk_batch_validator : Proof.context -> term list -> (int -> bool) list option
  val mk_batch_tester : Proof.context -> term list -> (int -> term list option) list option
  val active_testers : Proof.context -> tester list
  val test_terms :
    Proof.context -> bool * bool -> (string * typ) list -> (term * term list) list -> result list option
  val quickcheck: (string * string list) list -> int -> Proof.state -> (string * term) list option
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

fun set_response names eval_terms (SOME ts) (Result r) =
  let
    val (ts1, ts2) = chop (length names) ts
    val (eval_terms', _) = chop (length ts2) eval_terms
  in
    Result {counterexample = SOME (names ~~ ts1), evaluation_terms = SOME (eval_terms' ~~ ts2),
      timings = #timings r, reports = #reports r}
  end
  | set_response _ _ NONE result = result


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
  Unsynchronized.change result_ref (set_response names eval_terms response)

(* expectation *)

datatype expectation = No_Expectation | No_Counterexample | Counterexample;

fun merge_expectation (expect1, expect2) =
  if expect1 = expect2 then expect1 else No_Expectation

(* quickcheck configuration -- default parameters, test generators *)
val batch_tester = Attrib.setup_config_string @{binding quickcheck_batch_tester} (K "")
val size = Attrib.setup_config_int @{binding quickcheck_size} (K 10)
val iterations = Attrib.setup_config_int @{binding quickcheck_iterations} (K 100)
val depth = Attrib.setup_config_int @{binding quickcheck_depth} (K 10)

val no_assms = Attrib.setup_config_bool @{binding quickcheck_no_assms} (K false)
val report = Attrib.setup_config_bool @{binding quickcheck_report} (K true)
val timing = Attrib.setup_config_bool @{binding quickcheck_timing} (K false)
val potential = Attrib.setup_config_bool @{binding quickcheck_potential} (K true)
val quiet = Attrib.setup_config_bool @{binding quickcheck_quiet} (K false)
val timeout = Attrib.setup_config_real @{binding quickcheck_timeout} (K 30.0)
val allow_function_inversion =
  Attrib.setup_config_bool @{binding quickcheck_allow_function_inversion} (K false)
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

type tester =
  Proof.context -> bool -> (string * typ) list -> (term * term list) list -> result list

structure Data = Generic_Data
(
  type T =
    ((string * (bool Config.T * tester)) list
      * ((string * (Proof.context -> term list -> (int -> term list option) list)) list
      * ((string * (Proof.context -> term list -> (int -> bool) list)) list)))
      * test_params;
  val empty = (([], ([], [])), Test_Params {default_type = [], expect = No_Expectation});
  val extend = I;
  fun merge (((testers1, (batch_generators1, batch_validators1)), params1),
    ((testers2, (batch_generators2, batch_validators2)), params2)) : T =
    ((AList.merge (op =) (K true) (testers1, testers2),
      (AList.merge (op =) (K true) (batch_generators1, batch_generators2),
       AList.merge (op =) (K true) (batch_validators1, batch_validators2))),
      merge_test_params (params1, params2));
);

val test_params_of = snd o Data.get o Context.Proof;

val default_type = fst o dest_test_params o test_params_of

val expect = snd o dest_test_params o test_params_of

val map_test_params = Data.map o apsnd o map_test_params'

val add_tester = Data.map o apfst o apfst o AList.update (op =);

val add_batch_generator = Data.map o apfst o apsnd o apfst o AList.update (op =);

val add_batch_validator = Data.map o apfst o apsnd o apsnd o AList.update (op =);

fun active_testers ctxt =
  let
    val testers = (map snd o fst o fst o Data.get o Context.Proof) ctxt
  in
    map snd (filter (fn (active, _) => Config.get ctxt active) testers)
  end
  
fun set_active_testers [] gen_ctxt = gen_ctxt
  | set_active_testers testers gen_ctxt =
  let
    val registered_testers = (fst o fst o Data.get) gen_ctxt
  in
    fold (fn (name, (config, _)) => Config.put_generic config (member (op =) testers name))
      registered_testers gen_ctxt
  end
    
(* generating tests *)

fun gen_mk_tester lookup ctxt v =
  let
    val name = Config.get ctxt batch_tester
    val tester = case lookup ctxt name
      of NONE => error ("No such quickcheck batch-tester: " ^ name)
      | SOME tester => tester ctxt;
  in
    if Config.get ctxt quiet then
      try tester v
    else
      let (* FIXME !?!? *)
        val tester = Exn.interruptible_capture tester v
      in case Exn.get_res tester of
          NONE => SOME (Exn.release tester)
        | SOME tester => SOME tester
      end
  end

val mk_batch_tester =
  gen_mk_tester (fn ctxt => AList.lookup (op =) ((fst o snd o fst o Data.get o Context.Proof) ctxt))
val mk_batch_validator =
  gen_mk_tester (fn ctxt => AList.lookup (op =) ((snd o snd o fst o Data.get o Context.Proof) ctxt))
  
fun lookup_tester ctxt = AList.lookup (op =) ((fst o fst o Data.get o Context.Proof) ctxt)

(* testing propositions *)

type compile_generator =
  Proof.context -> (term * term list) list -> int list -> term list option * report option

fun limit timeout (limit_time, is_interactive) f exc () =
  if limit_time then
      TimeLimit.timeLimit timeout f ()
    handle TimeLimit.TimeOut =>
      if is_interactive then exc () else raise TimeLimit.TimeOut
  else
    f ()

fun message ctxt s = if Config.get ctxt quiet then () else Output.urgent_message s
  
fun test_terms ctxt (limit_time, is_interactive) insts goals =
  case active_testers ctxt of
    [] => error "No active testers for quickcheck"
  | testers => limit (seconds (Config.get ctxt timeout)) (limit_time, is_interactive)
      (fn () => Par_List.get_some (fn tester =>
      tester ctxt (length testers > 1) insts goals |>
      (fn result => if exists found_counterexample result then SOME result else NONE)) testers)
      (fn () => (message ctxt "Quickcheck ran out of time"; NONE)) ();
      
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
    test_terms lthy (time_limit, is_interactive) insts goals
  end

(* pretty printing *)

fun tool_name auto = (if auto then "Auto " else "") ^ "Quickcheck"

fun pretty_counterex ctxt auto NONE = Pretty.str (tool_name auto ^ " found no counterexample.")
  | pretty_counterex ctxt auto (SOME (cex, eval_terms)) =
      Pretty.chunks ((Pretty.str (tool_name auto ^ " found a counterexample:\n") ::
        map (fn (s, t) =>
          Pretty.block [Pretty.str (s ^ " ="), Pretty.brk 1, Syntax.pretty_term ctxt t]) (rev cex))
        @ (if null eval_terms then []
           else (Pretty.fbrk :: Pretty.str ("Evaluated terms:") ::
             map (fn (t, u) =>
               Pretty.block [Syntax.pretty_term ctxt t, Pretty.str " =", Pretty.brk 1,
                 Syntax.pretty_term ctxt u]) (rev eval_terms))));

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

fun valid_tester_name genctxt name = AList.defined (op =) (fst (fst (Data.get genctxt))) name
  
fun parse_tester name (testers, genctxt) =
  if valid_tester_name genctxt name then
    (insert (op =) name testers, genctxt)  
  else
    error ("Unknown tester: " ^ name)

fun parse_test_param ("tester", args) = fold parse_tester args
  | parse_test_param ("size", [arg]) = apsnd (Config.put_generic size (read_nat arg))
  | parse_test_param ("iterations", [arg]) = apsnd (Config.put_generic iterations (read_nat arg))
  | parse_test_param ("depth", [arg]) = apsnd (Config.put_generic depth (read_nat arg))  
  | parse_test_param ("default_type", arg) = (fn (testers, gen_ctxt) =>
    (testers, map_test_params
      ((apfst o K) (map (Proof_Context.read_typ (Context.proof_of gen_ctxt)) arg)) gen_ctxt))
  | parse_test_param ("no_assms", [arg]) = apsnd (Config.put_generic no_assms (read_bool arg))
  | parse_test_param ("expect", [arg]) = apsnd (map_test_params ((apsnd o K) (read_expectation arg)))
  | parse_test_param ("report", [arg]) = apsnd (Config.put_generic report (read_bool arg))
  | parse_test_param ("quiet", [arg]) = apsnd (Config.put_generic quiet (read_bool arg))
  | parse_test_param ("timeout", [arg]) = apsnd (Config.put_generic timeout (read_real arg))
  | parse_test_param ("finite_types", [arg]) = apsnd (Config.put_generic finite_types (read_bool arg))
  | parse_test_param ("allow_function_inversion", [arg]) =
      apsnd (Config.put_generic allow_function_inversion (read_bool arg))
  | parse_test_param ("finite_type_size", [arg]) =
    apsnd (Config.put_generic finite_type_size (read_nat arg))
  | parse_test_param (name, _) = (fn (testers, genctxt) =>
    if valid_tester_name genctxt name then
      (insert (op =) name testers, genctxt)  
    else error ("Unknown tester or test parameter: " ^ name));

fun proof_map_result f = apsnd Context.the_proof o f o Context.Proof;

fun parse_test_param_inst (name, arg) ((insts, eval_terms), (testers, ctxt)) =
      case try (Proof_Context.read_typ ctxt) name
       of SOME (TFree (v, _)) =>
         ((AList.update (op =) (v, Proof_Context.read_typ ctxt (the_single arg)) insts, eval_terms),
           (testers, ctxt))
        | NONE => (case name of
            "eval" => ((insts, eval_terms @ map (Syntax.read_term ctxt) arg), (testers, ctxt))
          | _ => ((insts, eval_terms),
            proof_map_result (fn gen_ctxt => parse_test_param (name, arg) (testers, gen_ctxt)) ctxt));

fun quickcheck_params_cmd args = Context.theory_map
  (fn gen_ctxt => uncurry set_active_testers (fold parse_test_param args ([], gen_ctxt)));

fun check_expectation state results =
  (if is_some results andalso expect (Proof.context_of state) = No_Counterexample
  then
    error ("quickcheck expected to find no counterexample but found one")
  else
    (if is_none results andalso expect (Proof.context_of state) = Counterexample
    then
      error ("quickcheck expected to find a counterexample but did not find one")
    else ()))

fun gen_quickcheck args i state =
  state
  |> Proof.map_context_result (fn ctxt =>
    apsnd (fn (testers, ctxt) => Context.proof_map (set_active_testers testers) ctxt)
      (fold parse_test_param_inst args (([], []), ([], ctxt))))
  |> (fn ((insts, eval_terms), state') => test_goal (true, true) (insts, eval_terms) i state'
  |> tap (check_expectation state'))

fun quickcheck args i state =
  Option.map (the o get_first counterexample_of) (gen_quickcheck args i state)

fun quickcheck_cmd args i state =
  gen_quickcheck args i (Toplevel.proof_of state)
  |> Option.map (the o get_first response_of)
  |> Output.urgent_message o Pretty.string_of
     o pretty_counterex (Toplevel.context_of state) false;

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
          val msg = pretty_counterex ctxt auto (Option.map (the o get_first response_of) results)
        in
          if is_some results then
            (genuineN,
             state
             |> (if auto then
                   Proof.goal_message (K (Pretty.chunks [Pretty.str "",
                       Pretty.mark Isabelle_Markup.hilite msg]))
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
