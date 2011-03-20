(*  Title:      Tools/quickcheck.ML
    Author:     Stefan Berghofer, Florian Haftmann, Lukas Bulwahn, TU Muenchen

Generic counterexample search engine.
*)

signature QUICKCHECK =
sig
  val setup: theory -> theory
  (* configuration *)
  val auto: bool Unsynchronized.ref
  val timing : bool Unsynchronized.ref
  val tester : string Config.T
  val size : int Config.T
  val iterations : int Config.T
  val no_assms : bool Config.T
  val report : bool Config.T
  val quiet : bool Config.T
  val timeout : real Config.T
  val finite_types : bool Config.T
  val finite_type_size : int Config.T
  datatype report = Report of
    { iterations : int, raised_match_errors : int,
      satisfied_assms : int list, positive_concl_tests : int }
  datatype expectation = No_Expectation | No_Counterexample | Counterexample;
  datatype test_params = Test_Params of {default_type: typ list, expect : expectation};
  val test_params_of : Proof.context -> test_params
  val map_test_params : (typ list * expectation -> typ list * expectation)
    -> Context.generic -> Context.generic
  val add_generator:
    string * (Proof.context -> term -> int -> term list option * report option)
      -> Context.generic -> Context.generic
  val add_batch_generator:
    string * (Proof.context -> term list -> (int -> term list option) list)
      -> Context.generic -> Context.generic
  (* testing terms and proof states *)
  val test_term: Proof.context -> bool * bool -> term ->
    (string * term) list option * ((string * int) list * ((int * report) list) option)
  val test_goal_terms:
    Proof.context -> bool * bool -> (string * typ) list -> term list
      -> (string * term) list option * ((string * int) list * ((int * report) list) option) list
  val quickcheck: (string * string list) list -> int -> Proof.state -> (string * term) list option
  (* testing a batch of terms *)
  val test_terms: Proof.context -> term list -> (string * term) list option list option
end;

structure Quickcheck : QUICKCHECK =
struct

(* preferences *)

val auto = Unsynchronized.ref false;

val timing = Unsynchronized.ref false;

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

(* expectation *)

datatype expectation = No_Expectation | No_Counterexample | Counterexample;

fun merge_expectation (expect1, expect2) =
  if expect1 = expect2 then expect1 else No_Expectation

(* quickcheck configuration -- default parameters, test generators *)
val (tester, setup_tester) = Attrib.config_string "quickcheck_tester" (K "")
val (size, setup_size) = Attrib.config_int "quickcheck_size" (K 10)
val (iterations, setup_iterations) = Attrib.config_int "quickcheck_iterations" (K 100)
val (no_assms, setup_no_assms) = Attrib.config_bool "quickcheck_no_assms" (K false)
val (report, setup_report) = Attrib.config_bool "quickcheck_report" (K true)
val (quiet, setup_quiet) = Attrib.config_bool "quickcheck_quiet" (K false)
val (timeout, setup_timeout) = Attrib.config_real "quickcheck_timeout" (K 30.0)
val (finite_types, setup_finite_types) = Attrib.config_bool "quickcheck_finite_types" (K true)
val (finite_type_size, setup_finite_type_size) =
  Attrib.config_int "quickcheck_finite_type_size" (K 3)

val setup_config =
  setup_tester #> setup_size #> setup_iterations #> setup_no_assms #> setup_report #> setup_quiet
    #> setup_timeout #> setup_finite_types #> setup_finite_type_size

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
    ((string * (Proof.context -> term -> int -> term list option * report option)) list
      * (string * (Proof.context -> term list -> (int -> term list option) list)) list)
      * test_params;
  val empty = (([], []), Test_Params {default_type = [], expect = No_Expectation});
  val extend = I;
  fun merge (((generators1, batch_generators1), params1), ((generators2, batch_generators2), params2)) : T =
    ((AList.merge (op =) (K true) (generators1, generators2),
    AList.merge (op =) (K true) (batch_generators1, batch_generators2)),
      merge_test_params (params1, params2));
);

val test_params_of = snd o Data.get o Context.Proof;

val default_type = fst o dest_test_params o test_params_of

val expect = snd o dest_test_params o test_params_of

val map_test_params = Data.map o apsnd o map_test_params'

val add_generator = Data.map o apfst o apfst o AList.update (op =);

val add_batch_generator = Data.map o apfst o apsnd o AList.update (op =);

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

val mk_tester = gen_mk_tester (fn ctxt =>
  AList.lookup (op =) ((fst o fst o Data.get o Context.Proof) ctxt))
val mk_batch_tester = gen_mk_tester (fn ctxt => AList.lookup (op =) ((snd o fst o Data.get o Context.Proof) ctxt))
  
(* testing propositions *)

fun prep_test_term t =
  let
    val _ = (null (Term.add_tvars t []) andalso null (Term.add_tfrees t [])) orelse
      error "Term to be tested contains type variables";
    val _ = null (Term.add_vars t []) orelse
      error "Term to be tested contains schematic variables";
    val frees = Term.add_frees t [];
  in (frees, list_abs_free (frees, t)) end

fun cpu_time description f =  (* FIXME !? *)
  let
    val start = Timing.start ()
    val result = Exn.capture f ()
    val time = Time.toMilliseconds (#cpu (Timing.result start))
  in (Exn.release result, (description, time)) end

fun limit ctxt (limit_time, is_interactive) f exc () =
  if limit_time then
      TimeLimit.timeLimit (seconds (Config.get ctxt timeout)) f ()
    handle TimeLimit.TimeOut =>
      if is_interactive then exc () else raise TimeLimit.TimeOut
  else
    f ()

fun test_term ctxt (limit_time, is_interactive) t =
  let
    val (names, t') = apfst (map fst) (prep_test_term t);
    val current_size = Unsynchronized.ref 0
    fun excipit s =
      "Quickcheck " ^ s ^ " while testing at size " ^ string_of_int (!current_size)
    val (test_fun, comp_time) = cpu_time "quickcheck compilation" (fn () => mk_tester ctxt t');
    fun with_size test_fun k reports =
      if k > Config.get ctxt size then
        (NONE, reports)
      else
        let
          val _ = if Config.get ctxt quiet then () else Output.urgent_message
            ("Test data size: " ^ string_of_int k)
          val _ = current_size := k
          val ((result, new_report), timing) =
            cpu_time ("size " ^ string_of_int k) (fn () => test_fun (k - 1))
          val reports = case new_report of NONE => reports | SOME rep => (k, rep) :: reports
        in
          case result of NONE => with_size test_fun (k + 1) reports | SOME q => (SOME q, reports)
        end;
  in
    case test_fun of NONE => (NONE, ([comp_time], NONE))
      | SOME test_fun =>
        limit ctxt (limit_time, is_interactive) (fn () =>
          let
            val ((result, reports), exec_time) =
              cpu_time "quickcheck execution" (fn () => with_size test_fun 1 [])
          in
            (case result of NONE => NONE | SOME ts => SOME (names ~~ ts),
              ([exec_time, comp_time],
               if Config.get ctxt report andalso not (null reports) then SOME reports else NONE))
          end) (fn () => error (excipit "ran out of time")) ()
  end;

fun test_terms ctxt ts =
  let
    val (namess, ts') = split_list (map (fn t => apfst (map fst) (prep_test_term t)) ts)
    val test_funs = mk_batch_tester ctxt ts'
    fun with_size tester k =
      if k > Config.get ctxt size then NONE
      else case tester k of SOME ts => SOME ts | NONE => with_size tester (k + 1)
    val results =
      Option.map (map (fn test_fun => TimeLimit.timeLimit (seconds (Config.get ctxt timeout))
            (fn () => with_size test_fun 1)  ()
           handle TimeLimit.TimeOut => NONE)) test_funs
  in
    Option.map (map2 (fn names => Option.map (fn ts => names ~~ ts)) namess) results
  end

(* FIXME: this function shows that many assumptions are made upon the generation *)
(* In the end there is probably no generic quickcheck interface left... *)

fun test_term_with_increasing_cardinality ctxt (limit_time, is_interactive) ts =
  let
    val thy = ProofContext.theory_of ctxt
    val (freess, ts') = split_list (map prep_test_term ts)
    val Ts = map snd (hd freess)
    val (test_funs, comp_time) = cpu_time "quickcheck compilation"
      (fn () => map (mk_tester ctxt) ts')
    fun test_card_size (card, size) =
      (* FIXME: why decrement size by one? *)
      case fst (the (nth test_funs (card - 1)) (size - 1)) of
        SOME ts => SOME (map fst (nth freess (card - 1)) ~~ ts)
      | NONE => NONE
    val enumeration_card_size =
      if forall (fn T => Sign.of_sort thy (T,  ["Enum.enum"])) Ts then
        (* size does not matter *)
        map (rpair 0) (1 upto (length ts))
      else
        (* size does matter *)
        map_product pair (1 upto (length ts)) (1 upto (Config.get ctxt size))
        |> sort (fn ((c1, s1), (c2, s2)) => int_ord ((c1 + s1), (c2 + s2)))
    in
      if (forall is_none test_funs) then
        (NONE, ([comp_time], NONE))
      else if (forall is_some test_funs) then
        limit ctxt (limit_time, is_interactive) (fn () =>
          (get_first test_card_size enumeration_card_size, ([comp_time], NONE)))
          (fn () => error "Quickcheck ran out of time") ()
      else
        error "Unexpectedly, testers of some cardinalities are executable but others are not"
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

datatype wellsorted_error = Wellsorted_Error of string | Term of term

fun test_goal_terms lthy (limit_time, is_interactive) insts check_goals =
  let
    val thy = ProofContext.theory_of lthy
    val default_insts =
      if Config.get lthy finite_types then (get_finite_types lthy) else (default_type lthy)
    val inst_goals =
      map (fn check_goal =>
        if not (null (Term.add_tfree_names check_goal [])) then
          map (fn T =>
            (pair (SOME T) o Term o Object_Logic.atomize_term thy o monomorphic_term thy insts T)
              check_goal
              handle WELLSORTED s => (SOME T, Wellsorted_Error s)) default_insts
        else
          [(NONE, Term (Object_Logic.atomize_term thy check_goal))]) check_goals
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
    fun collect_results f reports [] = (NONE, rev reports)
      | collect_results f reports (t :: ts) =
        case f t of
          (SOME res, report) => (SOME res, rev (report :: reports))
        | (NONE, report) => collect_results f (report :: reports) ts
    fun test_term' goal =
      case goal of
        [(NONE, t)] => test_term lthy (limit_time, is_interactive) t
      | ts => test_term_with_increasing_cardinality lthy (limit_time, is_interactive) (map snd ts)
  in
    if Config.get lthy finite_types then
      collect_results test_term' [] correct_inst_goals
    else
      collect_results (test_term lthy (limit_time, is_interactive)) [] (maps (map snd) correct_inst_goals)
  end;

fun test_goal (time_limit, is_interactive) insts i state =
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
    val check_goals = case some_locale
     of NONE => [proto_goal]
      | SOME locale => map (fn (_, phi) => Morphism.term phi proto_goal)
        (Locale.registrations_of (Context.Theory thy) (*FIXME*) locale);
  in
    test_goal_terms lthy (time_limit, is_interactive) insts check_goals
  end

(* pretty printing *)

fun tool_name auto = (if auto then "Auto " else "") ^ "Quickcheck"

fun pretty_counterex ctxt auto NONE = Pretty.str (tool_name auto ^ " found no counterexample.")
  | pretty_counterex ctxt auto (SOME cex) =
      Pretty.chunks (Pretty.str (tool_name auto ^ " found a counterexample:\n") ::
        map (fn (s, t) =>
          Pretty.block [Pretty.str (s ^ " ="), Pretty.brk 1, Syntax.pretty_term ctxt t]) (rev cex));

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

fun pretty_counterex_and_reports ctxt auto (cex, timing_and_reports) =
  Pretty.chunks (pretty_counterex ctxt auto cex ::
    map (pretty_reports ctxt) (map snd timing_and_reports))

(* automatic testing *)

fun auto_quickcheck state =
  let
    val ctxt = Proof.context_of state;
    val res =
      state
      |> Proof.map_context (Config.put report false #> Config.put quiet true)
      |> try (test_goal (false, false) [] 1);
  in
    case res of
      NONE => (false, state)
    | SOME (NONE, report) => (false, state)
    | SOME (cex, report) => (true, Proof.goal_message (K (Pretty.chunks [Pretty.str "",
        Pretty.mark Markup.hilite (pretty_counterex ctxt true cex)])) state)
  end

val setup = Auto_Tools.register_tool (auto, auto_quickcheck)
  #> setup_config

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

fun valid_tester_name genctxt = AList.defined (op =) (fst (fst (Data.get genctxt)))

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
      ((apfst o K) (map (ProofContext.read_typ (Context.proof_of gen_ctxt)) arg)) gen_ctxt)
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

fun parse_test_param_inst (name, arg) (insts, ctxt) =
      case try (ProofContext.read_typ ctxt) name
       of SOME (TFree (v, _)) => (apfst o AList.update (op =))
              (v, ProofContext.read_typ ctxt (the_single arg)) (insts, ctxt)
        | _ => (apsnd o Context.proof_map o parse_test_param) (name, arg) (insts, ctxt);

fun quickcheck_params_cmd args = Context.theory_map (fold parse_test_param args);

fun gen_quickcheck args i state =
  state
  |> Proof.map_context_result (fn ctxt => fold parse_test_param_inst args ([], ctxt))
  |> (fn (insts, state') => test_goal (true, true) insts i state'
  |> tap (fn (SOME x, _) => if expect (Proof.context_of state') = No_Counterexample then
               error ("quickcheck expected to find no counterexample but found one") else ()
           | (NONE, _) => if expect (Proof.context_of state') = Counterexample then
               error ("quickcheck expected to find a counterexample but did not find one") else ()))

fun quickcheck args i state = fst (gen_quickcheck args i state);

fun quickcheck_cmd args i state =
  gen_quickcheck args i (Toplevel.proof_of state)
  |> Pretty.writeln o pretty_counterex_and_reports (Toplevel.context_of state) false;

val parse_arg =
  Parse.name --
    (Scan.optional (Parse.$$$ "=" |--
      (((Parse.name || Parse.float_number) >> single) ||
        (Parse.$$$ "[" |-- Parse.list1 Parse.name --| Parse.$$$ "]"))) ["true"]);

val parse_args =
  Parse.$$$ "[" |-- Parse.list1 parse_arg --| Parse.$$$ "]" || Scan.succeed [];

val _ =
  Outer_Syntax.command "quickcheck_params" "set parameters for random testing" Keyword.thy_decl
    (parse_args >> (fn args => Toplevel.theory (quickcheck_params_cmd args)));

val _ =
  Outer_Syntax.improper_command "quickcheck" "try to find counterexample for subgoal" Keyword.diag
    (parse_args -- Scan.optional Parse.nat 1
      >> (fn (args, i) => Toplevel.no_timing o Toplevel.keep (quickcheck_cmd args i)));

end;


val auto_quickcheck = Quickcheck.auto;
