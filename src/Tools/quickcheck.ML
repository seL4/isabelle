(*  Title:      Tools/quickcheck.ML
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen

Generic counterexample search engine.
*)

signature QUICKCHECK =
sig
  val auto: bool Unsynchronized.ref
  val timing : bool Unsynchronized.ref
  datatype report = Report of
    { iterations : int, raised_match_errors : int,
      satisfied_assms : int list, positive_concl_tests : int }
  val gen_test_term: Proof.context -> bool -> bool -> string option -> int -> int -> term ->
    (string * term) list option * ((string * int) list * ((int * report list) list) option)
  val test_term: Proof.context -> bool -> string option -> int -> int -> term ->
    (string * term) list option
  val add_generator:
    string * (Proof.context -> bool -> term -> int -> term list option * (bool list * bool))
      -> theory -> theory
  val setup: theory -> theory
  val quickcheck: (string * string) list -> int -> Proof.state -> (string * term) list option
end;

structure Quickcheck : QUICKCHECK =
struct

(* preferences *)

val auto = Unsynchronized.ref false;

val timing = Unsynchronized.ref false;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
  (setmp_CRITICAL auto true (fn () =>
    Preferences.bool_pref auto
      "auto-quickcheck"
      "Whether to run Quickcheck automatically.") ());

(* quickcheck report *)

datatype single_report = Run of bool list * bool | MatchExc

datatype report = Report of
  { iterations : int, raised_match_errors : int,
    satisfied_assms : int list, positive_concl_tests : int }

fun collect_single_report single_report
    (Report {iterations = iterations, raised_match_errors = raised_match_errors,
    satisfied_assms = satisfied_assms, positive_concl_tests = positive_concl_tests}) =
  case single_report
  of MatchExc =>
    Report {iterations = iterations + 1, raised_match_errors = raised_match_errors + 1,
      satisfied_assms = satisfied_assms, positive_concl_tests = positive_concl_tests}
   | Run (assms, concl) =>
    Report {iterations = iterations + 1, raised_match_errors = raised_match_errors,
      satisfied_assms =
        map2 (fn b => fn s => if b then s + 1 else s) assms
         (if null satisfied_assms then replicate (length assms) 0 else satisfied_assms),
      positive_concl_tests = if concl then positive_concl_tests + 1 else positive_concl_tests}

(* quickcheck configuration -- default parameters, test generators *)

datatype test_params = Test_Params of
  { size: int, iterations: int, default_type: typ option, no_assms: bool, report: bool, quiet : bool};

fun dest_test_params (Test_Params { size, iterations, default_type, no_assms, report, quiet }) =
  ((size, iterations), ((default_type, no_assms), (report, quiet)));
fun make_test_params ((size, iterations), ((default_type, no_assms), (report, quiet))) =
  Test_Params { size = size, iterations = iterations, default_type = default_type,
                no_assms = no_assms, report = report, quiet = quiet };
fun map_test_params f (Test_Params { size, iterations, default_type, no_assms, report, quiet }) =
  make_test_params (f ((size, iterations), ((default_type, no_assms), (report, quiet))));
fun merge_test_params (Test_Params { size = size1, iterations = iterations1, default_type = default_type1,
                                     no_assms = no_assms1, report = report1, quiet = quiet1 },
  Test_Params { size = size2, iterations = iterations2, default_type = default_type2,
                no_assms = no_assms2, report = report2, quiet = quiet2 }) =
  make_test_params ((Int.max (size1, size2), Int.max (iterations1, iterations2)),
    ((case default_type1 of NONE => default_type2 | _ => default_type1, no_assms1 orelse no_assms2),
    (report1 orelse report2, quiet1 orelse quiet2)));

structure Data = Theory_Data
(
  type T = (string * (Proof.context -> bool -> term -> int -> term list option * (bool list * bool))) list
    * test_params;
  val empty = ([], Test_Params
    { size = 10, iterations = 100, default_type = NONE, no_assms = false, report = false, quiet = false});
  val extend = I;
  fun merge ((generators1, params1), (generators2, params2)) : T =
    (AList.merge (op =) (K true) (generators1, generators2),
      merge_test_params (params1, params2));
);

val add_generator = Data.map o apfst o AList.update (op =);

(* generating tests *)

fun mk_tester_select name ctxt =
  case AList.lookup (op =) ((fst o Data.get o ProofContext.theory_of) ctxt) name
   of NONE => error ("No such quickcheck generator: " ^ name)
    | SOME generator => generator ctxt;

fun mk_testers ctxt report t =
  (map snd o fst o Data.get o ProofContext.theory_of) ctxt
  |> map_filter (fn generator => try (generator ctxt report) t);

fun mk_testers_strict ctxt report t =
  let
    val generators = ((map snd o fst o Data.get o ProofContext.theory_of) ctxt)
    val testers = map (fn generator => Exn.capture (generator ctxt report) t) generators;
  in if forall (is_none o Exn.get_result) testers
    then [(Exn.release o snd o split_last) testers]
    else map_filter Exn.get_result testers
  end;


(* testing propositions *)

fun prep_test_term t =
  let
    val _ = (null (Term.add_tvars t []) andalso null (Term.add_tfrees t [])) orelse
      error "Term to be tested contains type variables";
    val _ = null (Term.add_vars t []) orelse
      error "Term to be tested contains schematic variables";
    val frees = Term.add_frees t [];
  in (map fst frees, list_abs_free (frees, t)) end

fun cpu_time description f =
  let
    val start = start_timing ()
    val result = Exn.capture f ()
    val time = Time.toMilliseconds (#cpu (end_timing start))
  in (Exn.release result, (description, time)) end

fun gen_test_term ctxt quiet report generator_name size i t =
  let
    val (names, t') = prep_test_term t;
    val (testers, comp_time) = cpu_time "quickcheck compilation"
      (fn () => (case generator_name
       of NONE => if quiet then mk_testers ctxt report t' else mk_testers_strict ctxt report t'
        | SOME name => [mk_tester_select name ctxt report t']));
    fun iterate f 0 report = (NONE, report)
      | iterate f j report =
        let
          val (test_result, single_report) = apsnd Run (f ()) handle Match => (if quiet then ()
             else warning "Exception Match raised during quickcheck"; (NONE, MatchExc))
          val report = collect_single_report single_report report
        in
          case test_result of NONE => iterate f (j - 1) report | SOME q => (SOME q, report)
        end
    val empty_report = Report { iterations = 0, raised_match_errors = 0,
      satisfied_assms = [], positive_concl_tests = 0 }
    fun with_testers k [] = (NONE, [])
      | with_testers k (tester :: testers) =
          case iterate (fn () => tester (k - 1)) i empty_report
           of (NONE, report) => apsnd (cons report) (with_testers k testers)
            | (SOME q, report) => (SOME q, [report]);
    fun with_size k reports = if k > size then (NONE, reports)
      else (if quiet then () else priority ("Test data size: " ^ string_of_int k);
        let
          val (result, new_report) = with_testers k testers
          val reports = ((k, new_report) :: reports)
        in case result of NONE => with_size (k + 1) reports | SOME q => (SOME q, reports) end);
    val ((result, reports), exec_time) = cpu_time "quickcheck execution"
      (fn () => apfst
         (fn result => case result of NONE => NONE
        | SOME ts => SOME (names ~~ ts)) (with_size 1 []))
  in
    (result, ([exec_time, comp_time], if report then SOME reports else NONE))
  end;

fun test_term ctxt quiet generator_name size i t =
  fst (gen_test_term ctxt quiet false generator_name size i t)

fun monomorphic_term thy insts default_T = 
  let
    fun subst (T as TFree (v, S)) =
          let
            val T' = AList.lookup (op =) insts v
              |> the_default (the_default T default_T)
          in if Sign.of_sort thy (T, S) then T'
            else error ("Type " ^ Syntax.string_of_typ_global thy T ^
              " to be substituted for variable " ^
              Syntax.string_of_typ_global thy T ^ "\ndoes not have sort " ^
              Syntax.string_of_sort_global thy S)
          end
      | subst T = T;
  in (map_types o map_atyps) subst end;

fun test_goal quiet report generator_name size iterations default_T no_assms insts i assms state =
  let
    val ctxt = Proof.context_of state;
    val thy = Proof.theory_of state;
    fun strip (Const ("all", _) $ Abs (_, _, t)) = strip t
      | strip t = t;
    val {goal = st, ...} = Proof.raw_goal state;
    val (gi, frees) = Logic.goal_params (prop_of st) i;
    val gi' = Logic.list_implies (if no_assms then [] else assms,
                                  subst_bounds (frees, strip gi))
      |> monomorphic_term thy insts default_T
      |> Object_Logic.atomize_term thy;
  in gen_test_term ctxt quiet report generator_name size iterations gi' end;

fun pretty_counterex ctxt NONE = Pretty.str "Quickcheck found no counterexample."
  | pretty_counterex ctxt (SOME cex) =
      Pretty.chunks (Pretty.str "Quickcheck found a counterexample:\n" ::
        map (fn (s, t) =>
          Pretty.block [Pretty.str (s ^ " ="), Pretty.brk 1, Syntax.pretty_term ctxt t]) cex);

fun pretty_report (Report {iterations = iterations, raised_match_errors = raised_match_errors,
    satisfied_assms = satisfied_assms, positive_concl_tests = positive_concl_tests}) =
  let
    fun pretty_stat s i = Pretty.block ([Pretty.str (s ^ ": " ^ string_of_int i)])
  in
     ([pretty_stat "iterations" iterations,
     pretty_stat "match exceptions" raised_match_errors]
     @ map_index (fn (i, n) => pretty_stat ("satisfied " ^ string_of_int (i + 1) ^ ". assumption") n)
       satisfied_assms
     @ [pretty_stat "positive conclusion tests" positive_concl_tests])
  end

fun pretty_reports' [report] = [Pretty.chunks (pretty_report report)]
  | pretty_reports' reports =
  map_index (fn (i, report) =>
    Pretty.chunks (Pretty.str (string_of_int (i + 1) ^ ". generator:\n") :: pretty_report report))
    reports

fun pretty_reports ctxt (SOME reports) =
  Pretty.chunks (Pretty.str "Quickcheck report:" ::
    maps (fn (size, reports) =>
      Pretty.str ("size " ^ string_of_int size ^ ":") :: pretty_reports' reports @ [Pretty.brk 1])
      (rev reports))
  | pretty_reports ctxt NONE = Pretty.str ""

fun pretty_counterex_and_reports ctxt (cex, (timing, reports)) =
  Pretty.chunks [pretty_counterex ctxt cex, pretty_reports ctxt reports]

(* automatic testing *)

fun auto_quickcheck state =
  if not (!auto) then
    (false, state)
  else
    let
      val ctxt = Proof.context_of state;
      val assms = map term_of (Assumption.all_assms_of ctxt);
      val Test_Params { size, iterations, default_type, no_assms, report, quiet } =
        (snd o Data.get o Proof.theory_of) state;
      val res =
        try (test_goal true false NONE size iterations default_type no_assms [] 1 assms) state;
    in
      case res of
        NONE => (false, state)
      | SOME (NONE, report) => (false, state)
      | SOME (cex, report) => (true, Proof.goal_message (K (Pretty.chunks [Pretty.str "",
          Pretty.mark Markup.hilite (pretty_counterex ctxt cex)])) state)
    end

val setup = Auto_Counterexample.register_tool ("quickcheck", auto_quickcheck)


(* Isar commands *)

fun read_nat s = case (Library.read_int o Symbol.explode) s
 of (k, []) => if k >= 0 then k
      else error ("Not a natural number: " ^ s)
  | (_, _ :: _) => error ("Not a natural number: " ^ s);
fun read_bool "false" = false
  | read_bool "true" = true
  | read_bool s = error ("Not a Boolean value: " ^ s)

fun parse_test_param ctxt ("size", arg) =
      (apfst o apfst o K) (read_nat arg)
  | parse_test_param ctxt ("iterations", arg) =
      (apfst o apsnd o K) (read_nat arg)
  | parse_test_param ctxt ("default_type", arg) =
      (apsnd o apfst o apfst o K o SOME) (ProofContext.read_typ ctxt arg)
  | parse_test_param ctxt ("no_assms", arg) =
      (apsnd o apfst o apsnd o K) (read_bool arg)
  | parse_test_param ctxt ("report", arg) =
      (apsnd o apsnd o apfst o K) (read_bool arg)
  | parse_test_param ctxt ("quiet", arg) =
      (apsnd o apsnd o apsnd o K) (read_bool arg)
  | parse_test_param ctxt (name, _) =
      error ("Unknown test parameter: " ^ name);

fun parse_test_param_inst ctxt ("generator", arg) =
      (apsnd o apfst o K o SOME) arg
  | parse_test_param_inst ctxt (name, arg) =
      case try (ProofContext.read_typ ctxt) name
       of SOME (TFree (v, _)) => (apsnd o apsnd o AList.update (op =))
              (v, ProofContext.read_typ ctxt arg)
        | _ => (apfst o parse_test_param ctxt) (name, arg);

fun quickcheck_params_cmd args thy =
  let
    val ctxt = ProofContext.init_global thy;
    val f = fold (parse_test_param ctxt) args;
  in
    thy
    |> (Data.map o apsnd o map_test_params) f
  end;

fun gen_quickcheck args i state =
  let
    val thy = Proof.theory_of state;
    val ctxt = Proof.context_of state;
    val assms = map term_of (Assumption.all_assms_of ctxt);
    val default_params = (dest_test_params o snd o Data.get) thy;
    val f = fold (parse_test_param_inst ctxt) args;
    val (((size, iterations), ((default_type, no_assms), (report, quiet))), (generator_name, insts)) =
      f (default_params, (NONE, []));
  in
    test_goal quiet report generator_name size iterations default_type no_assms insts i assms state
  end;

fun quickcheck args i state = fst (gen_quickcheck args i state);

fun quickcheck_cmd args i state =
  gen_quickcheck args i (Toplevel.proof_of state)
  |> Pretty.writeln o pretty_counterex_and_reports (Toplevel.context_of state);

val parse_arg = Parse.name -- (Scan.optional (Parse.$$$ "=" |-- Parse.name) "true");

val parse_args = Parse.$$$ "[" |-- Parse.list1 parse_arg --| Parse.$$$ "]"
  || Scan.succeed [];

val _ =
  Outer_Syntax.command "quickcheck_params" "set parameters for random testing" Keyword.thy_decl
    (parse_args >> (fn args => Toplevel.theory (quickcheck_params_cmd args)));

val _ =
  Outer_Syntax.improper_command "quickcheck" "try to find counterexample for subgoal" Keyword.diag
    (parse_args -- Scan.optional Parse.nat 1
      >> (fn (args, i) => Toplevel.no_timing o Toplevel.keep (quickcheck_cmd args i)));

end;


val auto_quickcheck = Quickcheck.auto;
