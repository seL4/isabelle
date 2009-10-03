(*  Title:      Tools/quickcheck.ML
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen

Generic counterexample search engine.
*)

signature QUICKCHECK =
sig
  val auto: bool Unsynchronized.ref
  val auto_time_limit: int Unsynchronized.ref
  val test_term: Proof.context -> bool -> string option -> int -> int -> term ->
    (string * term) list option
  val add_generator: string * (Proof.context -> term -> int -> term list option) -> theory -> theory
  val quickcheck: (string * string) list -> int -> Proof.state -> (string * term) list option
end;

structure Quickcheck : QUICKCHECK =
struct

(* preferences *)

val auto = Unsynchronized.ref false;
val auto_time_limit = Unsynchronized.ref 2500;

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
  (setmp auto true (fn () =>
    Preferences.bool_pref auto
      "auto-quickcheck"
      "Whether to enable quickcheck automatically.") ());

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
    (Preferences.nat_pref auto_time_limit
      "auto-quickcheck-time-limit"
      "Time limit for automatic quickcheck (in milliseconds).");


(* quickcheck configuration -- default parameters, test generators *)

datatype test_params = Test_Params of
  { size: int, iterations: int, default_type: typ option };

fun dest_test_params (Test_Params { size, iterations, default_type }) =
  ((size, iterations), default_type);
fun make_test_params ((size, iterations), default_type) =
  Test_Params { size = size, iterations = iterations, default_type = default_type };
fun map_test_params f (Test_Params { size, iterations, default_type}) =
  make_test_params (f ((size, iterations), default_type));
fun merge_test_params (Test_Params { size = size1, iterations = iterations1, default_type = default_type1 },
  Test_Params { size = size2, iterations = iterations2, default_type = default_type2 }) =
  make_test_params ((Int.max (size1, size2), Int.max (iterations1, iterations2)),
    case default_type1 of NONE => default_type2 | _ => default_type1);

structure Data = TheoryDataFun(
  type T = (string * (Proof.context -> term -> int -> term list option)) list
    * test_params;
  val empty = ([], Test_Params { size = 10, iterations = 100, default_type = NONE });
  val copy = I;
  val extend = I;
  fun merge pp ((generators1, params1), (generators2, params2)) =
    (AList.merge (op = : string * string -> bool) (K true) (generators1, generators2),
      merge_test_params (params1, params2));
)

val add_generator = Data.map o apfst o AList.update (op =);


(* generating tests *)

fun mk_tester_select name ctxt =
  case AList.lookup (op =) ((fst o Data.get o ProofContext.theory_of) ctxt) name
   of NONE => error ("No such quickcheck generator: " ^ name)
    | SOME generator => generator ctxt;

fun mk_testers ctxt t =
  (map snd o fst o Data.get o ProofContext.theory_of) ctxt
  |> map_filter (fn generator => try (generator ctxt) t);

fun mk_testers_strict ctxt t =
  let
    val generators = ((map snd o fst o Data.get o ProofContext.theory_of) ctxt)
    val testers = map (fn generator => Exn.capture (generator ctxt) t) generators;
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

fun test_term ctxt quiet generator_name size i t =
  let
    val (names, t') = prep_test_term t;
    val testers = case generator_name
     of NONE => if quiet then mk_testers ctxt t' else mk_testers_strict ctxt t'
      | SOME name => [mk_tester_select name ctxt t'];
    fun iterate f 0 = NONE
      | iterate f j = case f () handle Match => (if quiet then ()
             else warning "Exception Match raised during quickcheck"; NONE)
          of NONE => iterate f (j - 1) | SOME q => SOME q;
    fun with_testers k [] = NONE
      | with_testers k (tester :: testers) =
          case iterate (fn () => tester (k - 1)) i
           of NONE => with_testers k testers
            | SOME q => SOME q;
    fun with_size k = if k > size then NONE
      else (if quiet then () else priority ("Test data size: " ^ string_of_int k);
        case with_testers k testers
         of NONE => with_size (k + 1) | SOME q => SOME q);
  in case with_size 1
   of NONE => NONE
    | SOME ts => SOME (names ~~ ts)
  end;

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

fun test_goal quiet generator_name size iterations default_T insts i assms state =
  let
    val ctxt = Proof.context_of state;
    val thy = Proof.theory_of state;
    fun strip (Const ("all", _) $ Abs (_, _, t)) = strip t
      | strip t = t;
    val (_, st) = Proof.flat_goal state;
    val (gi, frees) = Logic.goal_params (prop_of st) i;
    val gi' = Logic.list_implies (assms, subst_bounds (frees, strip gi))
      |> monomorphic_term thy insts default_T
      |> ObjectLogic.atomize_term thy;
  in test_term ctxt quiet generator_name size iterations gi' end;

fun pretty_counterex ctxt NONE = Pretty.str "No counterexamples found."
  | pretty_counterex ctxt (SOME cex) =
      Pretty.chunks (Pretty.str "Counterexample found:\n" ::
        map (fn (s, t) =>
          Pretty.block [Pretty.str (s ^ " ="), Pretty.brk 1, Syntax.pretty_term ctxt t]) cex);


(* automatic testing *)

val _ = Context.>> (Specification.add_theorem_hook (fn int => fn state =>
  let
    val ctxt = Proof.context_of state;
    val assms = map term_of (Assumption.all_assms_of ctxt);
    val Test_Params { size, iterations, default_type } =
      (snd o Data.get o Proof.theory_of) state;
    fun test () =
      let
        val res = TimeLimit.timeLimit (Time.fromMilliseconds (!auto_time_limit))
          (try (test_goal true NONE size iterations default_type [] 1 assms)) state;
      in
        case res of
          NONE => state
        | SOME NONE => state
        | SOME cex => Proof.goal_message (fn () => Pretty.chunks [Pretty.str "",
            Pretty.mark Markup.hilite (pretty_counterex ctxt cex)]) state
      end handle TimeLimit.TimeOut => (warning "Auto quickcheck: timeout."; state);
  in
    if int andalso !auto andalso not (!Toplevel.quiet)
    then test ()
    else state
  end));


(* Isar commands *)

fun read_nat s = case (Library.read_int o Symbol.explode) s
 of (k, []) => if k >= 0 then k
      else error ("Not a natural number: " ^ s)
  | (_, _ :: _) => error ("Not a natural number: " ^ s);

fun parse_test_param ctxt ("size", arg) =
      (apfst o apfst o K) (read_nat arg)
  | parse_test_param ctxt ("iterations", arg) =
      (apfst o apsnd o K) (read_nat arg)
  | parse_test_param ctxt ("default_type", arg) =
      (apsnd o K o SOME) (ProofContext.read_typ ctxt arg)
  | parse_test_param ctxt (name, _) =
      error ("Bad test parameter: " ^ name);

fun parse_test_param_inst ctxt ("generator", arg) =
      (apsnd o apfst o K o SOME) arg
  | parse_test_param_inst ctxt (name, arg) =
      case try (ProofContext.read_typ ctxt) name
       of SOME (TFree (v, _)) => (apsnd o apsnd o AList.update (op =))
              (v, ProofContext.read_typ ctxt arg)
        | _ => (apfst o parse_test_param ctxt) (name, arg);

fun quickcheck_params_cmd args thy =
  let
    val ctxt = ProofContext.init thy;
    val f = fold (parse_test_param ctxt) args;
  in
    thy
    |> (Data.map o apsnd o map_test_params) f
  end;

fun quickcheck args i state =
  let
    val thy = Proof.theory_of state;
    val ctxt = Proof.context_of state;
    val default_params = (dest_test_params o snd o Data.get) thy;
    val f = fold (parse_test_param_inst ctxt) args;
    val (((size, iterations), default_type), (generator_name, insts)) =
      f (default_params, (NONE, []));
  in
    test_goal false generator_name size iterations default_type insts i [] state
  end;

fun quickcheck_cmd args i state =
  quickcheck args i (Toplevel.proof_of state)
  |> Pretty.writeln o pretty_counterex (Toplevel.context_of state);

local structure P = OuterParse and K = OuterKeyword in

val parse_arg = P.name --| P.$$$ "=" -- P.name;
val parse_args = P.$$$ "[" |-- P.list1 parse_arg --| P.$$$ "]"
  || Scan.succeed [];

val _ = OuterSyntax.command "quickcheck_params" "set parameters for random testing" K.thy_decl
  (parse_args >> (fn args => Toplevel.theory (quickcheck_params_cmd args)));

val _ = OuterSyntax.improper_command "quickcheck" "try to find counterexample for subgoal" K.diag
  (parse_args -- Scan.optional P.nat 1
    >> (fn (args, i) => Toplevel.no_timing o Toplevel.keep (quickcheck_cmd args i)));

end; (*local*)

end;


val auto_quickcheck = Quickcheck.auto;
val auto_quickcheck_time_limit = Quickcheck.auto_time_limit;
