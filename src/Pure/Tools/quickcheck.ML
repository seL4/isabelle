(*  Title:      Pure/Tools/quickcheck.ML
    ID:         $Id$
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen

Generic counterexample search engine.
*)

signature QUICKCHECK =
sig
  val test_term: string option -> Proof.context -> bool -> int -> int -> term -> (string * term) list option;
  val add_generator: string * (Proof.context -> term -> int -> term list option) -> theory -> theory
end;

structure Quickcheck : QUICKCHECK =
struct

datatype test_params = Test_Params of
  { size: int, iterations: int, default_type: typ option };

fun mk_test_params ((size, iterations), default_type) =
  Test_Params { size = size, iterations = iterations, default_type = default_type };
fun map_test_params f (Test_Params { size, iterations, default_type}) =
  mk_test_params (f ((size, iterations), default_type));
fun merge_test_params (Test_Params {size = size1, iterations = iterations1, default_type = default_type1},
  Test_Params {size = size2, iterations = iterations2, default_type = default_type2}) =
  mk_test_params ((Int.max (size1, size2), Int.max (iterations1, iterations2)),
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

fun prep_test_term t =
  let
    val _ = (null (term_tvars t) andalso null (term_tfrees t)) orelse
      error "Term to be tested contains type variables";
    val _ = null (term_vars t) orelse
      error "Term to be tested contains schematic variables";
    val frees = map dest_Free (term_frees t);
  in (map fst frees, list_abs_free (frees, t)) end

fun test_term generator_name ctxt quiet size i t =
  let
    val (names, t') = prep_test_term t;
    val testers = case generator_name
     of NONE => if quiet then mk_testers ctxt t' else mk_testers_strict ctxt t'
      | SOME name => [mk_tester_select name ctxt t'];
    fun iterate f 0 = NONE
      | iterate f k = case f () handle Match => (if quiet then ()
             else warning "Exception Match raised during quickcheck"; NONE)
          of NONE => iterate f (k - 1) | SOME q => SOME q;
    fun with_testers k [] = NONE
      | with_testers k (tester :: testers) =
          case iterate (fn () => tester k) i
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
          in if Sign.of_sort thy (T, S) then T
            else error ("Type " ^ Syntax.string_of_typ_global thy T ^
              " to be substituted for variable " ^
              Syntax.string_of_typ_global thy T ^ "\ndoes not have sort " ^
              Syntax.string_of_sort_global thy S)
          end
      | subst T = T;
  in (map_types o map_atyps) subst end;

fun pretty_counterex ctxt NONE = Pretty.str "No counterexamples found."
  | pretty_counterex ctxt (SOME cex) =
      Pretty.chunks (Pretty.str "Counterexample found:\n" ::
        map (fn (s, t) =>
          Pretty.block [Pretty.str (s ^ " ="), Pretty.brk 1, Syntax.pretty_term ctxt t]) cex);

fun test_goal generator_name quiet size iterations default_T insts i assms state =
  let
    val ctxt = Proof.context_of state;
    val thy = Proof.theory_of state;
    fun strip (Const ("all", _) $ Abs (_, _, t)) = strip t
      | strip t = t;
    val (_, (_, st)) = Proof.get_goal state;
    val (gi, frees) = Logic.goal_params (prop_of st) i;
    val gi' = Logic.list_implies (assms, subst_bounds (frees, strip gi))
      |> monomorphic_term thy insts default_T
      |> ObjectLogic.atomize_term thy;
  in test_term generator_name ctxt quiet size iterations gi' end;

val auto = ref false;
val auto_time_limit = ref 5000;

fun test_goal_auto int state =
  let
    val ctxt = Proof.context_of state;
    val assms = map term_of (Assumption.assms_of ctxt);
    val Test_Params { size, iterations, default_type } =
      (snd o Data.get o Proof.theory_of) state;
    fun test () =
      let
        val res = TimeLimit.timeLimit (Time.fromMilliseconds (!auto_time_limit))
          (try (test_goal NONE true size iterations default_type [] 1 assms)) state;
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
  end;

(*val _ = Context.>> (Specification.add_theorem_hook test_goal_auto);*)

fun test_goal_cmd generator_name i state =
  test_goal generator_name false 10 100 NONE [] i [] (Toplevel.proof_of state)
  |> pretty_counterex (Toplevel.context_of state)
  |> Pretty.writeln;

local structure P = OuterParse and K = OuterKeyword in

fun read_nothing x thy = x;
fun read_typ raw_ty thy = Syntax.read_typ_global thy raw_ty;

val parse_test_param = (P.short_ident --| P.$$$ "=" #->
  (fn "size" => P.nat >> (apfst o apfst o K)
    | "iterations" => P.nat >> (apfst o apsnd o K)
    | "default_type" => P.typ >> (apsnd o K)));

val parse_test_param_inst =
  P.type_ident --| P.$$$ "=" -- P.typ >> (apsnd o AList.update (op =))
  || parse_test_param >> apfst;

(*fun quickcheck_test_params_cmd fs thy =
  (Data.map o apsnd o map_test_params) (Library.apply fs);*)

(*val _ =
  OuterSyntax.command "quickcheck_params" "set parameters for random testing" K.thy_decl
    (P.$$$ "[" |-- P.list1 parse_test_param --| P.$$$ "]" >>
      (Toplevel.theory o quickcheck_test_params_cmd));*)

(*
val params =
  [("size", P.nat >> (K o set_size)),
   ("iterations", P.nat >> (K o set_iterations)),
   ("default_type", P.typ >> set_default_type)];

val parse_test_params = P.short_ident :|-- (fn s =>
  P.$$$ "=" |-- (AList.lookup (op =) params s |> the_default Scan.fail));

fun parse_tyinst xs =
  (P.type_ident --| P.$$$ "=" -- P.typ >> (fn (v, s) => fn thy =>
    fn (x, ys) => (x, (v, Syntax.read_typ_global thy s) :: ys))) xs;


*)

val _ = OuterSyntax.improper_command "test_goal" "try to find counterexample for subgoal" K.diag
  (Scan.option (P.$$$ "[" |-- P.xname --| P.$$$ "]") -- Scan.optional P.nat 1
    >> (fn (some_name, i) => Toplevel.no_timing o Toplevel.keep (test_goal_cmd some_name i)));

end; (*local*)



(*
val _ =
  OuterSyntax.command "quickcheck_params" "set parameters for random testing" K.thy_decl
    (P.$$$ "[" |-- P.list1 parse_test_params --| P.$$$ "]" >>
      (fn fs => Toplevel.theory (fn thy =>
         map_test_params (Library.apply (map (fn f => f thy) fs)) thy)));

val _ =
  OuterSyntax.command "quickcheck" "try to find counterexample for subgoal" K.diag
  (Scan.option (P.$$$ "[" |-- P.list1
    (   parse_test_params >> (fn f => fn thy => apfst (f thy))
     || parse_tyinst) --| P.$$$ "]") -- Scan.optional P.nat 1 >>
    (fn (ps, g) => Toplevel.keep (fn st => Toplevel.proof_of st |>
      test_goal false (Library.apply (the_default []
          (Option.map (map (fn f => f (Toplevel.theory_of st))) ps))
        (get_test_params (Toplevel.theory_of st), [])) g [] |>
      pretty_counterex (Toplevel.context_of st) |> Pretty.writeln)));

val auto_quickcheck = ref false;
val auto_quickcheck_time_limit = ref 5000;

fun test_goal' int state =
  let
    val ctxt = Proof.context_of state;
    val assms = map term_of (Assumption.assms_of ctxt);
    val params = get_test_params (Proof.theory_of state);
    fun test () =
      let
        val res = TimeLimit.timeLimit (Time.fromMilliseconds (!auto_quickcheck_time_limit))
          (try (test_goal true (params, []) 1 assms)) state;
      in
        case res of
          NONE => state
        | SOME NONE => state
        | SOME cex => Proof.goal_message (fn () => Pretty.chunks [Pretty.str "",
            Pretty.mark Markup.hilite (pretty_counterex ctxt cex)]) state
      end handle TimeLimit.TimeOut => (warning "Auto quickcheck: timeout."; state);
  in
    if int andalso !auto_quickcheck andalso not (!Toplevel.quiet)
    then test ()
    else state
  end;
*)

(*
fun value_cmd some_name modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = case some_name
     of NONE => value ctxt t
      | SOME name => value_select name ctxt t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t ctxt;
    val p = PrintMode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;*)

end;

(*val auto_quickcheck = Quickcheck.auto;
val auto_quickcheck_time_limit = Quickcheck.auto_time_limit;*)
