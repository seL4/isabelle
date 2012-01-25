(*  Title:      HOL/Tools/Quickcheck/quickcheck_common.ML
    Author:     Florian Haftmann, Lukas Bulwahn, TU Muenchen

Common functions for quickcheck's generators.
*)

signature QUICKCHECK_COMMON =
sig
  val strip_imp : term -> (term list * term)
  val reflect_bool : bool -> term
  val define_functions : ((term list -> term list) * (Proof.context -> tactic) option)
    -> string -> string list -> string list -> typ list -> Proof.context -> Proof.context 
  val perhaps_constrain: theory -> (typ * sort) list -> (string * sort) list
    -> (string * sort -> string * sort) option
  val instantiate_goals: Proof.context -> (string * typ) list -> (term * term list) list
    -> (typ option * (term * term list)) list list
  val mk_safe_if : term -> term -> term * term * (bool -> term) -> bool -> term
  val collect_results : ('a -> Quickcheck.result) -> 'a list -> Quickcheck.result list -> Quickcheck.result list
  type result = (bool * term list) option * Quickcheck.report option
  type generator = string * ((theory -> typ list -> bool) * 
      (Proof.context -> (term * term list) list -> bool -> int list -> result))
  val generator_test_goal_terms :
    generator -> Proof.context -> bool -> (string * typ) list
      -> (term * term list) list -> Quickcheck.result list
  type instantiation = Datatype.config -> Datatype.descr -> (string * sort) list
     -> string list -> string -> string list * string list -> typ list * typ list -> theory -> theory
  val ensure_sort :
    (((sort * sort) * sort) *
      ((theory -> string list -> Datatype_Aux.descr * (string * sort) list * string list
        * string * (string list * string list) * (typ list * typ list)) * instantiation))
    -> Datatype.config -> string list -> theory -> theory
  val ensure_common_sort_datatype :
    (sort * instantiation) -> Datatype.config -> string list -> theory -> theory
  val datatype_interpretation : (sort * instantiation) -> theory -> theory
  val gen_mk_parametric_generator_expr :
   (((Proof.context -> term * term list -> term) * term) * typ)
     -> Proof.context -> (term * term list) list -> term
  val mk_fun_upd : typ -> typ -> term * term -> term -> term
  val post_process_term : term -> term
  val test_term : generator -> Proof.context -> bool -> term * term list -> Quickcheck.result
end;

structure Quickcheck_Common : QUICKCHECK_COMMON =
struct

(* static options *)

val define_foundationally = false

(* HOLogic's term functions *)

fun strip_imp (Const(@{const_name HOL.implies},_) $ A $ B) = apfst (cons A) (strip_imp B)
  | strip_imp A = ([], A)

fun reflect_bool b = if b then @{term "True"} else @{term "False"}

fun mk_undefined T = Const(@{const_name undefined}, T)

(* testing functions: testing with increasing sizes (and cardinalities) *)

type result = (bool * term list) option * Quickcheck.report option
type generator = string * ((theory -> typ list -> bool) * 
      (Proof.context -> (term * term list) list -> bool -> int list -> result))

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

fun test_term (name, (_, compile)) ctxt catch_code_errors (t, eval_terms) =
  let
    val genuine_only = Config.get ctxt Quickcheck.genuine_only
    val _ = check_test_term t
    val names = Term.add_free_names t []
    val current_size = Unsynchronized.ref 0
    val current_result = Unsynchronized.ref Quickcheck.empty_result 
    fun excipit () =
      "Quickcheck ran out of time while testing at size " ^ string_of_int (!current_size)
    val act = if catch_code_errors then try else (fn f => SOME o f) 
    val (test_fun, comp_time) = cpu_time "quickcheck compilation"
        (fn () => act (compile ctxt) [(t, eval_terms)]);
    val _ = Quickcheck.add_timing comp_time current_result
    fun with_size test_fun genuine_only k =
      if k > Config.get ctxt Quickcheck.size then
        NONE
      else
        let
          val _ = Quickcheck.verbose_message ctxt
            ("[Quickcheck-" ^ name ^ "] Test data size: " ^ string_of_int k)
          val _ = current_size := k
          val ((result, report), timing) =
            cpu_time ("size " ^ string_of_int k) (fn () => test_fun genuine_only [1, k - 1])
          val _ = Quickcheck.add_timing timing current_result
          val _ = Quickcheck.add_report k report current_result
        in
          case result of
            NONE => with_size test_fun genuine_only (k + 1)
          | SOME (true, ts) => SOME (true, ts)
          | SOME (false, ts) =>
            let
              val (ts1, ts2) = chop (length names) ts
              val (eval_terms', _) = chop (length ts2) eval_terms
              val cex = SOME ((false, names ~~ ts1), eval_terms' ~~ ts2)
            in
              (Quickcheck.message ctxt (Pretty.string_of (Quickcheck.pretty_counterex ctxt false cex));
              Quickcheck.message ctxt "Quickcheck continues to find a genuine counterexample...";
              with_size test_fun true k)
            end
        end;
  in
    case test_fun of
      NONE => (Quickcheck.message ctxt ("Conjecture is not executable with Quickcheck-" ^ name);
        !current_result)
    | SOME test_fun =>
      let
        val _ = Quickcheck.message ctxt ("Testing conjecture with Quickcheck-" ^ name ^ "...");
        val (response, exec_time) =
          cpu_time "quickcheck execution" (fn () => with_size test_fun genuine_only 1)
        val _ = Quickcheck.add_response names eval_terms response current_result
        val _ = Quickcheck.add_timing exec_time current_result
      in !current_result end
  end;

fun validate_terms ctxt ts =
  let
    val _ = map check_test_term ts
    val size = Config.get ctxt Quickcheck.size
    val (test_funs, comp_time) = cpu_time "quickcheck batch compilation"
      (fn () => Quickcheck.mk_batch_validator ctxt ts) 
    fun with_size tester k =
      if k > size then true
      else if tester k then with_size tester (k + 1) else false
    val (results, exec_time) = cpu_time "quickcheck batch execution" (fn () =>
        Option.map (map (fn test_fun =>
          TimeLimit.timeLimit (seconds (Config.get ctxt Quickcheck.timeout))
              (fn () => with_size test_fun 1) ()
             handle TimeLimit.TimeOut => true)) test_funs)
  in
    (results, [comp_time, exec_time])
  end
  
fun test_terms ctxt ts =
  let
    val _ = map check_test_term ts
    val size = Config.get ctxt Quickcheck.size
    val namess = map (fn t => Term.add_free_names t []) ts
    val (test_funs, comp_time) =
      cpu_time "quickcheck batch compilation" (fn () => Quickcheck.mk_batch_tester ctxt ts) 
    fun with_size tester k =
      if k > size then NONE
      else case tester k of SOME ts => SOME ts | NONE => with_size tester (k + 1)
    val (results, exec_time) = cpu_time "quickcheck batch execution" (fn () =>
        Option.map (map (fn test_fun =>
          TimeLimit.timeLimit (seconds (Config.get ctxt Quickcheck.timeout))
              (fn () => with_size test_fun 1) ()
             handle TimeLimit.TimeOut => NONE)) test_funs)
  in
    (Option.map (map2 (fn names => Option.map (fn ts => names ~~ ts)) namess) results,
      [comp_time, exec_time])
  end

fun test_term_with_cardinality (name, (size_matters_for, compile)) ctxt catch_code_errors ts =
  let
    val genuine_only = Config.get ctxt Quickcheck.genuine_only
    val thy = Proof_Context.theory_of ctxt
    val (ts', eval_terms) = split_list ts
    val _ = map check_test_term ts'
    val names = Term.add_free_names (hd ts') []
    val Ts = map snd (Term.add_frees (hd ts') [])
    val current_result = Unsynchronized.ref Quickcheck.empty_result
    fun test_card_size test_fun genuine_only (card, size) =
      (* FIXME: why decrement size by one? *)
      let
        val _ =
          Quickcheck.verbose_message ctxt ("[Quickcheck-" ^ name ^ "] Test " ^
            (if size = 0 then "" else "data size: " ^ string_of_int (size - 1) ^ " and ") ^
            "cardinality: " ^ string_of_int card)          
        val (ts, timing) =
          cpu_time ("size " ^ string_of_int size ^ " and card " ^ string_of_int card)
            (fn () => fst (test_fun genuine_only [card, size - 1]))
        val _ = Quickcheck.add_timing timing current_result
      in
        Option.map (pair (card, size)) ts
      end
    val enumeration_card_size =
      if size_matters_for thy Ts then
        map_product pair (1 upto (length ts)) (1 upto (Config.get ctxt Quickcheck.size))
        |> sort (fn ((c1, s1), (c2, s2)) => int_ord ((c1 + s1), (c2 + s2)))
      else
        map (rpair 0) (1 upto (length ts))
    val act = if catch_code_errors then try else (fn f => SOME o f)
    val (test_fun, comp_time) = cpu_time "quickcheck compilation" (fn () => act (compile ctxt) ts)
    val _ = Quickcheck.add_timing comp_time current_result
  in
    case test_fun of
      NONE => (Quickcheck.message ctxt ("Conjecture is not executable with Quickcheck-" ^ name);
        !current_result)
    | SOME test_fun =>
      let
        val _ = Quickcheck.message ctxt ("Testing conjecture with Quickcheck-" ^ name ^ "...");
        fun test genuine_only enum = case get_first (test_card_size test_fun genuine_only) enum of
          SOME ((card, _), (true, ts)) =>
            Quickcheck.add_response names (nth eval_terms (card - 1)) (SOME (true, ts)) current_result
        | SOME ((card, size), (false, ts)) =>
           let
              val (ts1, ts2) = chop (length names) ts
              val (eval_terms', _) = chop (length ts2) (nth eval_terms (card - 1))
              val cex = SOME ((false, names ~~ ts1), eval_terms' ~~ ts2)
            in
              (Quickcheck.message ctxt (Pretty.string_of (Quickcheck.pretty_counterex ctxt false cex));
              Quickcheck.message ctxt "Quickcheck continues to find a genuine counterexample...";
              test true (snd (take_prefix (fn x => not (x = (card, size))) enum)))
            end
        | NONE => ()
      in (test genuine_only enumeration_card_size; !current_result) end
  end

fun get_finite_types ctxt =
  fst (chop (Config.get ctxt Quickcheck.finite_type_size)
    [@{typ "Enum.finite_1"}, @{typ "Enum.finite_2"}, @{typ "Enum.finite_3"},
     @{typ "Enum.finite_4"}, @{typ "Enum.finite_5"}])

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

(* minimalistic preprocessing *)

fun strip_all (Const (@{const_name HOL.All}, _) $ Abs (a, T, t)) = 
  let
    val (a', t') = strip_all t
  in ((a, T) :: a', t') end
  | strip_all t = ([], t);

fun preprocess ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    val dest = HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of
    val rewrs = map (swap o dest) @{thms all_simps} @
      (map dest [@{thm not_ex}, @{thm not_all}, @{thm imp_conjL}, @{thm fun_eq_iff},
        @{thm bot_fun_def}, @{thm less_bool_def}])
    val t' = Pattern.rewrite_term thy rewrs [] (Object_Logic.atomize_term thy t)
    val (vs, body) = strip_all t'
    val vs' = Variable.variant_frees ctxt [t'] vs
  in
    subst_bounds (map Free (rev vs'), body)
  end

(* instantiation of type variables with concrete types *)
 
fun instantiate_goals lthy insts goals =
  let
    fun map_goal_and_eval_terms f (check_goal, eval_terms) = (f check_goal, map f eval_terms)
    val thy = Proof_Context.theory_of lthy
    val default_insts =
      if Config.get lthy Quickcheck.finite_types then get_finite_types else Quickcheck.default_type
    val inst_goals =
      map (fn (check_goal, eval_terms) =>
        if not (null (Term.add_tfree_names check_goal [])) then
          map (fn T =>
            (pair (SOME T) o Term o apfst (preprocess lthy))
              (map_goal_and_eval_terms (monomorphic_term thy insts T) (check_goal, eval_terms))
              handle WELLSORTED s => (SOME T, Wellsorted_Error s)) (default_insts lthy)
        else
          [(NONE, Term (preprocess lthy check_goal, eval_terms))]) goals
    val error_msg =
      cat_lines
        (maps (map_filter (fn (_, Term t) => NONE | (_, Wellsorted_Error s) => SOME s)) inst_goals)
    fun is_wellsorted_term (T, Term t) = SOME (T, t)
      | is_wellsorted_term (_, Wellsorted_Error s) = NONE
    val correct_inst_goals =
      case map (map_filter is_wellsorted_term) inst_goals of
        [[]] => error error_msg
      | xs => xs
    val _ = if Config.get lthy Quickcheck.quiet then () else warning error_msg
  in
    correct_inst_goals
  end

(* compilation of testing functions *)

fun mk_safe_if genuine_only none (cond, then_t, else_t) genuine =
  let
    val T = fastype_of then_t
    val if_t = Const (@{const_name "If"}, @{typ bool} --> T --> T --> T)
  in
    Const (@{const_name "Quickcheck.catch_match"}, T --> T --> T) $ 
      (if_t $ cond $ then_t $ else_t genuine) $
      (if_t $ genuine_only $ none $ else_t false)
  end

fun collect_results f [] results = results
  | collect_results f (t :: ts) results =
    let
      val result = f t
    in
      if Quickcheck.found_counterexample result then
        (result :: results)
      else
        collect_results f ts (result :: results)
    end  

fun generator_test_goal_terms generator ctxt catch_code_errors insts goals =
  let
    fun add_eval_term t ts = if is_Free t then ts else ts @ [t]
    fun add_equation_eval_terms (t, eval_terms) =
      case try HOLogic.dest_eq (snd (strip_imp t)) of
        SOME (lhs, rhs) => (t, add_eval_term lhs (add_eval_term rhs eval_terms))
      | NONE => (t, eval_terms)
    fun test_term' goal =
      case goal of
        [(NONE, t)] => test_term generator ctxt catch_code_errors t
      | ts => test_term_with_cardinality generator ctxt catch_code_errors (map snd ts)
    val goals' = instantiate_goals ctxt insts goals
      |> map (map (apsnd add_equation_eval_terms))
  in
    if Config.get ctxt Quickcheck.finite_types then
      collect_results test_term' goals' []
    else
      collect_results (test_term generator ctxt catch_code_errors)
        (maps (map snd) goals') []
  end;

(* defining functions *)

fun pat_completeness_auto ctxt =
  Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt

fun define_functions (mk_equations, termination_tac) prfx argnames names Ts =
  if define_foundationally andalso is_some termination_tac then
    let
      val eqs_t = mk_equations (map2 (fn name => fn T => Free (name, T)) names Ts)
    in
      Function.add_function
        (map (fn (name, T) => (Binding.conceal (Binding.name name), SOME T, NoSyn))
          (names ~~ Ts))
        (map (pair (apfst Binding.conceal Attrib.empty_binding)) eqs_t)
        Function_Common.default_config pat_completeness_auto
      #> snd
      #> (fn lthy => Function.prove_termination NONE (the termination_tac lthy) lthy)
      #> snd
    end
  else
    fold_map (fn (name, T) => Local_Theory.define
        ((Binding.conceal (Binding.name name), NoSyn),
          (apfst Binding.conceal Attrib.empty_binding, mk_undefined T))
      #> apfst fst) (names ~~ Ts)
    #> (fn (consts, lthy) =>
      let
        val eqs_t = mk_equations consts
        val eqs = map (fn eq => Goal.prove lthy argnames [] eq
          (fn _ => Skip_Proof.cheat_tac (Proof_Context.theory_of lthy))) eqs_t
      in
        fold (fn (name, eq) => Local_Theory.note
          ((Binding.conceal
            (Binding.qualify true prfx
              (Binding.qualify true name (Binding.name "simps"))),
             Code.add_default_eqn_attrib :: @{attributes [simp, nitpick_simp]}), [eq]) #> snd)
          (names ~~ eqs) lthy
      end)

(** ensuring sort constraints **)

type instantiation = Datatype.config -> Datatype.descr -> (string * sort) list
  -> string list -> string -> string list * string list -> typ list * typ list -> theory -> theory

fun perhaps_constrain thy insts raw_vs =
  let
    fun meet (T, sort) = Sorts.meet_sort (Sign.classes_of thy) 
      (Logic.varifyT_global T, sort);
    val vtab = Vartab.empty
      |> fold (fn (v, sort) => Vartab.update ((v, 0), sort)) raw_vs
      |> fold meet insts;
  in SOME (fn (v, _) => (v, (the o Vartab.lookup vtab) (v, 0)))
  end handle Sorts.CLASS_ERROR _ => NONE;

fun ensure_sort (((sort_vs, aux_sort), sort), (the_descr, instantiate)) config raw_tycos thy =
  let
    val algebra = Sign.classes_of thy;
    val (descr, raw_vs, tycos, prfx, (names, auxnames), raw_TUs) = the_descr thy raw_tycos
    val vs = (map o apsnd) (curry (Sorts.inter_sort algebra) sort_vs) raw_vs
    fun insts_of sort constr  = (map (rpair sort) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr vs constr)
    val insts = insts_of sort  { atyp = single, dtyp = (K o K o K) [] }
      @ insts_of aux_sort { atyp = K [], dtyp = K o K }
    val has_inst = exists (fn tyco => can (Sorts.mg_domain algebra tyco) sort) tycos;
  in if has_inst then thy
    else case perhaps_constrain thy insts vs
     of SOME constrain => instantiate config descr
          (map constrain vs) tycos prfx (names, auxnames)
            ((pairself o map o map_atyps) (fn TFree v => TFree (constrain v)) raw_TUs) thy
      | NONE => thy
  end;

fun ensure_common_sort_datatype (sort, instantiate) =
  ensure_sort (((@{sort typerep}, @{sort term_of}), sort), (Datatype.the_descr, instantiate))

val datatype_interpretation = Datatype.interpretation o ensure_common_sort_datatype
  
(** generic parametric compilation **)

fun gen_mk_parametric_generator_expr ((mk_generator_expr, out_of_bounds), T) ctxt ts =
  let
    val if_t = Const (@{const_name "If"}, @{typ bool} --> T --> T --> T)
    fun mk_if (index, (t, eval_terms)) else_t = if_t $
        (HOLogic.eq_const @{typ code_numeral} $ Bound 0 $ HOLogic.mk_number @{typ code_numeral} index) $
        (mk_generator_expr ctxt (t, eval_terms)) $ else_t
  in
    absdummy @{typ "code_numeral"} (fold_rev mk_if (1 upto (length ts) ~~ ts) out_of_bounds)
  end

(** post-processing of function terms **)

fun dest_fun_upd (Const (@{const_name fun_upd}, _) $ t0 $ t1 $ t2) = (t0, (t1, t2))
  | dest_fun_upd t = raise TERM ("dest_fun_upd", [t])

fun mk_fun_upd T1 T2 (t1, t2) t = 
  Const (@{const_name fun_upd}, (T1 --> T2) --> T1 --> T2 --> T1 --> T2) $ t $ t1 $ t2

fun dest_fun_upds t =
  case try dest_fun_upd t of
    NONE =>
      (case t of
        Abs (_, _, _) => ([], t) 
      | _ => raise TERM ("dest_fun_upds", [t]))
  | SOME (t0, (t1, t2)) => apfst (cons (t1, t2)) (dest_fun_upds t0)

fun make_fun_upds T1 T2 (tps, t) = fold_rev (mk_fun_upd T1 T2) tps t

fun make_set T1 [] = Const (@{const_abbrev Set.empty}, T1 --> @{typ bool})
  | make_set T1 ((_, @{const False}) :: tps) = make_set T1 tps
  | make_set T1 ((t1, @{const True}) :: tps) =
    Const (@{const_name insert}, T1 --> (T1 --> @{typ bool}) --> T1 --> @{typ bool})
      $ t1 $ (make_set T1 tps)
  | make_set T1 ((_, t) :: tps) = raise TERM ("make_set", [t])

fun make_coset T [] = Const (@{const_abbrev UNIV}, T --> @{typ bool})
  | make_coset T tps = 
    let
      val U = T --> @{typ bool}
      fun invert @{const False} = @{const True}
        | invert @{const True} = @{const False}
    in
      Const (@{const_name "Groups.minus_class.minus"}, U --> U --> U)
        $ Const (@{const_abbrev UNIV}, U) $ make_set T (map (apsnd invert) tps)
    end

fun make_map T1 T2 [] = Const (@{const_abbrev Map.empty}, T1 --> T2)
  | make_map T1 T2 ((_, Const (@{const_name None}, _)) :: tps) = make_map T1 T2 tps
  | make_map T1 T2 ((t1, t2) :: tps) = mk_fun_upd T1 T2 (t1, t2) (make_map T1 T2 tps)
  
fun post_process_term t =
  let
    fun map_Abs f t =
      case t of Abs (x, T, t') => Abs (x, T, f t') | _ => raise TERM ("map_Abs", [t]) 
    fun process_args t = case strip_comb t of
      (c as Const (_, _), ts) => list_comb (c, map post_process_term ts)
  in
    case fastype_of t of
      Type (@{type_name fun}, [T1, T2]) =>
        (case try dest_fun_upds t of
          SOME (tps, t) =>
            (map (pairself post_process_term) tps, map_Abs post_process_term t)
            |> (case T2 of
              @{typ bool} => 
                (case t of
                   Abs(_, _, @{const False}) => fst #> rev #> make_set T1
                 | Abs(_, _, @{const True}) => fst #> rev #> make_coset T1
                 | Abs(_, _, Const (@{const_name undefined}, _)) => fst #> rev #> make_set T1
                 | _ => raise TERM ("post_process_term", [t]))
            | Type (@{type_name option}, _) =>
                (case t of
                  Abs(_, _, Const (@{const_name None}, _)) => fst #> make_map T1 T2
                | Abs(_, _, Const (@{const_name undefined}, _)) => fst #> make_map T1 T2
                | _ => make_fun_upds T1 T2)
            | _ => make_fun_upds T1 T2)
        | NONE => process_args t)
    | _ => process_args t
  end

end;
