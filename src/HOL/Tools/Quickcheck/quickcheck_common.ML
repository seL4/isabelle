(*  Title:      HOL/Tools/Quickcheck/quickcheck_common.ML
    Author:     Florian Haftmann, Lukas Bulwahn, TU Muenchen

Common functions for quickcheck's generators.
*)

signature QUICKCHECK_COMMON =
sig
  val compat_prefs : BNF_LFP_Compat.preference list
  val strip_imp : term -> (term list * term)
  val reflect_bool : bool -> term
  val define_functions : ((term list -> term list) * (Proof.context -> tactic) option)
    -> string -> string list -> string list -> typ list -> Proof.context -> Proof.context
  val perhaps_constrain: theory -> (typ * sort) list -> (string * sort) list
    -> (string * sort -> string * sort) option
  val instantiate_goals: Proof.context -> (string * typ) list -> (term * term list) list
    -> (typ option * (term * term list)) list list
  val register_predicate : term * string -> Context.generic -> Context.generic
  val mk_safe_if : term -> term -> term * term * (bool -> term) -> bool -> term
  val collect_results : ('a -> Quickcheck.result) -> 'a list ->
    Quickcheck.result list -> Quickcheck.result list
  type result = (bool * term list) option * Quickcheck.report option
  type generator = string * ((theory -> typ list -> bool) *
      (Proof.context -> (term * term list) list -> bool -> int list -> result))
  val generator_test_goal_terms :
    generator -> Proof.context -> bool -> (string * typ) list
      -> (term * term list) list -> Quickcheck.result list
  type instantiation =
    Old_Datatype_Aux.config -> Old_Datatype_Aux.descr -> (string * sort) list ->
      string list -> string -> string list * string list -> typ list * typ list -> theory -> theory
  val ensure_sort :
    (((sort * sort) * sort) *
      ((theory -> string list -> Old_Datatype_Aux.descr * (string * sort) list * string list
        * string * (string list * string list) * (typ list * typ list)) * instantiation)) ->
    Old_Datatype_Aux.config -> string list -> theory -> theory
  val ensure_common_sort_datatype : (sort * instantiation) -> Old_Datatype_Aux.config ->
    string list -> theory -> theory
  val datatype_interpretation : string -> sort * instantiation -> theory -> theory
  val gen_mk_parametric_generator_expr :
    (((Proof.context -> term * term list -> term) * term) * typ) ->
      Proof.context -> (term * term list) list -> term
  val mk_fun_upd : typ -> typ -> term * term -> term -> term
  val post_process_term : term -> term
  val test_term : generator -> Proof.context -> bool -> term * term list -> Quickcheck.result
end

structure Quickcheck_Common : QUICKCHECK_COMMON =
struct

(* static options *)

val compat_prefs = [BNF_LFP_Compat.Include_GFPs]

val define_foundationally = false


(* HOLogic's term functions *)

fun strip_imp (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ A $ B) = apfst (cons A) (strip_imp B)
  | strip_imp A = ([], A)

fun reflect_bool b = if b then \<^term>\<open>True\<close> else \<^term>\<open>False\<close>

fun mk_undefined T = Const (\<^const_name>\<open>undefined\<close>, T)


(* testing functions: testing with increasing sizes (and cardinalities) *)

type result = (bool * term list) option * Quickcheck.report option
type generator =
  string * ((theory -> typ list -> bool) *
    (Proof.context -> (term * term list) list -> bool -> int list -> result))

fun check_test_term t =
  let
    val _ =
      (null (Term.add_tvars t []) andalso null (Term.add_tfrees t [])) orelse
        error "Term to be tested contains type variables"
    val _ =
      null (Term.add_vars t []) orelse
        error "Term to be tested contains schematic variables"
  in () end

fun cpu_time description e =
  let val ({cpu, ...}, result) = Timing.timing e ()
  in (result, (description, Time.toMilliseconds cpu)) end

fun test_term (name, (_, compile)) ctxt catch_code_errors (t, eval_terms) =
  let
    val genuine_only = Config.get ctxt Quickcheck.genuine_only
    val abort_potential = Config.get ctxt Quickcheck.abort_potential
    val _ = check_test_term t
    val names = Term.add_free_names t []
    val current_size = Unsynchronized.ref 0
    val current_result = Unsynchronized.ref Quickcheck.empty_result
    val act = if catch_code_errors then try else (fn f => SOME o f)
    val (test_fun, comp_time) =
      cpu_time "quickcheck compilation" (fn () => act (compile ctxt) [(t, eval_terms)])
    val _ = Quickcheck.add_timing comp_time current_result
    fun with_size test_fun genuine_only k =
      if k > Config.get ctxt Quickcheck.size then NONE
      else
        let
          val _ =
            Quickcheck.verbose_message ctxt
              ("[Quickcheck-" ^ name ^ "] Test data size: " ^ string_of_int k)
          val _ = current_size := k
          val ((result, report), time) =
            cpu_time ("size " ^ string_of_int k) (fn () => test_fun genuine_only [1, k - 1])
          val _ =
            if Config.get ctxt Quickcheck.timing then
              Quickcheck.verbose_message ctxt (fst time ^ ": " ^ string_of_int (snd time) ^ " ms")
            else ()
          val _ = Quickcheck.add_timing time current_result
          val _ = Quickcheck.add_report k report current_result
        in
          (case result of
            NONE => with_size test_fun genuine_only (k + 1)
          | SOME (true, ts) => SOME (true, ts)
          | SOME (false, ts) =>
              if abort_potential then SOME (false, ts)
              else
                let
                  val (ts1, ts2) = chop (length names) ts
                  val (eval_terms', _) = chop (length ts2) eval_terms
                  val cex = SOME ((false, names ~~ ts1), eval_terms' ~~ ts2)
                in
                  Quickcheck.message ctxt
                    (Pretty.string_of (Quickcheck.pretty_counterex ctxt false cex));
                  Quickcheck.message ctxt "Quickcheck continues to find a genuine counterexample...";
                  with_size test_fun true k
                end)
        end
  in
    case test_fun of
      NONE =>
        (Quickcheck.message ctxt ("Conjecture is not executable with Quickcheck-" ^ name);
          !current_result)
    | SOME test_fun =>
        let
          val _ = Quickcheck.message ctxt ("Testing conjecture with Quickcheck-" ^ name ^ "...")
          val (response, exec_time) =
            cpu_time "quickcheck execution" (fn () => with_size test_fun genuine_only 1)
          val _ = Quickcheck.add_response names eval_terms response current_result
          val _ = Quickcheck.add_timing exec_time current_result
        in !current_result end
  end

fun test_term_with_cardinality (name, (size_matters_for, compile)) ctxt catch_code_errors ts =
  let
    val genuine_only = Config.get ctxt Quickcheck.genuine_only
    val abort_potential = Config.get ctxt Quickcheck.abort_potential
    val thy = Proof_Context.theory_of ctxt
    val (ts', eval_terms) = split_list ts
    val _ = map check_test_term ts'
    val names = Term.add_free_names (hd ts') []
    val Ts = map snd (Term.add_frees (hd ts') [])
    val current_result = Unsynchronized.ref Quickcheck.empty_result
    fun test_card_size test_fun genuine_only (card, size) = (* FIXME: why decrement size by one? *)
      let
        val _ =
          Quickcheck.verbose_message ctxt ("[Quickcheck-" ^ name ^ "] Test " ^
            (if size = 0 then "" else "data size: " ^ string_of_int size ^ " and ") ^
            "cardinality: " ^ string_of_int card)
        val (ts, timing) =
          cpu_time ("size " ^ string_of_int size ^ " and card " ^ string_of_int card)
            (fn () => fst (test_fun genuine_only [card, size + 1]))
        val _ = Quickcheck.add_timing timing current_result
      in Option.map (pair (card, size)) ts end
    val enumeration_card_size =
      if size_matters_for thy Ts then
        map_product pair (1 upto (length ts)) (1 upto (Config.get ctxt Quickcheck.size))
        |> sort (fn ((c1, s1), (c2, s2)) => int_ord ((c1 + s1), (c2 + s2)))
      else map (rpair 0) (1 upto (length ts))
    val act = if catch_code_errors then try else (fn f => SOME o f)
    val (test_fun, comp_time) = cpu_time "quickcheck compilation" (fn () => act (compile ctxt) ts)
    val _ = Quickcheck.add_timing comp_time current_result
  in
    (case test_fun of
      NONE =>
        (Quickcheck.message ctxt ("Conjecture is not executable with Quickcheck-" ^ name);
          !current_result)
    | SOME test_fun =>
        let
          val _ = Quickcheck.message ctxt ("Testing conjecture with Quickcheck-" ^ name ^ "...")
          fun test genuine_only enum =
            (case get_first (test_card_size test_fun genuine_only) enum of
              SOME ((card, _), (true, ts)) =>
                Quickcheck.add_response names (nth eval_terms (card - 1))
                  (SOME (true, ts)) current_result
            | SOME ((card, size), (false, ts)) =>
                if abort_potential then
                  Quickcheck.add_response names (nth eval_terms (card - 1))
                    (SOME (false, ts)) current_result
                else
                  let
                    val (ts1, ts2) = chop (length names) ts
                    val (eval_terms', _) = chop (length ts2) (nth eval_terms (card - 1))
                    val cex = SOME ((false, names ~~ ts1), eval_terms' ~~ ts2)
                  in
                    Quickcheck.message ctxt
                      (Pretty.string_of (Quickcheck.pretty_counterex ctxt false cex));
                    Quickcheck.message ctxt
                      "Quickcheck continues to find a genuine counterexample...";
                    test true (drop_prefix (fn x => not (x = (card, size))) enum)
                end
            | NONE => ())
        in (test genuine_only enumeration_card_size; !current_result) end)
  end

fun get_finite_types ctxt =
  fst (chop (Config.get ctxt Quickcheck.finite_type_size)
    [\<^typ>\<open>Enum.finite_1\<close>, \<^typ>\<open>Enum.finite_2\<close>, \<^typ>\<open>Enum.finite_3\<close>,
     \<^typ>\<open>Enum.finite_4\<close>, \<^typ>\<open>Enum.finite_5\<close>])

exception WELLSORTED of string

fun monomorphic_term ctxt insts default_T =
  (map_types o map_atyps)
    (fn T as TFree (v, S) =>
        let val T' = AList.lookup (op =) insts v |> the_default default_T in
          if Sign.of_sort (Proof_Context.theory_of ctxt) (T', S) then T'
          else
            raise WELLSORTED ("For instantiation with default_type " ^
              Syntax.string_of_typ ctxt default_T ^ ":\n" ^ Syntax.string_of_typ ctxt T' ^
              " to be substituted for variable " ^ Syntax.string_of_typ ctxt T ^
              " does not have sort " ^ Syntax.string_of_sort ctxt S)
        end
      | T => T)

datatype wellsorted_error = Wellsorted_Error of string | Term of term * term list


(* minimalistic preprocessing *)

fun strip_all (Const (\<^const_name>\<open>HOL.All\<close>, _) $ Abs (a, T, t)) =
      let val (a', t') = strip_all t
      in ((a, T) :: a', t') end
  | strip_all t = ([], t)

fun preprocess ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    val dest = HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of
    val rewrs =
      map (swap o dest) @{thms all_simps} @
        (map dest [@{thm not_ex}, @{thm not_all}, @{thm imp_conjL}, @{thm fun_eq_iff},
          @{thm bot_fun_def}, @{thm less_bool_def}])
    val t' = Pattern.rewrite_term thy rewrs [] (Object_Logic.atomize_term ctxt t)
    val (vs, body) = strip_all t'
    val vs' = Variable.variant_frees ctxt [t'] vs
  in subst_bounds (map Free (rev vs'), body) end


structure Subtype_Predicates = Generic_Data
(
  type T = (term * string) list
  val empty = []
  val extend = I
  fun merge data : T = AList.merge (op =) (K true) data
)

val register_predicate = Subtype_Predicates.map o AList.update (op =)

fun subtype_preprocess ctxt (T, (t, ts)) =
  let
    val preds = Subtype_Predicates.get (Context.Proof ctxt)
    fun matches (p $ _) = AList.defined Term.could_unify preds p
    fun get_match (p $ x) = Option.map (rpair x) (AList.lookup Term.could_unify preds p)
    fun subst_of (tyco, v as Free (x, repT)) =
      let
        val [(info, _)] = Typedef.get_info ctxt tyco
        val repT' = Logic.varifyT_global (#rep_type info)
        val substT = Sign.typ_match (Proof_Context.theory_of ctxt) (repT', repT) Vartab.empty
        val absT = Envir.subst_type substT (Logic.varifyT_global (#abs_type info))
      in (v, Const (#Rep_name info, absT --> repT) $ Free (x, absT)) end
    val (prems, concl) = strip_imp t
    val subst = map subst_of (map_filter get_match prems)
    val t' = Term.subst_free subst
     (fold_rev (curry HOLogic.mk_imp) (filter_out matches prems) concl)
  in (T, (t', ts)) end


(* instantiation of type variables with concrete types *)

fun instantiate_goals ctxt insts goals =
  let
    fun map_goal_and_eval_terms f (check_goal, eval_terms) = (f check_goal, map f eval_terms)
    val default_insts =
      if Config.get ctxt Quickcheck.finite_types
      then get_finite_types else Quickcheck.default_type
    val inst_goals =
      map (fn (check_goal, eval_terms) =>
        if not (null (Term.add_tfree_names check_goal [])) then
          map (fn T =>
            (pair (SOME T) o Term o apfst (preprocess ctxt))
              (map_goal_and_eval_terms (monomorphic_term ctxt insts T) (check_goal, eval_terms))
              handle WELLSORTED s => (SOME T, Wellsorted_Error s)) (default_insts ctxt)
        else [(NONE, Term (preprocess ctxt check_goal, eval_terms))]) goals
    val error_msg =
      cat_lines
        (maps (map_filter (fn (_, Term _) => NONE | (_, Wellsorted_Error s) => SOME s)) inst_goals)
    fun is_wellsorted_term (T, Term t) = SOME (T, t)
      | is_wellsorted_term (_, Wellsorted_Error _) = NONE
    val correct_inst_goals =
      (case map (map_filter is_wellsorted_term) inst_goals of
        [[]] => error error_msg
      | xs => xs)
    val _ = if Config.get ctxt Quickcheck.quiet then () else warning error_msg
  in correct_inst_goals end


(* compilation of testing functions *)

fun mk_safe_if genuine_only none (cond, then_t, else_t) genuine =
  let
    val T = fastype_of then_t
    val if_t = Const (\<^const_name>\<open>If\<close>, \<^typ>\<open>bool\<close> --> T --> T --> T)
  in
    Const (\<^const_name>\<open>Quickcheck_Random.catch_match\<close>, T --> T --> T) $
      (if_t $ cond $ then_t $ else_t genuine) $
      (if_t $ genuine_only $ none $ else_t false)
  end

fun collect_results _ [] results = results
  | collect_results f (t :: ts) results =
      let val result = f t in
        if Quickcheck.found_counterexample result then result :: results
        else collect_results f ts (result :: results)
      end

fun generator_test_goal_terms generator ctxt catch_code_errors insts goals =
  let
    val use_subtype = Config.get ctxt Quickcheck.use_subtype
    fun add_eval_term t ts = if is_Free t then ts else ts @ [t]
    fun add_equation_eval_terms (t, eval_terms) =
      (case try HOLogic.dest_eq (snd (strip_imp t)) of
        SOME (lhs, rhs) => (t, add_eval_term lhs (add_eval_term rhs eval_terms))
      | NONE => (t, eval_terms))
    fun test_term' goal =
      (case goal of
        [(NONE, t)] => test_term generator ctxt catch_code_errors t
      | ts => test_term_with_cardinality generator ctxt catch_code_errors (map snd ts))
    val goals' =
      instantiate_goals ctxt insts goals
      |> (if use_subtype then map (map (subtype_preprocess ctxt)) else I)
      |> map (map (apsnd add_equation_eval_terms))
  in
    if Config.get ctxt Quickcheck.finite_types then
      collect_results test_term' goals' []
    else collect_results (test_term generator ctxt catch_code_errors) (maps (map snd) goals') []
  end


(* defining functions *)

fun pat_completeness_auto ctxt =
  Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt

fun define_functions (mk_equations, termination_tac) prfx argnames names Ts =
  if define_foundationally andalso is_some termination_tac then
    let
      val eqs_t = mk_equations (map2 (fn name => fn T => Free (name, T)) names Ts)
    in
      Function.add_function
        (map (fn (name, T) => (Binding.concealed (Binding.name name), SOME T, NoSyn))
          (names ~~ Ts))
        (map (fn t => (((Binding.concealed Binding.empty, []), t), [], [])) eqs_t)
        Function_Common.default_config pat_completeness_auto
      #> snd
      #> (fn lthy => Function.prove_termination NONE (the termination_tac lthy) lthy)
      #> snd
    end
  else
    fold_map (fn (name, T) => Local_Theory.define
        ((Binding.concealed (Binding.name name), NoSyn),
          (apfst Binding.concealed Binding.empty_atts, mk_undefined T))
      #> apfst fst) (names ~~ Ts)
    #> (fn (consts, lthy) =>
      let
        val eqs_t = mk_equations consts
        val eqs = map (fn eq => Goal.prove lthy argnames [] eq
          (fn {context = ctxt, ...} => ALLGOALS (Skip_Proof.cheat_tac ctxt))) eqs_t
      in
        lthy
        |> fold_map (fn (name, eq) => Local_Theory.note
             (((Binding.qualify true prfx o Binding.qualify true name) (Binding.name "simps"), []), [eq]))
               (names ~~ eqs) 
        |-> (fn notes => Code.declare_default_eqns (map (rpair true) (maps snd notes)))
      end)


(** ensuring sort constraints **)

type instantiation =
  Old_Datatype_Aux.config -> Old_Datatype_Aux.descr -> (string * sort) list ->
    string list -> string -> string list * string list -> typ list * typ list -> theory -> theory

fun perhaps_constrain thy insts raw_vs =
  let
    fun meet (T, sort) = Sorts.meet_sort (Sign.classes_of thy) (Logic.varifyT_global T, sort)
    val vtab = Vartab.empty
      |> fold (fn (v, sort) => Vartab.update ((v, 0), sort)) raw_vs
      |> fold meet insts
  in SOME (fn (v, _) => (v, (the o Vartab.lookup vtab) (v, 0))) end
  handle Sorts.CLASS_ERROR _ => NONE

fun ensure_sort (((sort_vs, aux_sort), sort), (the_descr, instantiate)) config raw_tycos thy =
  (case try (the_descr thy) raw_tycos of
    NONE => thy
  | SOME (descr, raw_vs, tycos, prfx, (names, auxnames), raw_TUs) =>
    let
      val algebra = Sign.classes_of thy
      val vs = (map o apsnd) (curry (Sorts.inter_sort algebra) sort_vs) raw_vs
      fun insts_of sort constr = (map (rpair sort) o flat o maps snd o maps snd)
        (Old_Datatype_Aux.interpret_construction descr vs constr)
      val insts = insts_of sort { atyp = single, dtyp = (K o K o K) [] }
        @ insts_of aux_sort { atyp = K [], dtyp = K o K }
      val has_inst = exists (fn tyco => Sorts.has_instance algebra tyco sort) tycos
    in
      if has_inst then thy
      else
        (case perhaps_constrain thy insts vs of
          SOME constrain =>
            instantiate config descr
              (map constrain vs) tycos prfx (names, auxnames)
                ((apply2 o map o map_atyps) (fn TFree v => TFree (constrain v)) raw_TUs) thy
        | NONE => thy)
    end)

fun ensure_common_sort_datatype (sort, instantiate) =
  ensure_sort (((\<^sort>\<open>typerep\<close>, \<^sort>\<open>term_of\<close>), sort),
    (fn thy => BNF_LFP_Compat.the_descr thy compat_prefs, instantiate))

fun datatype_interpretation name =
  BNF_LFP_Compat.interpretation name compat_prefs o ensure_common_sort_datatype


(** generic parametric compilation **)

fun gen_mk_parametric_generator_expr ((mk_generator_expr, out_of_bounds), T) ctxt ts =
  let
    val if_t = Const (\<^const_name>\<open>If\<close>, \<^typ>\<open>bool\<close> --> T --> T --> T)
    fun mk_if (index, (t, eval_terms)) else_t =
      if_t $ (HOLogic.eq_const \<^typ>\<open>natural\<close> $ Bound 0 $ HOLogic.mk_number \<^typ>\<open>natural\<close> index) $
        (mk_generator_expr ctxt (t, eval_terms)) $ else_t
  in absdummy \<^typ>\<open>natural\<close> (fold_rev mk_if (1 upto (length ts) ~~ ts) out_of_bounds) end


(** post-processing of function terms **)

fun dest_fun_upd (Const (\<^const_name>\<open>fun_upd\<close>, _) $ t0 $ t1 $ t2) = (t0, (t1, t2))
  | dest_fun_upd t = raise TERM ("dest_fun_upd", [t])

fun mk_fun_upd T1 T2 (t1, t2) t =
  Const (\<^const_name>\<open>fun_upd\<close>, (T1 --> T2) --> T1 --> T2 --> T1 --> T2) $ t $ t1 $ t2

fun dest_fun_upds t =
  (case try dest_fun_upd t of
    NONE =>
      (case t of
        Abs (_, _, _) => ([], t)
      | _ => raise TERM ("dest_fun_upds", [t]))
  | SOME (t0, (t1, t2)) => apfst (cons (t1, t2)) (dest_fun_upds t0))

fun make_fun_upds T1 T2 (tps, t) = fold_rev (mk_fun_upd T1 T2) tps t

fun make_set T1 [] = Const (\<^const_abbrev>\<open>Set.empty\<close>, T1 --> \<^typ>\<open>bool\<close>)
  | make_set T1 ((_, \<^Const_>\<open>False\<close>) :: tps) = make_set T1 tps
  | make_set T1 ((t1, \<^Const_>\<open>True\<close>) :: tps) =
      Const (\<^const_name>\<open>insert\<close>, T1 --> (T1 --> \<^typ>\<open>bool\<close>) --> T1 --> \<^typ>\<open>bool\<close>) $
        t1 $ (make_set T1 tps)
  | make_set T1 ((_, t) :: _) = raise TERM ("make_set", [t])

fun make_coset T [] = Const (\<^const_abbrev>\<open>UNIV\<close>, T --> \<^typ>\<open>bool\<close>)
  | make_coset T tps =
    let
      val U = T --> \<^typ>\<open>bool\<close>
      fun invert \<^Const_>\<open>False\<close> = \<^Const>\<open>True\<close>
        | invert \<^Const_>\<open>True\<close> = \<^Const>\<open>False\<close>
    in
      Const (\<^const_name>\<open>Groups.minus_class.minus\<close>, U --> U --> U) $
        Const (\<^const_abbrev>\<open>UNIV\<close>, U) $ make_set T (map (apsnd invert) tps)
    end

fun make_map T1 T2 [] = Const (\<^const_abbrev>\<open>Map.empty\<close>, T1 --> T2)
  | make_map T1 T2 ((_, Const (\<^const_name>\<open>None\<close>, _)) :: tps) = make_map T1 T2 tps
  | make_map T1 T2 ((t1, t2) :: tps) = mk_fun_upd T1 T2 (t1, t2) (make_map T1 T2 tps)

fun post_process_term t =
  let
    fun map_Abs f t =
      (case t of
        Abs (x, T, t') => Abs (x, T, f t')
      | _ => raise TERM ("map_Abs", [t]))
    fun process_args t =
      (case strip_comb t of
        (c as Const (_, _), ts) => list_comb (c, map post_process_term ts))
  in
    (case fastype_of t of
      Type (\<^type_name>\<open>fun\<close>, [T1, T2]) =>
        (case try dest_fun_upds t of
          SOME (tps, t) =>
            (map (apply2 post_process_term) tps, map_Abs post_process_term t) |>
              (case T2 of
                \<^typ>\<open>bool\<close> =>
                  (case t of
                     Abs(_, _, \<^Const_>\<open>False\<close>) => fst #> rev #> make_set T1
                   | Abs(_, _, \<^Const_>\<open>True\<close>) => fst #> rev #> make_coset T1
                   | Abs(_, _, Const (\<^const_name>\<open>undefined\<close>, _)) => fst #> rev #> make_set T1
                   | _ => raise TERM ("post_process_term", [t]))
              | Type (\<^type_name>\<open>option\<close>, _) =>
                  (case t of
                    Abs(_, _, Const (\<^const_name>\<open>None\<close>, _)) => fst #> make_map T1 T2
                  | Abs(_, _, Const (\<^const_name>\<open>undefined\<close>, _)) => fst #> make_map T1 T2
                  | _ => make_fun_upds T1 T2)
              | _ => make_fun_upds T1 T2)
        | NONE => process_args t)
    | _ => process_args t)
  end

end
