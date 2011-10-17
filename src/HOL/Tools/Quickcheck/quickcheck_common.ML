(*  Title:      HOL/Tools/Quickcheck/quickcheck_common.ML
    Author:     Florian Haftmann, Lukas Bulwahn, TU Muenchen

Common functions for quickcheck's generators.
*)

signature QUICKCHECK_COMMON =
sig
  val strip_imp : term -> (term list * term)
  val define_functions : ((term list -> term list) * (Proof.context -> tactic) option)
    -> string -> string list -> string list -> typ list -> Proof.context -> Proof.context 
  val perhaps_constrain: theory -> (typ * sort) list -> (string * sort) list
    -> (string * sort -> string * sort) option
  val instantiate_goals: Proof.context -> (string * typ) list -> (term * term list) list
    -> (typ option * (term * term list)) list list
  val collect_results : ('a -> Quickcheck.result) -> 'a list -> Quickcheck.result list -> Quickcheck.result list
  type compile_generator =
    Proof.context -> (term * term list) list -> int list -> term list option * Quickcheck.report option
  val generator_test_goal_terms : compile_generator -> Proof.context -> bool * bool
    -> (string * typ) list -> (term * term list) list -> Quickcheck.result list
  val ensure_sort_datatype:
    ((sort * sort) * sort) * (Datatype.config -> Datatype.descr -> (string * sort) list
      -> string list -> string -> string list * string list -> typ list * typ list -> theory -> theory)
    -> Datatype.config -> string list -> theory -> theory
  val gen_mk_parametric_generator_expr :
   (((Proof.context -> term * term list -> term) * term) * typ)
     -> Proof.context -> (term * term list) list -> term
  val mk_fun_upd : typ -> typ -> term * term -> term -> term
  val post_process_term : term -> term
  val test_term : compile_generator -> Proof.context -> bool * bool -> term * term list -> Quickcheck.result
end;

structure Quickcheck_Common : QUICKCHECK_COMMON =
struct

(* static options *)

val define_foundationally = false

(* HOLogic's term functions *)

fun strip_imp (Const(@{const_name HOL.implies},_) $ A $ B) = apfst (cons A) (strip_imp B)
  | strip_imp A = ([], A)

fun mk_undefined T = Const(@{const_name undefined}, T)

(* testing functions: testing with increasing sizes (and cardinalities) *)

type compile_generator =
  Proof.context -> (term * term list) list -> int list -> term list option * Quickcheck.report option

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

fun test_term compile ctxt (limit_time, is_interactive) (t, eval_terms) =
  let
    val _ = check_test_term t
    val names = Term.add_free_names t []
    val current_size = Unsynchronized.ref 0
    val current_result = Unsynchronized.ref Quickcheck.empty_result 
    fun excipit () =
      "Quickcheck ran out of time while testing at size " ^ string_of_int (!current_size)
    fun with_size test_fun k =
      if k > Config.get ctxt Quickcheck.size then
        NONE
      else
        let
          val _ = Quickcheck.message ctxt ("Test data size: " ^ string_of_int k)
          val _ = current_size := k
          val ((result, report), timing) =
            cpu_time ("size " ^ string_of_int k) (fn () => test_fun [1, k - 1])
          val _ = Quickcheck.add_timing timing current_result
          val _ = Quickcheck.add_report k report current_result
        in
          case result of NONE => with_size test_fun (k + 1) | SOME q => SOME q
        end;
  in
    (*limit (seconds (Config.get ctxt timeout)) (limit_time, is_interactive) (fn () =>*)(
      let
        val (test_fun, comp_time) = cpu_time "quickcheck compilation"
          (fn () => compile ctxt [(t, eval_terms)]);
        val _ = Quickcheck.add_timing comp_time current_result
        val (response, exec_time) =
          cpu_time "quickcheck execution" (fn () => with_size test_fun 1)
        val _ = Quickcheck.add_response names eval_terms response current_result
        val _ = Quickcheck.add_timing exec_time current_result
      in !current_result end)
(*    (fn () => (message (excipit ()); !current_result)) ()*)
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
        Option.map (map (fn test_fun => TimeLimit.timeLimit (seconds (Config.get ctxt Quickcheck.timeout))
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
        Option.map (map (fn test_fun => TimeLimit.timeLimit (seconds (Config.get ctxt Quickcheck.timeout))
              (fn () => with_size test_fun 1) ()
             handle TimeLimit.TimeOut => NONE)) test_funs)
  in
    (Option.map (map2 (fn names => Option.map (fn ts => names ~~ ts)) namess) results,
      [comp_time, exec_time])
  end


fun test_term_with_increasing_cardinality compile ctxt (limit_time, is_interactive) ts =
  let
    val thy = Proof_Context.theory_of ctxt
    val (ts', eval_terms) = split_list ts
    val _ = map check_test_term ts'
    val names = Term.add_free_names (hd ts') []
    val Ts = map snd (Term.add_frees (hd ts') [])
    val current_result = Unsynchronized.ref Quickcheck.empty_result
    fun test_card_size test_fun (card, size) =
      (* FIXME: why decrement size by one? *)
      let
        val (ts, timing) =
          cpu_time ("size " ^ string_of_int size ^ " and card " ^ string_of_int card)
            (fn () => fst (test_fun [card, size - 1]))
        val _ = Quickcheck.add_timing timing current_result
      in
        Option.map (pair card) ts
      end
    val enumeration_card_size =
      if forall (fn T => Sign.of_sort thy (T,  ["Enum.enum"])) Ts then
        (* size does not matter *)
        map (rpair 0) (1 upto (length ts))
      else
        (* size does matter *)
        map_product pair (1 upto (length ts)) (1 upto (Config.get ctxt Quickcheck.size))
        |> sort (fn ((c1, s1), (c2, s2)) => int_ord ((c1 + s1), (c2 + s2)))
  in
    (*limit (seconds (Config.get ctxt timeout)) (limit_time, is_interactive) (fn () =>*)(
      let
        val (test_fun, comp_time) = cpu_time "quickcheck compilation" (fn () => compile ctxt ts)
        val _ = Quickcheck.add_timing comp_time current_result     
        val _ = case get_first (test_card_size test_fun) enumeration_card_size of
          SOME (card, ts) => Quickcheck.add_response names (nth eval_terms (card - 1)) (SOME ts) current_result
        | NONE => ()
      in !current_result end)
      (*(fn () => (message "Quickcheck ran out of time"; !current_result)) ()*)
  end

fun get_finite_types ctxt =
  fst (chop (Config.get ctxt Quickcheck.finite_type_size)
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
      if Config.get lthy Quickcheck.finite_types then (get_finite_types lthy) else (Quickcheck.default_type lthy)
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
    val _ = if Config.get lthy Quickcheck.quiet then () else warning error_msg
  in
    correct_inst_goals
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

fun add_equation_eval_terms (t, eval_terms) =
  case try HOLogic.dest_eq (snd (strip_imp t)) of
    SOME (lhs, rhs) => (t, eval_terms @ [rhs, lhs])
  | NONE => (t, eval_terms)

fun generator_test_goal_terms compile ctxt (limit_time, is_interactive) insts goals =
  let
    fun test_term' goal =
      case goal of
        [(NONE, t)] => test_term compile ctxt (limit_time, is_interactive) t
      | ts => test_term_with_increasing_cardinality compile ctxt (limit_time, is_interactive) (map snd ts)
    val goals' = instantiate_goals ctxt insts goals
      |> map (map (apsnd add_equation_eval_terms))
  in
    if Config.get ctxt Quickcheck.finite_types then
      collect_results test_term' goals' []
    else
      collect_results (test_term compile ctxt (limit_time, is_interactive))
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
      #> Local_Theory.restore
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
        ((Binding.conceal (Binding.qualify true prfx
           (Binding.qualify true name (Binding.name "simps"))),
           Code.add_default_eqn_attrib :: map (Attrib.internal o K)
             [Simplifier.simp_add, Nitpick_Simps.add]), [eq]) #> snd) (names ~~ eqs) lthy
      end)

(** ensuring sort constraints **)

fun perhaps_constrain thy insts raw_vs =
  let
    fun meet (T, sort) = Sorts.meet_sort (Sign.classes_of thy) 
      (Logic.varifyT_global T, sort);
    val vtab = Vartab.empty
      |> fold (fn (v, sort) => Vartab.update ((v, 0), sort)) raw_vs
      |> fold meet insts;
  in SOME (fn (v, _) => (v, (the o Vartab.lookup vtab) (v, 0)))
  end handle Sorts.CLASS_ERROR _ => NONE;

fun ensure_sort_datatype (((sort_vs, aux_sort), sort), instantiate_datatype) config raw_tycos thy =
  let
    val algebra = Sign.classes_of thy;
    val (descr, raw_vs, tycos, prfx, (names, auxnames), raw_TUs) = Datatype.the_descr thy raw_tycos
    val vs = (map o apsnd) (curry (Sorts.inter_sort algebra) sort_vs) raw_vs
    fun insts_of sort constr  = (map (rpair sort) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr vs constr)
    val insts = insts_of sort  { atyp = single, dtyp = (K o K o K) [] }
      @ insts_of aux_sort { atyp = K [], dtyp = K o K }
    val has_inst = exists (fn tyco => can (Sorts.mg_domain algebra tyco) sort) tycos;
  in if has_inst then thy
    else case perhaps_constrain thy insts vs
     of SOME constrain => instantiate_datatype config descr
          (map constrain vs) tycos prfx (names, auxnames)
            ((pairself o map o map_atyps) (fn TFree v => TFree (constrain v)) raw_TUs) thy
      | NONE => thy
  end;
  
(** generic parametric compilation **)

fun gen_mk_parametric_generator_expr ((mk_generator_expr, out_of_bounds), T) ctxt ts =
  let
    val if_t = Const (@{const_name "If"}, @{typ bool} --> T --> T --> T)
    fun mk_if (index, (t, eval_terms)) else_t =
      if_t $ (HOLogic.eq_const @{typ code_numeral} $ Bound 0 $ HOLogic.mk_number @{typ code_numeral} index) $
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
