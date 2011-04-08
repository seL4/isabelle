(*  Title:      HOL/Tools/Quickcheck/exhaustive_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Exhaustive generators for various types.
*)

signature EXHAUSTIVE_GENERATORS =
sig
  val compile_generator_expr:
    Proof.context -> (term * term list) list -> int list -> term list option * Quickcheck.report option
  val compile_generator_exprs: Proof.context -> term list -> (int -> term list option) list
  val compile_validator_exprs: Proof.context -> term list -> (int -> bool) list
  val put_counterexample: (unit -> int -> int -> term list option)
    -> Proof.context -> Proof.context
  val put_counterexample_batch: (unit -> (int -> term list option) list)
    -> Proof.context -> Proof.context
  val put_validator_batch: (unit -> (int -> bool) list) -> Proof.context -> Proof.context
  exception Counterexample of term list
  val smart_quantifier : bool Config.T
  val quickcheck_pretty : bool Config.T
  val setup: theory -> theory
end;

structure Exhaustive_Generators : EXHAUSTIVE_GENERATORS =
struct

(* dynamic options *)

val (smart_quantifier, setup_smart_quantifier) =
  Attrib.config_bool "quickcheck_smart_quantifier" (K true)

val (fast, setup_fast) =
  Attrib.config_bool "quickcheck_fast" (K true)
  
val (full_support, setup_full_support) =
  Attrib.config_bool "quickcheck_full_support" (K true)

val (quickcheck_pretty, setup_quickcheck_pretty) =
  Attrib.config_bool "quickcheck_pretty" (K true)
 
(** general term functions **)

fun mk_measure f =
  let
    val Type ("fun", [T, @{typ nat}]) = fastype_of f 
  in
    Const (@{const_name Wellfounded.measure},
      (T --> @{typ nat}) --> HOLogic.mk_prodT (T, T) --> @{typ bool})
    $ f
  end

fun mk_sumcases rT f (Type (@{type_name Sum_Type.sum}, [TL, TR])) =
  let
    val lt = mk_sumcases rT f TL
    val rt = mk_sumcases rT f TR
  in
    SumTree.mk_sumcase TL TR rT lt rt
  end
  | mk_sumcases _ f T = f T

fun mk_undefined T = Const(@{const_name undefined}, T)
  

(** abstract syntax **)

fun termifyT T = HOLogic.mk_prodT (T, @{typ "unit => Code_Evaluation.term"});

val size = @{term "i :: code_numeral"}
val size_pred = @{term "(i :: code_numeral) - 1"}
val size_ge_zero = @{term "(i :: code_numeral) > 0"}

fun test_function T = Free ("f", T --> @{typ "term list option"})
fun full_test_function T = Free ("f", termifyT T --> @{typ "term list option"})
fun fast_test_function T = Free ("f", T --> @{typ "unit"})

fun mk_none_continuation (x, y) =
  let
    val (T as Type(@{type_name "option"}, [T'])) = fastype_of x
  in
    Const (@{const_name "Quickcheck_Exhaustive.orelse"}, T --> T --> T) $ x $ y
  end

fun mk_unit_let (x, y) =
  Const (@{const_name "Let"}, @{typ "unit => (unit => unit) => unit"}) $ x $ (absdummy (@{typ unit}, y))
  
(** datatypes **)

(* constructing exhaustive generator instances on datatypes *)

exception FUNCTION_TYPE;

exception Counterexample of term list

val exhaustiveN = "exhaustive";
val full_exhaustiveN = "full_exhaustive";
val fast_exhaustiveN = "fast_exhaustive";

fun fast_exhaustiveT T = (T --> @{typ unit})
  --> @{typ code_numeral} --> @{typ unit}


fun exhaustiveT T = (T --> @{typ "Code_Evaluation.term list option"})
  --> @{typ code_numeral} --> @{typ "Code_Evaluation.term list option"}

fun full_exhaustiveT T = (termifyT T --> @{typ "Code_Evaluation.term list option"})
  --> @{typ code_numeral} --> @{typ "Code_Evaluation.term list option"}

fun check_allT T = (termifyT T --> @{typ "Code_Evaluation.term list option"})
  --> @{typ "Code_Evaluation.term list option"}


fun mk_fast_equations descr vs tycos fast_exhaustives (Ts, Us) =
  let
    fun mk_call T =
      let
        val fast_exhaustive =
          Const (@{const_name "Quickcheck_Exhaustive.fast_exhaustive_class.fast_exhaustive"}, fast_exhaustiveT T)
      in
        (T, fn t => fast_exhaustive $ absdummy (T, t) $ size_pred)
      end
    fun mk_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts)
        val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
      in
       (T, fn t => nth fast_exhaustives k $ absdummy (T, t) $ size_pred)
      end
    fun mk_consexpr simpleT (c, xs) =
      let
        val (Ts, fns) = split_list xs
        val constr = Const (c, Ts ---> simpleT)
        val bounds = map Bound (((length xs) - 1) downto 0)
        val term_bounds = map (fn x => Bound (2 * x)) (((length xs) - 1) downto 0)
        val start_term = fast_test_function simpleT $ list_comb (constr, bounds)
      in fold_rev (fn f => fn t => f t) fns start_term end
    fun mk_rhs exprs =
        @{term "If :: bool => unit => unit => unit"}
            $ size_ge_zero $ (foldr1 mk_unit_let exprs) $ @{term "()"}
    val rhss =
      Datatype_Aux.interpret_construction descr vs
        { atyp = mk_call, dtyp = mk_aux_call }
      |> (map o apfst) Type
      |> map (fn (T, cs) => map (mk_consexpr T) cs)
      |> map mk_rhs
    val lhss = map2 (fn t => fn T => t $ fast_test_function T $ size) fast_exhaustives (Ts @ Us)
    val eqs = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhss ~~ rhss)
  in
    eqs
  end
  
fun mk_equations descr vs tycos exhaustives (Ts, Us) =
  let
    fun mk_call T =
      let
        val exhaustive = Const (@{const_name "Quickcheck_Exhaustive.exhaustive_class.exhaustive"}, exhaustiveT T)
      in
        (T, fn t => exhaustive $ absdummy (T, t) $ size_pred)
      end
    fun mk_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts)
        val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
      in
       (T, fn t => nth exhaustives k $ absdummy (T, t) $ size_pred)
      end
    fun mk_consexpr simpleT (c, xs) =
      let
        val (Ts, fns) = split_list xs
        val constr = Const (c, Ts ---> simpleT)
        val bounds = map Bound (((length xs) - 1) downto 0)
        val term_bounds = map (fn x => Bound (2 * x)) (((length xs) - 1) downto 0)
        val start_term = test_function simpleT $ list_comb (constr, bounds)
      in fold_rev (fn f => fn t => f t) fns start_term end
    fun mk_rhs exprs =
        @{term "If :: bool => term list option => term list option => term list option"}
            $ size_ge_zero $ (foldr1 mk_none_continuation exprs) $ @{term "None :: term list option"}
    val rhss =
      Datatype_Aux.interpret_construction descr vs
        { atyp = mk_call, dtyp = mk_aux_call }
      |> (map o apfst) Type
      |> map (fn (T, cs) => map (mk_consexpr T) cs)
      |> map mk_rhs
    val lhss = map2 (fn t => fn T => t $ test_function T $ size) exhaustives (Ts @ Us)
    val eqs = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhss ~~ rhss)
  in
    eqs
  end
    
fun mk_full_equations descr vs tycos full_exhaustives (Ts, Us) =
  let
    fun mk_call T =
      let
        val full_exhaustive = Const (@{const_name "Quickcheck_Exhaustive.exhaustive_class.full_exhaustive"}, full_exhaustiveT T)
      in
        (T, (fn t => full_exhaustive $
          (HOLogic.split_const (T, @{typ "unit => Code_Evaluation.term"}, @{typ "Code_Evaluation.term list option"})
          $ absdummy (T, absdummy (@{typ "unit => Code_Evaluation.term"}, t))) $ size_pred))
      end
    fun mk_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts)
        val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
      in
       (T, (fn t => nth full_exhaustives k $
          (HOLogic.split_const (T, @{typ "unit => Code_Evaluation.term"}, @{typ "Code_Evaluation.term list option"})
            $ absdummy (T, absdummy (@{typ "unit => Code_Evaluation.term"}, t))) $ size_pred))
      end
    fun mk_consexpr simpleT (c, xs) =
      let
        val (Ts, fns) = split_list xs
        val constr = Const (c, Ts ---> simpleT)
        val bounds = map (fn x => Bound (2 * x + 1)) (((length xs) - 1) downto 0)
        val term_bounds = map (fn x => Bound (2 * x)) (((length xs) - 1) downto 0)
        val Eval_App = Const ("Code_Evaluation.App", HOLogic.termT --> HOLogic.termT --> HOLogic.termT)
        val Eval_Const = Const ("Code_Evaluation.Const", HOLogic.literalT --> @{typ typerep} --> HOLogic.termT)
        val term = fold (fn u => fn t => Eval_App $ t $ (u $ @{term "()"}))
          bounds (Eval_Const $ HOLogic.mk_literal c $ HOLogic.mk_typerep (Ts ---> simpleT))
        val start_term = full_test_function simpleT $ 
        (HOLogic.pair_const simpleT @{typ "unit => Code_Evaluation.term"}
          $ (list_comb (constr, bounds)) $ absdummy (@{typ unit}, term))
      in fold_rev (fn f => fn t => f t) fns start_term end
    fun mk_rhs exprs =
        @{term "If :: bool => term list option => term list option => term list option"}
            $ size_ge_zero $ (foldr1 mk_none_continuation exprs) $ @{term "None :: term list option"}
    val rhss =
      Datatype_Aux.interpret_construction descr vs
        { atyp = mk_call, dtyp = mk_aux_call }
      |> (map o apfst) Type
      |> map (fn (T, cs) => map (mk_consexpr T) cs)
      |> map mk_rhs
    val lhss = map2 (fn t => fn T => t $ full_test_function T $ size) full_exhaustives (Ts @ Us);
    val eqs = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhss ~~ rhss)
  in
    eqs
  end

(* foundational definition with the function package *)

val less_int_pred = @{lemma "i > 0 ==> Code_Numeral.nat_of ((i :: code_numeral) - 1) < Code_Numeral.nat_of i" by auto}

fun mk_single_measure T = HOLogic.mk_comp (@{term "Code_Numeral.nat_of"},
    Const (@{const_name "Product_Type.snd"}, T --> @{typ "code_numeral"}))

fun mk_termination_measure T =
  let
    val T' = fst (HOLogic.dest_prodT (HOLogic.dest_setT T))
  in
    mk_measure (mk_sumcases @{typ nat} mk_single_measure T')
  end

fun termination_tac ctxt = 
  Function_Relation.relation_tac ctxt mk_termination_measure 1
  THEN rtac @{thm wf_measure} 1
  THEN (REPEAT_DETERM (Simplifier.asm_full_simp_tac 
    (HOL_basic_ss addsimps [@{thm in_measure}, @{thm o_def}, @{thm snd_conv},
     @{thm nat_mono_iff}, less_int_pred] @ @{thms sum.cases}) 1))

(* creating the instances *)

fun instantiate_exhaustive_datatype config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  let
    val _ = Datatype_Aux.message config "Creating exhaustive generators...";
    val exhaustivesN = map (prefix (exhaustiveN ^ "_")) (names @ auxnames)
    val full_exhaustivesN = map (prefix (full_exhaustiveN ^ "_")) (names @ auxnames)
  in
    thy
    |> Class.instantiation (tycos, vs, @{sort exhaustive})
    |> Quickcheck_Common.define_functions
        (fn exhaustives => mk_equations descr vs tycos exhaustives (Ts, Us), SOME termination_tac)
        prfx ["f", "i"] exhaustivesN (map exhaustiveT (Ts @ Us))
    |> Quickcheck_Common.define_functions
        (fn full_exhaustives => mk_full_equations descr vs tycos full_exhaustives (Ts, Us),
        SOME termination_tac)
        prfx ["f", "i"] full_exhaustivesN (map full_exhaustiveT (Ts @ Us))
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end handle FUNCTION_TYPE =>
    (Datatype_Aux.message config
      "Creation of exhaustive generators failed because the datatype contains a function type";
    thy)

fun instantiate_fast_exhaustive_datatype config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  let
    val _ = Datatype_Aux.message config "Creating fast exhaustive generators...";
    val fast_exhaustivesN = map (prefix (fast_exhaustiveN ^ "_")) (names @ auxnames)
  in
    thy
    |> Class.instantiation (tycos, vs, @{sort fast_exhaustive})
    |> Quickcheck_Common.define_functions
        (fn exhaustives => mk_fast_equations descr vs tycos exhaustives (Ts, Us), SOME termination_tac)
        prfx ["f", "i"] fast_exhaustivesN (map fast_exhaustiveT (Ts @ Us))
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end handle FUNCTION_TYPE =>
    (Datatype_Aux.message config
      "Creation of exhaustive generators failed because the datatype contains a function type";
    thy)
       
(* constructing bounded_forall instances on datatypes *)

val bounded_forallN = "bounded_forall";

fun bounded_forallT T = (T --> @{typ bool}) --> @{typ code_numeral} --> @{typ bool}

fun mk_bounded_forall_equations descr vs tycos bounded_foralls (Ts, Us) =
  let
    fun mk_call T =
      let
        val bounded_forall =
          Const (@{const_name "Quickcheck_Exhaustive.bounded_forall_class.bounded_forall"},
            bounded_forallT T)
      in
        (T, (fn t => bounded_forall $ absdummy (T, t) $ size_pred))
      end
    fun mk_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts)
        val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
      in
        (T, (fn t => nth bounded_foralls k $ absdummy (T, t) $ size_pred))
      end
    fun mk_consexpr simpleT (c, xs) =
      let
        val (Ts, fns) = split_list xs
        val constr = Const (c, Ts ---> simpleT)
        val bounds = map Bound (((length xs) - 1) downto 0)
        val start_term = Free ("P", simpleT --> @{typ bool}) $ list_comb (constr, bounds)
      in fold_rev (fn f => fn t => f t) fns start_term end
    fun mk_rhs exprs =
      @{term "If :: bool => bool => bool => bool"} $ size_ge_zero $
        (foldr1 HOLogic.mk_conj exprs) $ @{term "True"}
    val rhss =
      Datatype_Aux.interpret_construction descr vs
        { atyp = mk_call, dtyp = mk_aux_call }
      |> (map o apfst) Type
      |> map (fn (T, cs) => map (mk_consexpr T) cs)
      |> map mk_rhs
    val lhss =
      map2 (fn t => fn T => t $ Free ("P", T --> @{typ bool}) $ size) bounded_foralls (Ts @ Us)
    val eqs = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhss ~~ rhss)
  in
    eqs
  end

(* creating the bounded_forall instances *)

fun instantiate_bounded_forall_datatype config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  let
    val _ = Datatype_Aux.message config "Creating bounded universal quantifiers...";
    val bounded_forallsN = map (prefix (bounded_forallN ^ "_")) (names @ auxnames);
  in
    thy
    |> Class.instantiation (tycos, vs, @{sort bounded_forall})
    |> Quickcheck_Common.define_functions
        (fn bounded_foralls => 
          mk_bounded_forall_equations descr vs tycos bounded_foralls (Ts, Us), NONE)
        prfx ["P", "i"] bounded_forallsN (map bounded_forallT (Ts @ Us))
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end handle FUNCTION_TYPE =>
    (Datatype_Aux.message config
      "Creation of bounded universal quantifiers failed because the datatype contains a function type";
    thy)
    
(** building and compiling generator expressions **)

fun mk_fast_generator_expr ctxt (t, eval_terms) =
  let
    val thy = ProofContext.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    val ([depth_name], ctxt'') = Variable.variant_fixes ["depth"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    val return = @{term "throw_Counterexample :: term list => unit"} $
      (HOLogic.mk_list @{typ "term"}
        (map (fn t => HOLogic.mk_term_of (fastype_of t) t) (frees @ eval_terms)))
    fun mk_exhaustive_closure (free as Free (_, T)) t =
      Const (@{const_name "Quickcheck_Exhaustive.fast_exhaustive_class.fast_exhaustive"}, fast_exhaustiveT T)
        $ lambda free t $ depth
    val none_t = @{term "()"}
    fun mk_safe_if (cond, then_t, else_t) =
      @{term "If :: bool => unit => unit => unit"} $ cond $ then_t $ else_t
    fun lookup v = the (AList.lookup (op =) (names ~~ frees) v)
    fun mk_naive_test_term t =
      fold_rev mk_exhaustive_closure frees (mk_safe_if (t, none_t, return)) 
    fun mk_smart_test_term' concl bound_vars assms =
      let
        fun vars_of t = subtract (op =) bound_vars (Term.add_free_names t [])
        val (vars, check) =
          case assms of [] => (vars_of concl, (concl, none_t, return))
            | assm :: assms => (vars_of assm, (assm,
                mk_smart_test_term' concl (union (op =) (vars_of assm) bound_vars) assms, none_t))
      in
        fold_rev mk_exhaustive_closure (map lookup vars) (mk_safe_if check)
      end
    fun mk_smart_test_term t =
      let
        val (assms, concl) = Quickcheck_Common.strip_imp t
      in
        mk_smart_test_term' concl [] assms
      end
    val mk_test_term =
      if Config.get ctxt smart_quantifier then mk_smart_test_term else mk_naive_test_term 
  in lambda depth (@{term "catch_Counterexample :: unit => term list option"} $ mk_test_term t) end

fun mk_generator_expr ctxt (t, eval_terms) =
  let
    val thy = ProofContext.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    val ([depth_name], ctxt'') = Variable.variant_fixes ["depth"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    val return = @{term "Some :: term list => term list option"} $
      (HOLogic.mk_list @{typ "term"}
        (map (fn t => HOLogic.mk_term_of (fastype_of t) t) (frees @ eval_terms)))
    fun mk_exhaustive_closure (free as Free (_, T)) t =
      Const (@{const_name "Quickcheck_Exhaustive.exhaustive_class.exhaustive"}, exhaustiveT T)
        $ lambda free t $ depth
    val none_t = @{term "None :: term list option"}
    fun mk_safe_if (cond, then_t, else_t) =
      @{term "Quickcheck_Exhaustive.catch_match :: term list option => term list option => term list option"} $
        (@{term "If :: bool => term list option => term list option => term list option"}
        $ cond $ then_t $ else_t) $ none_t;
    fun lookup v = the (AList.lookup (op =) (names ~~ frees) v)
    fun mk_naive_test_term t =
      fold_rev mk_exhaustive_closure frees (mk_safe_if (t, none_t, return)) 
    fun mk_smart_test_term' concl bound_vars assms =
      let
        fun vars_of t = subtract (op =) bound_vars (Term.add_free_names t [])
        val (vars, check) =
          case assms of [] => (vars_of concl, (concl, none_t, return))
            | assm :: assms => (vars_of assm, (assm,
                mk_smart_test_term' concl (union (op =) (vars_of assm) bound_vars) assms, none_t))
      in
        fold_rev mk_exhaustive_closure (map lookup vars) (mk_safe_if check)
      end
    fun mk_smart_test_term t =
      let
        val (assms, concl) = Quickcheck_Common.strip_imp t
      in
        mk_smart_test_term' concl [] assms
      end
    val mk_test_term =
      if Config.get ctxt smart_quantifier then mk_smart_test_term else mk_naive_test_term 
  in lambda depth (mk_test_term t) end

fun mk_full_generator_expr ctxt (t, eval_terms) =
  let
    val thy = ProofContext.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    val ([depth_name], ctxt'') = Variable.variant_fixes ["depth"] ctxt'
    val (term_names, ctxt''') = Variable.variant_fixes (map (prefix "t_") names) ctxt''
    val depth = Free (depth_name, @{typ code_numeral})
    val term_vars = map (fn n => Free (n, @{typ "unit => term"})) term_names
    val terms = HOLogic.mk_list @{typ term} (map (fn v => v $ @{term "()"}) term_vars)
    val appendC = @{term "List.append :: term list => term list => term list"}  
    val return = @{term "Some :: term list => term list option"} $ (appendC $ terms $
      (HOLogic.mk_list @{typ "term"} (map (fn t => HOLogic.mk_term_of (fastype_of t) t) eval_terms)))
    fun mk_exhaustive_closure (free as Free (_, T), term_var) t =
      if Sign.of_sort thy (T, @{sort enum}) then
        Const (@{const_name "Quickcheck_Exhaustive.check_all_class.check_all"}, check_allT T)
          $ (HOLogic.split_const (T, @{typ "unit => term"}, @{typ "term list option"}) 
            $ lambda free (lambda term_var t))
      else
        Const (@{const_name "Quickcheck_Exhaustive.exhaustive_class.exhaustive"}, exhaustiveT T)
          $ (HOLogic.split_const (T, @{typ "unit => term"}, @{typ "term list option"})
            $ lambda free (lambda term_var t)) $ depth
    val none_t = @{term "None :: term list option"}
    fun mk_safe_if (cond, then_t, else_t) =
      @{term "Quickcheck_Exhaustive.catch_match :: term list option => term list option => term list option"} $
        (@{term "If :: bool => term list option => term list option => term list option"}
        $ cond $ then_t $ else_t) $ none_t;
    fun lookup v = the (AList.lookup (op =) (names ~~ (frees ~~ term_vars)) v)
    fun mk_naive_test_term t =
      fold_rev mk_exhaustive_closure (frees ~~ term_vars) (mk_safe_if (t, none_t, return)) 
    fun mk_smart_test_term' concl bound_vars assms =
      let
        fun vars_of t = subtract (op =) bound_vars (Term.add_free_names t [])
        val (vars, check) =
          case assms of [] => (vars_of concl, (concl, none_t, return))
            | assm :: assms => (vars_of assm, (assm,
                mk_smart_test_term' concl (union (op =) (vars_of assm) bound_vars) assms, none_t))
      in
        fold_rev mk_exhaustive_closure (map lookup vars) (mk_safe_if check)
      end
    fun mk_smart_test_term t =
      let
        val (assms, concl) = Quickcheck_Common.strip_imp t
      in
        mk_smart_test_term' concl [] assms
      end
    val mk_test_term =
      if Config.get ctxt smart_quantifier then mk_smart_test_term else mk_naive_test_term 
  in lambda depth (mk_test_term t) end

fun mk_parametric_generator_expr mk_generator_expr =
  Quickcheck_Common.gen_mk_parametric_generator_expr 
    ((mk_generator_expr, absdummy (@{typ "code_numeral"}, @{term "None :: term list option"})),
      @{typ "code_numeral => term list option"})

fun mk_validator_expr ctxt t =
  let
    fun bounded_forallT T = (T --> @{typ bool}) --> @{typ code_numeral} --> @{typ bool}
    val thy = ProofContext.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val ([depth_name], ctxt'') = Variable.variant_fixes ["depth"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    fun mk_bounded_forall (s, T) t =
      Const (@{const_name "Quickcheck_Exhaustive.bounded_forall_class.bounded_forall"}, bounded_forallT T)
        $ lambda (Free (s, T)) t $ depth
    fun mk_implies (cond, then_t) =
      @{term "If :: bool => bool => bool => bool"} $ cond $ then_t $ @{term True}
    fun mk_naive_test_term t = fold_rev mk_bounded_forall (Term.add_frees t []) t 
    fun mk_smart_test_term' concl bound_frees assms =
      let
        fun vars_of t = subtract (op =) bound_frees (Term.add_frees t [])
        val (vars, check) =
          case assms of [] => (vars_of concl, concl)
            | assm :: assms => (vars_of assm, mk_implies (assm,
                mk_smart_test_term' concl (union (op =) (vars_of assm) bound_frees) assms))
      in
        fold_rev mk_bounded_forall vars check
      end
    fun mk_smart_test_term t =
      let
        val (assms, concl) = Quickcheck_Common.strip_imp t
      in
        mk_smart_test_term' concl [] assms
      end
    val mk_test_term =
      if Config.get ctxt smart_quantifier then mk_smart_test_term else mk_naive_test_term 
  in lambda depth (mk_test_term t) end


(** generator compiliation **)

structure Counterexample = Proof_Data
(
  type T = unit -> int -> int -> term list option
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Counterexample"
);
val put_counterexample = Counterexample.put;

structure Counterexample_Batch = Proof_Data
(
  type T = unit -> (int -> term list option) list
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Counterexample"
);
val put_counterexample_batch = Counterexample_Batch.put;

structure Validator_Batch = Proof_Data
(
  type T = unit -> (int -> bool) list
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Counterexample"
);
val put_validator_batch = Validator_Batch.put;


val target = "Quickcheck";
  
fun compile_generator_expr ctxt ts =
  let
    val thy = ProofContext.theory_of ctxt
    val mk_generator_expr = 
      if Config.get ctxt fast then mk_fast_generator_expr
      else if Config.get ctxt full_support then mk_full_generator_expr else mk_generator_expr
    val t' = mk_parametric_generator_expr mk_generator_expr ctxt ts;
    val compile = Code_Runtime.dynamic_value_strict
      (Counterexample.get, put_counterexample, "Exhaustive_Generators.put_counterexample")
      thy (SOME target) (fn proc => fn g =>
        fn card => fn size => g card size |> (Option.map o map) proc) t' []
  in
    fn [card, size] => rpair NONE (compile card size |> 
      (if Config.get ctxt quickcheck_pretty then
        Option.map (map Quickcheck_Common.post_process_term) else I))
  end;
 
fun compile_generator_exprs ctxt ts =
  let
    val thy = ProofContext.theory_of ctxt
    val ts' = map (fn t => mk_generator_expr ctxt (t, [])) ts;
    val compiles = Code_Runtime.dynamic_value_strict
      (Counterexample_Batch.get, put_counterexample_batch,
        "Exhaustive_Generators.put_counterexample_batch")
      thy (SOME target) (fn proc => map (fn g => g #> (Option.map o map) proc))
      (HOLogic.mk_list @{typ "code_numeral => term list option"} ts') []
  in
    map (fn compile => fn size => compile size
      |> Option.map (map Quickcheck_Common.post_process_term)) compiles
  end;

fun compile_validator_exprs ctxt ts =
  let
    val thy = ProofContext.theory_of ctxt
    val ts' = map (mk_validator_expr ctxt) ts
  in
    Code_Runtime.dynamic_value_strict
      (Validator_Batch.get, put_validator_batch, "Exhaustive_Generators.put_validator_batch")
      thy (SOME target) (K I) (HOLogic.mk_list @{typ "code_numeral => bool"} ts') []
  end;

(** setup **)

val setup =
  Datatype.interpretation (Quickcheck_Common.ensure_sort_datatype
      (((@{sort typerep}, @{sort term_of}), @{sort exhaustive}), instantiate_exhaustive_datatype))
  #> Datatype.interpretation (Quickcheck_Common.ensure_sort_datatype
      (((@{sort type}, @{sort type}), @{sort bounded_forall}), instantiate_bounded_forall_datatype))
  #> Datatype.interpretation (Quickcheck_Common.ensure_sort_datatype
      (((@{sort typerep}, @{sort term_of}), @{sort fast_exhaustive}), instantiate_fast_exhaustive_datatype))
  #> setup_smart_quantifier
  #> setup_full_support
  #> setup_fast
  #> setup_quickcheck_pretty
  #> Context.theory_map (Quickcheck.add_generator ("exhaustive", compile_generator_expr))
  #> Context.theory_map (Quickcheck.add_batch_generator ("exhaustive", compile_generator_exprs))
  #> Context.theory_map (Quickcheck.add_batch_validator ("exhaustive", compile_validator_exprs));

end;
