(*  Title:      HOL/Tools/Quickcheck/exhaustive_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Exhaustive generators for various types.
*)

signature EXHAUSTIVE_GENERATORS =
sig
  val compile_generator_expr:
    Proof.context -> (term * term list) list -> int list -> (bool * term list) option * Quickcheck.report option
  val compile_generator_exprs: Proof.context -> term list -> (int -> term list option) list
  val compile_validator_exprs: Proof.context -> term list -> (int -> bool) list
  val put_counterexample: (unit -> int -> int -> (bool * term list) option)
    -> Proof.context -> Proof.context
  val put_counterexample_batch: (unit -> (int -> term list option) list)
    -> Proof.context -> Proof.context
  val put_validator_batch: (unit -> (int -> bool) list) -> Proof.context -> Proof.context
  exception Counterexample of term list
  val smart_quantifier : bool Config.T
  val quickcheck_pretty : bool Config.T
  val setup_exhaustive_datatype_interpretation : theory -> theory
  val setup: theory -> theory
end;

structure Exhaustive_Generators : EXHAUSTIVE_GENERATORS =
struct

(* basics *)

(** dynamic options **)

val smart_quantifier = Attrib.setup_config_bool @{binding quickcheck_smart_quantifier} (K true)
val fast = Attrib.setup_config_bool @{binding quickcheck_fast} (K false)
val bounded_forall = Attrib.setup_config_bool @{binding quickcheck_bounded_forall} (K false)
val full_support = Attrib.setup_config_bool @{binding quickcheck_full_support} (K true)
val quickcheck_pretty = Attrib.setup_config_bool @{binding quickcheck_pretty} (K true)
 
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

(** abstract syntax **)

fun termifyT T = HOLogic.mk_prodT (T, @{typ "unit => Code_Evaluation.term"});

val size = @{term "i :: code_numeral"}
val size_pred = @{term "(i :: code_numeral) - 1"}
val size_ge_zero = @{term "(i :: code_numeral) > 0"}

fun mk_none_continuation (x, y) =
  let
    val (T as Type(@{type_name "option"}, [T'])) = fastype_of x
  in
    Const (@{const_name "Quickcheck_Exhaustive.orelse"}, T --> T --> T) $ x $ y
  end

fun mk_unit_let (x, y) =
  Const (@{const_name "Let"}, @{typ "unit => (unit => unit) => unit"}) $ x $ absdummy @{typ unit} y

fun mk_if (b, t, e) =
  let
    val T = fastype_of t
  in Const (@{const_name "HOL.If"}, @{typ bool} --> T --> T --> T) $ b $ t $ e end

(* handling inductive datatypes *)

(** constructing generator instances **)

exception FUNCTION_TYPE;

exception Counterexample of term list

val resultT =  @{typ "(bool * term list) option"};

val exhaustiveN = "exhaustive";
val full_exhaustiveN = "full_exhaustive";
val fast_exhaustiveN = "fast_exhaustive";
val bounded_forallN = "bounded_forall";

fun fast_exhaustiveT T = (T --> @{typ unit})
  --> @{typ code_numeral} --> @{typ unit}

fun exhaustiveT T = (T --> resultT) --> @{typ code_numeral} --> resultT

fun bounded_forallT T = (T --> @{typ bool}) --> @{typ code_numeral} --> @{typ bool}

fun full_exhaustiveT T = (termifyT T --> resultT) --> @{typ code_numeral} --> resultT

fun check_allT T = (termifyT T --> resultT) --> resultT

fun mk_equation_terms generics (descr, vs, Ts) =
  let
    val (mk_call, mk_aux_call, mk_consexpr, mk_rhs, test_function, exhaustives) = generics
    val rhss =
      Datatype_Aux.interpret_construction descr vs
        { atyp = mk_call, dtyp = mk_aux_call }
      |> (map o apfst) Type
      |> map (fn (T, cs) => map (mk_consexpr T) cs)
      |> map mk_rhs
    val lhss = map2 (fn t => fn T => t $ test_function T $ size) exhaustives Ts
  in
    map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhss ~~ rhss)
  end

fun gen_mk_call c T =  (T, fn t => c T $ absdummy T t $ size_pred)

fun gen_mk_aux_call functerms fTs (k, _) (tyco, Ts) =
  let
    val T = Type (tyco, Ts)
    val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
  in
   (T, fn t => nth functerms k $ absdummy T t $ size_pred)
  end

fun gen_mk_consexpr test_function functerms simpleT (c, xs) =
  let
    val (Ts, fns) = split_list xs
    val constr = Const (c, Ts ---> simpleT)
    val bounds = map Bound (((length xs) - 1) downto 0)
    val term_bounds = map (fn x => Bound (2 * x)) (((length xs) - 1) downto 0)
    val start_term = test_function simpleT $ list_comb (constr, bounds)
  in fold_rev (fn f => fn t => f t) fns start_term end
      
fun mk_fast_equations functerms =
  let
    fun test_function T = Free ("f", T --> @{typ "unit"})
    val mk_call = gen_mk_call (fn T =>
      Const (@{const_name "Quickcheck_Exhaustive.fast_exhaustive_class.fast_exhaustive"},
        fast_exhaustiveT T))
    val mk_aux_call = gen_mk_aux_call functerms
    val mk_consexpr = gen_mk_consexpr test_function functerms
    fun mk_rhs exprs = @{term "If :: bool => unit => unit => unit"}
        $ size_ge_zero $ (foldr1 mk_unit_let exprs) $ @{term "()"}
  in
    mk_equation_terms (mk_call, mk_aux_call, mk_consexpr, mk_rhs, test_function, functerms)
  end

fun mk_equations functerms =
  let
    fun test_function T = Free ("f", T --> resultT)
    val mk_call = gen_mk_call (fn T =>
      Const (@{const_name "Quickcheck_Exhaustive.exhaustive_class.exhaustive"}, exhaustiveT T))
    val mk_aux_call = gen_mk_aux_call functerms
    val mk_consexpr = gen_mk_consexpr test_function functerms
    fun mk_rhs exprs =
      mk_if (size_ge_zero, foldr1 mk_none_continuation exprs, Const (@{const_name "None"}, resultT))
  in
    mk_equation_terms (mk_call, mk_aux_call, mk_consexpr, mk_rhs, test_function, functerms)
  end

fun mk_bounded_forall_equations functerms =
  let
    fun test_function T = Free ("P", T --> @{typ bool})
    val mk_call = gen_mk_call (fn T =>
      Const (@{const_name "Quickcheck_Exhaustive.bounded_forall_class.bounded_forall"},
        bounded_forallT T))
    val mk_aux_call = gen_mk_aux_call functerms
    val mk_consexpr = gen_mk_consexpr test_function functerms
    fun mk_rhs exprs =
      mk_if (size_ge_zero, foldr1 HOLogic.mk_conj exprs, @{term "True"})
  in
    mk_equation_terms (mk_call, mk_aux_call, mk_consexpr, mk_rhs, test_function, functerms)
  end
  
fun mk_full_equations functerms =
  let
    fun test_function T = Free ("f", termifyT T --> resultT)
    fun split_const T = HOLogic.split_const (T, @{typ "unit => Code_Evaluation.term"}, resultT)
    fun mk_call T =
      let
        val full_exhaustive =
          Const (@{const_name "Quickcheck_Exhaustive.full_exhaustive_class.full_exhaustive"},
            full_exhaustiveT T)
      in                                   
        (T, fn t => full_exhaustive $
          (split_const T $ absdummy T (absdummy @{typ "unit => Code_Evaluation.term"} t)) $ size_pred)
      end
    fun mk_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts)
        val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
      in
        (T, fn t => nth functerms k $
          (split_const T $ absdummy T (absdummy @{typ "unit => Code_Evaluation.term"} t)) $ size_pred)
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
        val start_term = test_function simpleT $ 
        (HOLogic.pair_const simpleT @{typ "unit => Code_Evaluation.term"}
          $ (list_comb (constr, bounds)) $ absdummy @{typ unit} term)
      in fold_rev (fn f => fn t => f t) fns start_term end
    fun mk_rhs exprs =
      mk_if (size_ge_zero, foldr1 mk_none_continuation exprs,
        Const (@{const_name "None"}, resultT))
  in
    mk_equation_terms (mk_call, mk_aux_call, mk_consexpr, mk_rhs, test_function, functerms)
  end
  
(** foundational definition with the function package **)

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

(** instantiating generator classes **)
  
fun contains_recursive_type_under_function_types xs =
  exists (fn (_, (_, _, cs)) => cs |> exists (snd #> exists (fn dT =>
    (case Datatype_Aux.strip_dtyp dT of (_ :: _, Datatype.DtRec _) => true | _ => false)))) xs
    
fun instantiate_datatype (name, constprfx, sort, mk_equations, mk_T, argnames)
    config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  if not (contains_recursive_type_under_function_types descr) then
    let
      val _ = Datatype_Aux.message config ("Creating " ^ name ^ "...")
      val fullnames = map (prefix (constprfx ^ "_")) (names @ auxnames)
    in
      thy
      |> Class.instantiation (tycos, vs, sort)
      |> Quickcheck_Common.define_functions
          (fn functerms => mk_equations functerms (descr, vs, Ts @ Us), NONE)
          prfx argnames fullnames (map mk_T (Ts @ Us))
      |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
    end
  else
    (Datatype_Aux.message config
      ("Creation of " ^ name ^ " failed because the datatype is recursive under a function type");
    thy)

val instantiate_bounded_forall_datatype = instantiate_datatype
 ("bounded universal quantifiers", bounded_forallN, @{sort bounded_forall},
   mk_bounded_forall_equations, bounded_forallT, ["P", "i"]);

val instantiate_fast_exhaustive_datatype = instantiate_datatype 
 ("fast exhaustive generators", fast_exhaustiveN, @{sort fast_exhaustive},
   mk_fast_equations, fast_exhaustiveT, ["f", "i"])

val instantiate_exhaustive_datatype = instantiate_datatype  
  ("exhaustive generators", exhaustiveN, @{sort exhaustive},
    mk_equations, exhaustiveT, ["f", "i"])

val instantiate_full_exhaustive_datatype = instantiate_datatype
  ("full exhaustive generators", full_exhaustiveN, @{sort full_exhaustive},
    mk_full_equations, full_exhaustiveT, ["f", "i"])

(* building and compiling generator expressions *)


fun mk_test_term lookup mk_closure mk_if none_t return ctxt =
  let
    fun mk_naive_test_term t =
      fold_rev mk_closure (map lookup (Term.add_free_names t []))
        (mk_if (t, none_t, return))
    fun mk_smart_test_term' concl bound_vars assms genuine =
      let
        fun vars_of t = subtract (op =) bound_vars (Term.add_free_names t [])
        val (vars, check) =
          case assms of [] => (vars_of concl, (concl, none_t, return))
            | assm :: assms => (vars_of assm, (HOLogic.mk_not assm, none_t, 
                mk_smart_test_term' concl (union (op =) (vars_of assm) bound_vars) assms))
      in
        fold_rev mk_closure (map lookup vars) (mk_if check)
      end
    val mk_smart_test_term =
      Quickcheck_Common.strip_imp #> (fn (assms, concl) => mk_smart_test_term' concl [] assms true)
  in
    if Config.get ctxt smart_quantifier then mk_smart_test_term else mk_naive_test_term 
  end

fun mk_fast_generator_expr ctxt (t, eval_terms) =
  let
    val thy = Proof_Context.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    fun lookup v = the (AList.lookup (op =) (names ~~ frees) v)
    val ([depth_name], ctxt'') = Variable.variant_fixes ["depth"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    fun return _ = @{term "throw_Counterexample :: term list => unit"} $
      (HOLogic.mk_list @{typ "term"}
        (map (fn t => HOLogic.mk_term_of (fastype_of t) t) (frees @ eval_terms)))
    fun mk_exhaustive_closure (free as Free (_, T)) t =
      Const (@{const_name "Quickcheck_Exhaustive.fast_exhaustive_class.fast_exhaustive"},
        fast_exhaustiveT T)
        $ lambda free t $ depth
    val none_t = @{term "()"}
    fun mk_safe_if (cond, then_t, else_t) = mk_if (cond, then_t, else_t true)
    val mk_test_term = mk_test_term lookup mk_exhaustive_closure mk_safe_if none_t return ctxt 
  in lambda depth (@{term "catch_Counterexample :: unit => term list option"} $ mk_test_term t) end

fun mk_unknown_term T = HOLogic.reflect_term (Const ("Quickcheck_Exhaustive.unknown", T))

fun mk_safe_term t = @{term "Quickcheck.catch_match :: term => term => term"}
      $ (HOLogic.mk_term_of (fastype_of t) t) $ mk_unknown_term (fastype_of t)    

fun mk_return t genuine = @{term "Some :: bool * term list => (bool * term list) option"} $
  (HOLogic.pair_const @{typ bool} @{typ "term list"} $ Quickcheck_Common.reflect_bool genuine $ t)

fun mk_generator_expr ctxt (t, eval_terms) =
  let
    val thy = Proof_Context.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    fun lookup v = the (AList.lookup (op =) (names ~~ frees) v)
    val ([depth_name], ctxt'') = Variable.variant_fixes ["depth"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    val return = mk_return (HOLogic.mk_list @{typ "term"}
        (map (fn t => HOLogic.mk_term_of (fastype_of t) t) frees @ map mk_safe_term eval_terms))
    fun mk_exhaustive_closure (free as Free (_, T)) t =
      Const (@{const_name "Quickcheck_Exhaustive.exhaustive_class.exhaustive"}, exhaustiveT T)
        $ lambda free t $ depth
    val none_t = Const (@{const_name "None"}, resultT)
    val mk_if = Quickcheck_Common.mk_safe_if ctxt
    val mk_test_term = mk_test_term lookup mk_exhaustive_closure mk_if none_t return ctxt
  in lambda depth (mk_test_term t) end

fun mk_full_generator_expr ctxt (t, eval_terms) =
  let
    val thy = Proof_Context.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    val ([depth_name, genuine_only_name], ctxt'') =
      Variable.variant_fixes ["depth", "genuine_only"] ctxt'
    val (term_names, ctxt''') = Variable.variant_fixes (map (prefix "t_") names) ctxt''
    val depth = Free (depth_name, @{typ code_numeral})
    val genuine_only = Free (depth_name, @{typ bool})    
    val term_vars = map (fn n => Free (n, @{typ "unit => term"})) term_names
    fun lookup v = the (AList.lookup (op =) (names ~~ (frees ~~ term_vars)) v)
    val return = mk_return (HOLogic.mk_list @{typ term}
          (map (fn v => v $ @{term "()"}) term_vars @ map mk_safe_term eval_terms))
    fun mk_exhaustive_closure (free as Free (_, T), term_var) t =
      if Sign.of_sort thy (T, @{sort enum}) then
        Const (@{const_name "Quickcheck_Exhaustive.check_all_class.check_all"}, check_allT T)
          $ (HOLogic.split_const (T, @{typ "unit => term"}, resultT)
            $ lambda free (lambda term_var t))
      else
        Const (@{const_name "Quickcheck_Exhaustive.full_exhaustive_class.full_exhaustive"}, full_exhaustiveT T)
          $ (HOLogic.split_const (T, @{typ "unit => term"}, resultT)
            $ lambda free (lambda term_var t)) $ depth
    val none_t = Const (@{const_name "None"}, resultT)
    val mk_if = Quickcheck_Common.mk_safe_if ctxt
    val mk_test_term = mk_test_term lookup mk_exhaustive_closure mk_if none_t return ctxt
  in lambda genuine_only (lambda depth (mk_test_term t)) end

fun mk_parametric_generator_expr mk_generator_expr =
  Quickcheck_Common.gen_mk_parametric_generator_expr 
    ((mk_generator_expr, absdummy @{typ "code_numeral"} (Const (@{const_name "None"}, resultT))),
      @{typ "code_numeral"} --> resultT)

fun mk_validator_expr ctxt t =
  let
    fun bounded_forallT T = (T --> @{typ bool}) --> @{typ code_numeral} --> @{typ bool}
    val thy = Proof_Context.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    fun lookup v = the (AList.lookup (op =) (names ~~ frees) v)
    val ([depth_name], ctxt'') = Variable.variant_fixes ["depth"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    fun mk_bounded_forall (Free (s, T)) t =
      Const (@{const_name "Quickcheck_Exhaustive.bounded_forall_class.bounded_forall"}, bounded_forallT T)
        $ lambda (Free (s, T)) t $ depth
    fun mk_safe_if (cond, then_t, else_t) = mk_if (cond, then_t, else_t true)
    val mk_test_term =
      mk_test_term lookup mk_bounded_forall mk_safe_if @{term True} (K @{term False}) ctxt
  in lambda depth (mk_test_term t) end


fun mk_bounded_forall_generator_expr ctxt (t, eval_terms) = 
  let
    val frees = Term.add_free_names t []
    val dummy_term = @{term "Code_Evaluation.Const (STR ''dummy_pattern'')
      (Typerep.Typerep (STR ''dummy'') [])"}
    val return = @{term "Some :: term list => term list option"} $
      (HOLogic.mk_list @{typ "term"}
        (replicate (length frees + length eval_terms) dummy_term))
    val wrap = absdummy @{typ bool}
      (@{term "If :: bool => term list option => term list option => term list option"} $
        Bound 0 $ @{term "None :: term list option"} $ return)
  in HOLogic.mk_comp (wrap, mk_validator_expr ctxt t) end
  
(** generator compiliation **)

structure Counterexample = Proof_Data
(
  type T = unit -> int -> int -> (bool * term list) option
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
    val thy = Proof_Context.theory_of ctxt
    val mk_generator_expr = 
      if Config.get ctxt fast then mk_fast_generator_expr
      else if Config.get ctxt bounded_forall then mk_bounded_forall_generator_expr
      else if Config.get ctxt full_support then mk_full_generator_expr else mk_generator_expr
    val t' = mk_parametric_generator_expr mk_generator_expr ctxt ts;
    val compile = Code_Runtime.dynamic_value_strict
      (Counterexample.get, put_counterexample, "Exhaustive_Generators.put_counterexample")
      thy (SOME target) (fn proc => fn g =>
        fn card => fn size => g card size |> (Option.map o apsnd o map) proc) t' []
  in
    fn [card, size] => rpair NONE (compile card size |> 
      (if Config.get ctxt quickcheck_pretty then
        Option.map (apsnd (map Quickcheck_Common.post_process_term)) else I))
  end;

fun compile_generator_exprs ctxt ts =
  let
    val thy = Proof_Context.theory_of ctxt
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
    val thy = Proof_Context.theory_of ctxt
    val ts' = map (mk_validator_expr ctxt) ts
  in
    Code_Runtime.dynamic_value_strict
      (Validator_Batch.get, put_validator_batch, "Exhaustive_Generators.put_validator_batch")
      thy (SOME target) (K I) (HOLogic.mk_list @{typ "code_numeral => bool"} ts') []
  end;

val test_goals = Quickcheck_Common.generator_test_goal_terms ("exhaustive", compile_generator_expr);
  
(* setup *)

val setup_exhaustive_datatype_interpretation =
  Datatype.interpretation (Quickcheck_Common.ensure_sort_datatype
      (((@{sort typerep}, @{sort term_of}), @{sort exhaustive}), instantiate_exhaustive_datatype))

val active = Attrib.setup_config_bool @{binding quickcheck_exhaustive_active} (K true);

val setup =
  Datatype.interpretation (Quickcheck_Common.ensure_sort_datatype
      (((@{sort typerep}, @{sort term_of}), @{sort full_exhaustive}), instantiate_full_exhaustive_datatype))
(* #> Datatype.interpretation (Quickcheck_Common.ensure_sort_datatype
      (((@{sort typerep}, @{sort term_of}), @{sort exhaustive}), instantiate_exhaustive_datatype))
  #> Datatype.interpretation (Quickcheck_Common.ensure_sort_datatype
      (((@{sort typerep}, @{sort term_of}), @{sort fast_exhaustive}), instantiate_fast_exhaustive_datatype))
  #> Datatype.interpretation (Quickcheck_Common.ensure_sort_datatype
      (((@{sort type}, @{sort type}), @{sort bounded_forall}), instantiate_bounded_forall_datatype))*)
  #> Context.theory_map (Quickcheck.add_tester ("exhaustive", (active, test_goals)))
  #> Context.theory_map (Quickcheck.add_batch_generator ("exhaustive", compile_generator_exprs))
  #> Context.theory_map (Quickcheck.add_batch_validator ("exhaustive", compile_validator_exprs));

end;
