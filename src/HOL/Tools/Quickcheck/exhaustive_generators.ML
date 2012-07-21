(*  Title:      HOL/Tools/Quickcheck/exhaustive_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Exhaustive generators for various types.
*)

signature EXHAUSTIVE_GENERATORS =
sig
  val compile_generator_expr:
    Proof.context -> (term * term list) list -> bool -> int list -> (bool * term list) option * Quickcheck.report option
  val compile_generator_exprs: Proof.context -> term list -> (int -> term list option) list
  val compile_validator_exprs: Proof.context -> term list -> (int -> bool) list
  val put_counterexample: (unit -> int -> bool -> int -> (bool * term list) option)
    -> Proof.context -> Proof.context
  val put_counterexample_batch: (unit -> (int -> term list option) list)
    -> Proof.context -> Proof.context
  val put_validator_batch: (unit -> (int -> bool) list) -> Proof.context -> Proof.context
  exception Counterexample of term list
  val smart_quantifier : bool Config.T
  val optimise_equality : bool Config.T
  val quickcheck_pretty : bool Config.T
  val setup_exhaustive_datatype_interpretation : theory -> theory
  val setup_bounded_forall_datatype_interpretation : theory -> theory
  val setup: theory -> theory
  
  val instantiate_full_exhaustive_datatype : Datatype_Aux.config -> Datatype_Aux.descr ->
    (string * sort) list -> string list -> string -> string list * string list -> typ list * typ list -> theory -> theory
  val instantiate_exhaustive_datatype : Datatype_Aux.config -> Datatype_Aux.descr ->
    (string * sort) list -> string list -> string -> string list * string list -> typ list * typ list -> theory -> theory

end;

structure Exhaustive_Generators : EXHAUSTIVE_GENERATORS =
struct

(* basics *)

(** dynamic options **)

val smart_quantifier = Attrib.setup_config_bool @{binding quickcheck_smart_quantifier} (K true)
val optimise_equality = Attrib.setup_config_bool @{binding quickcheck_optimise_equality} (K true)

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
    val (T as Type(@{type_name "option"}, _)) = fastype_of x
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

fun gen_mk_consexpr test_function simpleT (c, xs) =
  let
    val (Ts, fns) = split_list xs
    val constr = Const (c, Ts ---> simpleT)
    val bounds = map Bound (((length xs) - 1) downto 0)
    val start_term = test_function simpleT $ list_comb (constr, bounds)
  in fold_rev (fn f => fn t => f t) fns start_term end
      
fun mk_fast_equations functerms =
  let
    fun test_function T = Free ("f", T --> @{typ "unit"})
    val mk_call = gen_mk_call (fn T =>
      Const (@{const_name "Quickcheck_Exhaustive.fast_exhaustive_class.fast_exhaustive"},
        fast_exhaustiveT T))
    val mk_aux_call = gen_mk_aux_call functerms
    val mk_consexpr = gen_mk_consexpr test_function
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
    val mk_consexpr = gen_mk_consexpr test_function
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
    val mk_consexpr = gen_mk_consexpr test_function
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

fun mk_let_expr (x, t, e) genuine =
  let
    val (T1, T2) = (fastype_of x, fastype_of (e genuine))
  in  
    Const (@{const_name Let}, T1 --> (T1 --> T2) --> T2) $ t $ lambda x (e genuine)
  end

fun mk_safe_let_expr genuine_only none safe (x, t, e) genuine =
  let
    val (T1, T2) = (fastype_of x, fastype_of (e genuine))
    val if_t = Const (@{const_name "If"}, @{typ bool} --> T2 --> T2 --> T2)
  in
    Const (@{const_name "Quickcheck.catch_match"}, T2 --> T2 --> T2) $ 
      (Const (@{const_name Let}, T1 --> (T1 --> T2) --> T2) $ t $ lambda x (e genuine)) $
      (if_t $ genuine_only $ none $ safe false)
  end

fun mk_test_term lookup mk_closure mk_if mk_let none_t return ctxt =
  let
    val cnstrs = flat (maps
      (map (fn (_, (Tname, _, cs)) => map (apsnd (rpair Tname o length)) cs) o #descr o snd)
      (Symtab.dest (Datatype.get_all (Proof_Context.theory_of ctxt))))
    fun is_constrt (Const (s, T), ts) = (case (AList.lookup (op =) cnstrs s, body_type T) of
        (SOME (i, Tname), Type (Tname', _)) => length ts = i andalso Tname = Tname'
      | _ => false)
      | is_constrt _ = false
    fun mk_naive_test_term t =
      fold_rev mk_closure (map lookup (Term.add_free_names t []))
        (mk_if (t, none_t, return) true)
    fun mk_test (vars, check) = fold_rev mk_closure (map lookup vars) check
    fun mk_smart_test_term' concl bound_vars assms genuine =
      let
        fun vars_of t = subtract (op =) bound_vars (Term.add_free_names t [])
        fun mk_equality_term (lhs, f as Free (x, _)) c (assm, assms) =
          if member (op =) (Term.add_free_names lhs bound_vars) x then
            c (assm, assms)
          else
            (let
               val rec_call = mk_smart_test_term' concl (union (op =) (vars_of assm) bound_vars) assms
               fun safe genuine =
                 the_default I (Option.map mk_closure (try lookup x)) (rec_call genuine)
            in
              mk_test (remove (op =) x (vars_of assm),
                mk_let safe f (try lookup x) lhs 
                  (mk_smart_test_term' concl (union (op =) (vars_of assm) bound_vars) assms) genuine)
            
            end)
          | mk_equality_term (lhs, t) c (assm, assms) =
            if is_constrt (strip_comb t) then
              let
                val (constr, args) = strip_comb t
                val T = fastype_of t
                val vars = map Free (Variable.variant_frees ctxt (concl :: assms)
                  (map (fn t => ("x", fastype_of t)) args))
                val varnames = map (fst o dest_Free) vars
                val dummy_var = Free (singleton
                  (Variable.variant_frees ctxt (concl :: assms @ vars)) ("dummy", T))
                val new_assms = map HOLogic.mk_eq (vars ~~ args)
                val bound_vars' = union (op =) (vars_of lhs) (union (op =) varnames bound_vars)
                val cont_t = mk_smart_test_term' concl bound_vars' (new_assms @ assms) genuine
              in
                mk_test (vars_of lhs, Datatype_Case.make_case ctxt Datatype_Case.Quiet [] lhs
                  [(list_comb (constr, vars), cont_t), (dummy_var, none_t)])
              end
            else c (assm, assms)
        fun default (assm, assms) =
          mk_test (vars_of assm,
            mk_if (HOLogic.mk_not assm, none_t, 
            mk_smart_test_term' concl (union (op =) (vars_of assm) bound_vars) assms) genuine)
      in
        case assms of [] => mk_test (vars_of concl, mk_if (concl, none_t, return) genuine)
          | assm :: assms =>
            if Config.get ctxt optimise_equality then
              (case try HOLogic.dest_eq assm of
                SOME (lhs, rhs) =>
                  mk_equality_term (lhs, rhs) (mk_equality_term (rhs, lhs) default) (assm, assms)
              | NONE => default (assm, assms))
            else default (assm, assms)
      end
    val mk_smart_test_term =
      Quickcheck_Common.strip_imp #> (fn (assms, concl) => mk_smart_test_term' concl [] assms true)
  in
    if Config.get ctxt smart_quantifier then mk_smart_test_term else mk_naive_test_term
  end

fun mk_fast_generator_expr ctxt (t, eval_terms) =
  let
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    fun lookup v = the (AList.lookup (op =) (names ~~ frees) v)
    val ([depth_name], _) = Variable.variant_fixes ["depth"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    fun return _ = @{term "throw_Counterexample :: term list => unit"} $
      (HOLogic.mk_list @{typ "term"}
        (map (fn t => HOLogic.mk_term_of (fastype_of t) t) (frees @ eval_terms)))
    fun mk_exhaustive_closure (free as Free (_, T)) t =
      Const (@{const_name "Quickcheck_Exhaustive.fast_exhaustive_class.fast_exhaustive"},
        fast_exhaustiveT T)
        $ lambda free t $ depth
    val none_t = @{term "()"}
    fun mk_safe_if (cond, then_t, else_t) genuine = mk_if (cond, then_t, else_t genuine)
    fun mk_let _ def v_opt t e = mk_let_expr (the_default def v_opt, t, e)
    val mk_test_term = mk_test_term lookup mk_exhaustive_closure mk_safe_if mk_let none_t return ctxt 
  in lambda depth (@{term "catch_Counterexample :: unit => term list option"} $ mk_test_term t) end

fun mk_unknown_term T = HOLogic.reflect_term (Const ("Quickcheck_Exhaustive.unknown", T))

fun mk_safe_term t = @{term "Quickcheck.catch_match :: term => term => term"}
      $ (HOLogic.mk_term_of (fastype_of t) t) $ mk_unknown_term (fastype_of t)    

fun mk_return t genuine = @{term "Some :: bool * term list => (bool * term list) option"} $
  (HOLogic.pair_const @{typ bool} @{typ "term list"} $ Quickcheck_Common.reflect_bool genuine $ t)

fun mk_generator_expr ctxt (t, eval_terms) =
  let
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    fun lookup v = the (AList.lookup (op =) (names ~~ frees) v)
    val ([depth_name, genuine_only_name], _) =
      Variable.variant_fixes ["depth", "genuine_only"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    val genuine_only = Free (genuine_only_name, @{typ bool}) 
    val return = mk_return (HOLogic.mk_list @{typ "term"}
        (map (fn t => HOLogic.mk_term_of (fastype_of t) t) frees @ map mk_safe_term eval_terms))
    fun mk_exhaustive_closure (free as Free (_, T)) t =
      Const (@{const_name "Quickcheck_Exhaustive.exhaustive_class.exhaustive"}, exhaustiveT T)
        $ lambda free t $ depth
    val none_t = Const (@{const_name "None"}, resultT)
    val mk_if = Quickcheck_Common.mk_safe_if genuine_only none_t
    fun mk_let safe def v_opt t e = mk_safe_let_expr genuine_only none_t safe (the_default def v_opt, t, e)
    val mk_test_term = mk_test_term lookup mk_exhaustive_closure mk_if mk_let none_t return ctxt
  in lambda genuine_only (lambda depth (mk_test_term t)) end

fun mk_full_generator_expr ctxt (t, eval_terms) =
  let
    val thy = Proof_Context.theory_of ctxt
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    val ([depth_name, genuine_only_name], ctxt'') =
      Variable.variant_fixes ["depth", "genuine_only"] ctxt'
    val (term_names, _) = Variable.variant_fixes (map (prefix "t_") names) ctxt''
    val depth = Free (depth_name, @{typ code_numeral})
    val genuine_only = Free (genuine_only_name, @{typ bool})    
    val term_vars = map (fn n => Free (n, @{typ "unit => term"})) term_names
    fun lookup v = the (AList.lookup (op =) (names ~~ (frees ~~ term_vars)) v)
    val return = mk_return (HOLogic.mk_list @{typ term}
          (map (fn v => v $ @{term "()"}) term_vars @ map mk_safe_term eval_terms))
    fun mk_exhaustive_closure (free as Free (_, T), term_var) t =
      if Sign.of_sort thy (T, @{sort check_all}) then
        Const (@{const_name "Quickcheck_Exhaustive.check_all_class.check_all"}, check_allT T)
          $ (HOLogic.split_const (T, @{typ "unit => term"}, resultT)
            $ lambda free (lambda term_var t))
      else
        Const (@{const_name "Quickcheck_Exhaustive.full_exhaustive_class.full_exhaustive"}, full_exhaustiveT T)
          $ (HOLogic.split_const (T, @{typ "unit => term"}, resultT)
            $ lambda free (lambda term_var t)) $ depth
    val none_t = Const (@{const_name "None"}, resultT)
    val mk_if = Quickcheck_Common.mk_safe_if genuine_only none_t
    fun mk_let safe _ (SOME (v, term_var)) t e =
        mk_safe_let_expr genuine_only none_t safe (v, t, 
          e #> subst_free [(term_var, absdummy @{typ unit} (mk_safe_term t))])
      | mk_let safe v NONE t e = mk_safe_let_expr genuine_only none_t safe (v, t, e)
    val mk_test_term = mk_test_term lookup mk_exhaustive_closure mk_if mk_let none_t return ctxt
  in lambda genuine_only (lambda depth (mk_test_term t)) end

fun mk_parametric_generator_expr mk_generator_expr =
  Quickcheck_Common.gen_mk_parametric_generator_expr 
    ((mk_generator_expr,
      absdummy @{typ bool} (absdummy @{typ "code_numeral"} (Const (@{const_name "None"}, resultT)))),
      @{typ bool} --> @{typ "code_numeral"} --> resultT)

fun mk_validator_expr ctxt t =
  let
    fun bounded_forallT T = (T --> @{typ bool}) --> @{typ code_numeral} --> @{typ bool}
    val ctxt' = Variable.auto_fixes t ctxt
    val names = Term.add_free_names t []
    val frees = map Free (Term.add_frees t [])
    fun lookup v = the (AList.lookup (op =) (names ~~ frees) v)
    val ([depth_name], _) = Variable.variant_fixes ["depth"] ctxt'
    val depth = Free (depth_name, @{typ code_numeral})
    fun mk_bounded_forall (Free (s, T)) t =
      Const (@{const_name "Quickcheck_Exhaustive.bounded_forall_class.bounded_forall"}, bounded_forallT T)
        $ lambda (Free (s, T)) t $ depth
    fun mk_safe_if (cond, then_t, else_t) genuine = mk_if (cond, then_t, else_t genuine)
    fun mk_let safe def v_opt t e = mk_let_expr (the_default def v_opt, t, e)
    val mk_test_term =
      mk_test_term lookup mk_bounded_forall mk_safe_if mk_let @{term True} (K @{term False}) ctxt
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

(* FIXME just one data slot (record) per program unit *)

structure Counterexample = Proof_Data
(
  type T = unit -> int -> bool -> int -> (bool * term list) option
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
        fn card => fn genuine_only => fn size => g card genuine_only size
          |> (Option.map o apsnd o map) proc) t' []
  in
    fn genuine_only => fn [card, size] => rpair NONE (compile card genuine_only size |> 
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

fun size_matters_for thy Ts = not (forall (fn T => Sign.of_sort thy (T,  @{sort check_all})) Ts)

val test_goals =
  Quickcheck_Common.generator_test_goal_terms ("exhaustive", (size_matters_for, compile_generator_expr));
  
(* setup *)

val setup_exhaustive_datatype_interpretation =
  Quickcheck_Common.datatype_interpretation (@{sort exhaustive}, instantiate_exhaustive_datatype)

val setup_bounded_forall_datatype_interpretation =
  Datatype.interpretation (Quickcheck_Common.ensure_sort
    (((@{sort type}, @{sort type}), @{sort bounded_forall}),
    (Datatype.the_descr, instantiate_bounded_forall_datatype)))

val active = Attrib.setup_config_bool @{binding quickcheck_exhaustive_active} (K true);

val setup =
  Quickcheck_Common.datatype_interpretation (@{sort full_exhaustive}, instantiate_full_exhaustive_datatype)
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
