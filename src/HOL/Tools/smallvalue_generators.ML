(*  Title:      HOL/Tools/smallvalue_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Generators for small values for various types.
*)

signature SMALLVALUE_GENERATORS =
sig
  val compile_generator_expr:
    Proof.context -> term -> int -> term list option * Quickcheck.report option
  val put_counterexample: (unit -> int -> term list option)
    -> Proof.context -> Proof.context
  val smart_quantifier : bool Config.T;
  val setup: theory -> theory
end;

structure Smallvalue_Generators : SMALLVALUE_GENERATORS =
struct

(* static options *)

val define_foundationally = false

(* dynamic options *)

val (smart_quantifier, setup_smart_quantifier) =
  Attrib.config_bool "quickcheck_smart_quantifier" (K true)

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
fun test_function T = Free ("f", termifyT T --> @{typ "term list option"})

fun mk_none_continuation (x, y) =
  let
    val (T as Type(@{type_name "option"}, [T'])) = fastype_of x
  in
    Const (@{const_name "Smallcheck.orelse"}, T --> T --> T)
      $ x $ y
  end

(** datatypes **)

(* constructing smallvalue generator instances on datatypes *)

exception FUNCTION_TYPE;

val smallN = "small";

fun smallT T = (T --> @{typ "Code_Evaluation.term list option"}) --> @{typ code_numeral}
  --> @{typ "Code_Evaluation.term list option"}

val full_smallN = "full_small";

fun full_smallT T = (termifyT T --> @{typ "Code_Evaluation.term list option"})
  --> @{typ code_numeral} --> @{typ "Code_Evaluation.term list option"}

fun check_allT T = (termifyT T --> @{typ "Code_Evaluation.term list option"})
  --> @{typ "Code_Evaluation.term list option"}

fun mk_equations thy descr vs tycos smalls (Ts, Us) =
  let
    fun mk_small_call T =
      let
        val small = Const (@{const_name "Smallcheck.full_small_class.full_small"}, full_smallT T)        
      in
        (T, (fn t => small $
          (HOLogic.split_const (T, @{typ "unit => Code_Evaluation.term"}, @{typ "Code_Evaluation.term list option"})
          $ absdummy (T, absdummy (@{typ "unit => Code_Evaluation.term"}, t))) $ size_pred))
      end
    fun mk_small_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts)
        val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
        val small = nth smalls k
      in
       (T, (fn t => small $
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
        val start_term = test_function simpleT $ 
        (HOLogic.pair_const simpleT @{typ "unit => Code_Evaluation.term"}
          $ (list_comb (constr, bounds)) $ absdummy (@{typ unit}, term))
      in fold_rev (fn f => fn t => f t) fns start_term end
    fun mk_rhs exprs =
        @{term "If :: bool => term list option => term list option => term list option"}
            $ size_ge_zero $ (foldr1 mk_none_continuation exprs) $ @{term "None :: term list option"}
    val rhss =
      Datatype_Aux.interpret_construction descr vs
        { atyp = mk_small_call, dtyp = mk_small_aux_call }
      |> (map o apfst) Type
      |> map (fn (T, cs) => map (mk_consexpr T) cs)
      |> map mk_rhs
    val lhss = map2 (fn t => fn T => t $ test_function T $ size) smalls (Ts @ Us);
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

fun pat_completeness_auto ctxt =
  Pat_Completeness.pat_completeness_tac ctxt 1
  THEN auto_tac (clasimpset_of ctxt)    


(* creating the instances *)

fun instantiate_smallvalue_datatype config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  let
    val _ = Datatype_Aux.message config "Creating smallvalue generators ...";
    val smallsN = map (prefix (full_smallN ^ "_")) (names @ auxnames);
  in
    thy
    |> Class.instantiation (tycos, vs, @{sort full_small})
    |> (if define_foundationally then
      let
        val smalls = map2 (fn name => fn T => Free (name, full_smallT T)) smallsN (Ts @ Us)
        val eqs = mk_equations thy descr vs tycos smalls (Ts, Us)
      in
        Function.add_function
          (map (fn (name, T) =>
              Syntax.no_syn (Binding.conceal (Binding.name name), SOME (full_smallT T)))
                (smallsN ~~ (Ts @ Us)))
            (map (pair (apfst Binding.conceal Attrib.empty_binding)) eqs)
          Function_Common.default_config pat_completeness_auto
        #> snd
        #> Local_Theory.restore
        #> (fn lthy => Function.prove_termination NONE (termination_tac lthy) lthy)
        #> snd
      end
    else
      fold_map (fn (name, T) => Local_Theory.define
          ((Binding.conceal (Binding.name name), NoSyn),
            (apfst Binding.conceal Attrib.empty_binding, mk_undefined (full_smallT T)))
        #> apfst fst) (smallsN ~~ (Ts @ Us))
      #> (fn (smalls, lthy) =>
        let
          val eqs_t = mk_equations thy descr vs tycos smalls (Ts, Us)
          val eqs = map (fn eq => Goal.prove lthy ["f", "i"] [] eq
            (fn _ => Skip_Proof.cheat_tac (ProofContext.theory_of lthy))) eqs_t
        in
          fold (fn (name, eq) => Local_Theory.note
          ((Binding.conceal (Binding.qualify true prfx
             (Binding.qualify true name (Binding.name "simps"))),
             Code.add_default_eqn_attrib :: map (Attrib.internal o K)
               [Simplifier.simp_add, Nitpick_Simps.add]), [eq]) #> snd) (smallsN ~~ eqs) lthy
        end))
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end handle FUNCTION_TYPE =>
    (Datatype_Aux.message config
      "Creation of smallvalue generators failed because the datatype contains a function type";
    thy)

(** building and compiling generator expressions **)

structure Counterexample = Proof_Data (
  type T = unit -> int -> term list option
  fun init _ () = error "Counterexample"
);
val put_counterexample = Counterexample.put;

val target = "Quickcheck";

fun mk_smart_generator_expr ctxt t =
  let
    val thy = ProofContext.theory_of ctxt
    val ((vnames, Ts), t') = apfst split_list (strip_abs t)
    val ([depth_name], ctxt') = Variable.variant_fixes ["depth"] ctxt
    val (names, ctxt'') = Variable.variant_fixes vnames ctxt'
    val (term_names, ctxt''') = Variable.variant_fixes (map (prefix "t_") vnames) ctxt''
    val depth = Free (depth_name, @{typ code_numeral})
    val frees = map2 (curry Free) names Ts
    val term_vars = map (fn n => Free (n, @{typ "unit => term"})) term_names 
    fun strip_imp (Const(@{const_name HOL.implies},_) $ A $ B) = apfst (cons A) (strip_imp B)
      | strip_imp A = ([], A)
    val (assms, concl) = strip_imp (subst_bounds (rev frees, t'))
    val terms = HOLogic.mk_list @{typ term} (map (fn v => v $ @{term "()"}) term_vars)
    fun mk_small_closure (free as Free (_, T), term_var) t =
      if Sign.of_sort thy (T, @{sort enum}) then
        Const (@{const_name "Smallcheck.check_all_class.check_all"}, check_allT T)
          $ (HOLogic.split_const (T, @{typ "unit => term"}, @{typ "term list option"}) 
            $ lambda free (lambda term_var t))
      else
        Const (@{const_name "Smallcheck.full_small_class.full_small"}, full_smallT T)
          $ (HOLogic.split_const (T, @{typ "unit => term"}, @{typ "term list option"}) 
            $ lambda free (lambda term_var t)) $ depth
    fun lookup v = the (AList.lookup (op =) (names ~~ (frees ~~ term_vars)) v)
    val none_t = @{term "None :: term list option"}
    fun mk_safe_if (cond, then_t, else_t) =
      @{term "Smallcheck.catch_match :: term list option => term list option => term list option"} $
        (@{term "If :: bool => term list option => term list option => term list option"}
        $ cond $ then_t $ else_t) $ none_t;
    fun mk_test_term bound_vars assms =
      let
        fun vars_of t = subtract (op =) bound_vars (Term.add_free_names t [])
        val (vars, check) =
          case assms of [] =>
            (vars_of concl, (concl, none_t, @{term "Some :: term list => term list option"} $ terms))
          | assm :: assms =>
            (vars_of assm, (assm, mk_test_term (union (op =) (vars_of assm) bound_vars) assms, none_t))
      in
        fold_rev mk_small_closure (map lookup vars) (mk_safe_if check)
      end
  in lambda depth (mk_test_term [] assms) end

fun mk_generator_expr ctxt t =
  let
    val Ts = (map snd o fst o strip_abs) t;
    val thy = ProofContext.theory_of ctxt
    val bound_max = length Ts - 1;
    val bounds = map_index (fn (i, ty) =>
      (2 * (bound_max - i) + 1, 2 * (bound_max - i), 2 * i, ty)) Ts;
    val result = list_comb (t, map (fn (i, _, _, _) => Bound i) bounds);
    val terms = HOLogic.mk_list @{typ term} (map (fn (_, i, _, _) => Bound i $ @{term "()"}) bounds);
    val check =
      @{term "Smallcheck.catch_match :: term list option => term list option => term list option"} $
        (@{term "If :: bool => term list option => term list option => term list option"}
        $ result $ @{term "None :: term list option"} $ (@{term "Some :: term list => term list option"} $ terms))
      $ @{term "None :: term list option"};
    fun mk_small_closure (_, _, i, T) t =
      Const (@{const_name "Smallcheck.full_small_class.full_small"}, full_smallT T)
        $ (HOLogic.split_const (T, @{typ "unit => term"}, @{typ "term list option"}) 
        $ absdummy (T, absdummy (@{typ "unit => term"}, t))) $ Bound i
  in Abs ("d", @{typ code_numeral}, fold_rev mk_small_closure bounds check) end

fun compile_generator_expr ctxt t =
  let
    val thy = ProofContext.theory_of ctxt
    val t' =
      (if Config.get ctxt smart_quantifier then mk_smart_generator_expr else mk_generator_expr)
        ctxt t;
    val compile = Code_Runtime.dynamic_value_strict
      (Counterexample.get, put_counterexample, "Smallvalue_Generators.put_counterexample")
      thy (SOME target) (fn proc => fn g => g #> (Option.map o map) proc) t' [];
  in fn size => rpair NONE (compile size) end;

(** setup **)

val setup =
  Datatype.interpretation
    (Quickcheck_Generators.ensure_sort_datatype (@{sort full_small}, instantiate_smallvalue_datatype))
  #> setup_smart_quantifier
  #> Context.theory_map
    (Quickcheck.add_generator ("exhaustive", compile_generator_expr));

end;
