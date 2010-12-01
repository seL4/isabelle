(*  Title:      HOL/Tools/smallvalue_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Generators for small values for various types.
*)

signature SMALLVALUE_GENERATORS =
sig
  val compile_generator_expr:
    Proof.context -> term -> int -> term list option * (bool list * bool)
  val put_counterexample: (unit -> int -> term list option)
    -> Proof.context -> Proof.context
  val setup: theory -> theory
end;

structure Smallvalue_Generators : SMALLVALUE_GENERATORS =
struct

(** general term functions **)

fun mk_fun_comp (t, u) =
  let
    val (_, B) = dest_funT (fastype_of t)
    val (C, A) = dest_funT (fastype_of u)
  in
    Const(@{const_name "Fun.comp"}, (A --> B) --> (C --> A) --> C --> B) $ t $ u
  end;

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
fun test_function T = Free ("f", termifyT T --> @{typ "term list option"})

fun mk_none_continuation (x, y) =
  let
    val (T as Type(@{type_name "option"}, [T'])) = fastype_of x
  in
    Const (@{const_name Option.option_case}, T --> (T' --> T) --> T --> T)
      $ y $ Const (@{const_name Some}, T' --> T) $ x
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
 
fun mk_equations thy descr vs tycos (names, auxnames) (Ts, Us) =
  let
    val smallsN = map (prefix (full_smallN ^ "_")) (names @ auxnames);
    val smalls = map2 (fn name => fn T => Free (name, full_smallT T))
      smallsN (Ts @ Us)
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
    (Ts @ Us ~~ (smallsN ~~ eqs))
  end
    
val less_int_pred = @{lemma "i > 0 ==> Code_Numeral.nat_of ((i :: code_numeral) - 1) < Code_Numeral.nat_of i" by auto}
  
fun instantiate_smallvalue_datatype config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  let
    val _ = Datatype_Aux.message config "Creating smallvalue generators ...";
    val eqs = mk_equations thy descr vs tycos (names, auxnames) (Ts, Us)
    fun mk_single_measure T = mk_fun_comp (@{term "Code_Numeral.nat_of"},
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
  in 
    thy
    |> Class.instantiation (tycos, vs, @{sort full_small})
    |> Function.add_function
      (map (fn (T, (name, _)) =>
          Syntax.no_syn (Binding.conceal (Binding.name name), SOME (full_smallT T))) eqs)
        (map (pair (apfst Binding.conceal Attrib.empty_binding) o snd o snd) eqs)
        Function_Common.default_config pat_completeness_auto
    |> snd
    |> Local_Theory.restore
    |> (fn lthy => Function.prove_termination NONE (termination_tac lthy) lthy)
    |> snd
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

fun mk_generator_expr thy prop Ts =
  let
    val bound_max = length Ts - 1;
    val bounds = map_index (fn (i, ty) =>
      (2 * (bound_max - i) + 1, 2 * (bound_max - i), 2 * i, ty)) Ts;
    val result = list_comb (prop, map (fn (i, _, _, _) => Bound i) bounds);
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
    val Ts = (map snd o fst o strip_abs) t;
    val thy = ProofContext.theory_of ctxt
  in if Config.get ctxt Quickcheck.report then
    error "Compilation with reporting facility is not supported"
  else
    let
      val t' = mk_generator_expr thy t Ts;
      val compile = Code_Runtime.dynamic_value_strict
        (Counterexample.get, put_counterexample, "Smallvalue_Generators.put_counterexample")
        thy (SOME target) (fn proc => fn g => g #> (Option.map o map) proc) t' [];
      val dummy_report = ([], false)
    in compile #> rpair dummy_report end
  end;

(** setup **)

val setup =
  Datatype.interpretation
    (Quickcheck_Generators.ensure_sort_datatype (@{sort full_small}, instantiate_smallvalue_datatype))
  #> Context.theory_map
    (Quickcheck.add_generator ("small", compile_generator_expr));

end;
