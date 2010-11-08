(*  Title:      HOL/Tools/smallvalue_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Generators for small values for various types.
*)

signature SMALLVALUE_GENERATORS =
sig
  val ensure_smallvalue_datatype: Datatype.config -> string list -> theory -> theory
  val compile_generator_expr:
    Proof.context -> term -> int -> term list option * (bool list * bool)
  val put_counterexample: (unit -> int -> term list option)
    -> Proof.context -> Proof.context
  val setup: theory -> theory
end;

structure Smallvalue_Generators : SMALLVALUE_GENERATORS =
struct

(** general term functions **)

fun dest_funT (Type ("fun",[S, T])) = (S, T)
  | dest_funT T = raise TYPE ("dest_funT", [T], [])
 
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

val size = @{term "i :: code_numeral"}
val size_pred = @{term "(i :: code_numeral) - 1"}
val size_ge_zero = @{term "(i :: code_numeral) > 0"}
fun test_function T = Free ("f", T --> @{typ "term list option"})

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

fun mk_equations thy descr vs tycos (names, auxnames) (Ts, Us) =
  let
    val smallsN = map (prefix (smallN ^ "_")) (names @ auxnames);
    val smalls = map2 (fn name => fn T => Free (name, smallT T))
      smallsN (Ts @ Us)
    fun mk_small_call T =
      let
        val small = Const (@{const_name "Smallcheck.small_class.small"}, smallT T)        
      in
        (T, (fn t => small $ absdummy (T, t) $ size_pred))
      end
    fun mk_small_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts)
        val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
        val small = nth smalls k
      in
        (T, (fn t => small $ absdummy (T, t) $ size_pred))
      end
    fun mk_consexpr simpleT (c, xs) =
      let
        val (Ts, fns) = split_list xs
        val constr = Const (c, Ts ---> simpleT)
        val bounds = map Bound (((length xs) - 1) downto 0)
        val start_term = test_function simpleT $ (list_comb (constr, bounds))
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

fun gen_inst_state_tac ctxt rel st =
  case Term.add_vars (prop_of st) [] of
    [v as (_, T)] =>
      let
        val cert = Thm.cterm_of (ProofContext.theory_of ctxt)
        val rel' = cert rel
        val st' = Thm.incr_indexes (#maxidx (Thm.rep_cterm rel') + 1) st (*FIXME??*)
      in        
        PRIMITIVE (Drule.cterm_instantiate [(cert (Var v), rel')]) st'
      end
  | _ => Seq.empty;

fun instantiate_smallvalue_datatype config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  let
    val _ = Datatype_Aux.message config "Creating smallvalue generators ...";
    val eqs = mk_equations thy descr vs tycos (names, auxnames) (Ts, Us)
    fun my_relation_tac ctxt st =
      let
        val ((_ $ (_ $ rel)) :: tl) = prems_of st
        val domT = (HOLogic.dest_setT (fastype_of rel))
        fun mk_single_measure T = mk_fun_comp (@{term "Code_Numeral.nat_of"},
            Const (@{const_name "Product_Type.snd"}, T --> @{typ "code_numeral"}))
        val measure = mk_measure (mk_sumcases @{typ nat} mk_single_measure domT)
      in
        (Function_Common.apply_termination_rule ctxt 1
        THEN gen_inst_state_tac ctxt measure) st
      end
    fun termination_tac ctxt = 
      my_relation_tac ctxt
      THEN rtac @{thm wf_measure} 1
      THEN (REPEAT_DETERM (Simplifier.asm_full_simp_tac 
        (HOL_basic_ss addsimps [@{thm in_measure}, @{thm o_def}, @{thm snd_conv},
         @{thm nat_mono_iff}, less_int_pred] @ @{thms sum.cases}) 1))
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac (clasimpset_of ctxt)
  in
    thy
    |> Class.instantiation (tycos, vs, @{sort small})
    |> Function.add_function
      (map (fn (T, (name, _)) =>
          Syntax.no_syn (Binding.conceal (Binding.name name), SOME (smallT T))) eqs)
        (map (pair (apfst Binding.conceal Attrib.empty_binding) o snd o snd) eqs)
        Function_Common.default_config pat_completeness_auto
    |> snd
    |> Local_Theory.restore
    |> (fn lthy => Function.prove_termination NONE (termination_tac lthy) lthy)
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun ensure_smallvalue_datatype config raw_tycos thy =
  let
    val algebra = Sign.classes_of thy;
    val (descr, raw_vs, tycos, prfx, (names, auxnames), raw_TUs) =
      Datatype.the_descr thy raw_tycos;
    val typerep_vs = (map o apsnd)
      (curry (Sorts.inter_sort algebra) @{sort typerep}) raw_vs;
    val smallvalue_insts = (map (rpair @{sort small}) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr typerep_vs
        { atyp = single, dtyp = (K o K o K) [] });
    (*val term_of_insts = (map (rpair @{sort term_of}) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr typerep_vs
        { atyp = K [], dtyp = K o K });*)
    val has_inst = exists (fn tyco =>
      can (Sorts.mg_domain algebra tyco) @{sort small}) tycos;
  in if has_inst then thy
    else case Quickcheck_Generators.perhaps_constrain thy smallvalue_insts typerep_vs
     of SOME constrain => (instantiate_smallvalue_datatype config descr
          (map constrain typerep_vs) tycos prfx (names, auxnames)
            ((pairself o map o map_atyps) (fn TFree v => TFree (constrain v)) raw_TUs) thy
            handle FUNCTION_TYPE =>
              (Datatype_Aux.message config
                "Creation of smallvalue generators failed because the datatype contains a function type";
              thy))
      | NONE => thy
  end;

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
    val bounds = map Bound (bound_max downto 0)
    val result = list_comb (prop, bounds);
    val terms = HOLogic.mk_list @{typ term} (map2 HOLogic.mk_term_of Ts bounds);
    val check =
      @{term "Smallcheck.catch_match :: term list option => term list option => term list option"} $
        (@{term "If :: bool => term list option => term list option => term list option"}
        $ result $ @{term "None :: term list option"}
        $ (@{term "Some :: term list => term list option"} $ terms))
      $ @{term "None :: term list option"};
    fun mk_small_closure (depth, T) t =
      Const (@{const_name "Smallcheck.small_class.small"}, smallT T)
        $ absdummy (T, t) $ depth
  in Abs ("d", @{typ code_numeral}, fold_rev mk_small_closure (rev bounds ~~ Ts) check) end

fun compile_generator_expr ctxt t =
  let
    val Ts = (map snd o fst o strip_abs) t;
    val thy = ProofContext.theory_of ctxt
  in if Quickcheck.report ctxt then
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
  Datatype.interpretation ensure_smallvalue_datatype
  #> Context.theory_map
    (Quickcheck.add_generator ("small", compile_generator_expr));

end;
