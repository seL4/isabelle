(* Author: Lukas Bulwahn, TU Muenchen

A quickcheck generator based on the predicate compiler
*)

signature PRED_COMPILE_QUICKCHECK =
sig
  val quickcheck : Proof.context -> term -> int -> term list option
  val test_ref :
    ((unit -> int -> int * int -> term list Predicate.pred * (int * int)) option) Unsynchronized.ref
end;

structure Pred_Compile_Quickcheck : PRED_COMPILE_QUICKCHECK =
struct

val test_ref =
  Unsynchronized.ref (NONE : (unit -> int -> int * int -> term list Predicate.pred * (int * int)) option)
val target = "Quickcheck"

fun dest_compfuns (Predicate_Compile_Core.CompilationFuns funs) = funs
val mk_predT = #mk_predT (dest_compfuns Predicate_Compile_Core.pred_compfuns)
val mk_rpredT = #mk_predT (dest_compfuns Predicate_Compile_Core.rpred_compfuns)
val mk_return = #mk_single (dest_compfuns Predicate_Compile_Core.rpred_compfuns)
val mk_bind = #mk_bind (dest_compfuns Predicate_Compile_Core.rpred_compfuns)
val lift_pred = #lift_pred (dest_compfuns Predicate_Compile_Core.rpred_compfuns)

fun mk_split_lambda [] t = Abs ("u", HOLogic.unitT, t)
  | mk_split_lambda [x] t = lambda x t
  | mk_split_lambda xs t =
  let
    fun mk_split_lambda' (x::y::[]) t = HOLogic.mk_split (lambda x (lambda y t))
      | mk_split_lambda' (x::xs) t = HOLogic.mk_split (lambda x (mk_split_lambda' xs t))
  in
    mk_split_lambda' xs t
  end;

fun strip_imp_prems (Const("op -->", _) $ A $ B) = A :: strip_imp_prems B
  | strip_imp_prems _ = [];

fun strip_imp_concl (Const("op -->", _) $ A $ B) = strip_imp_concl B
  | strip_imp_concl A = A : term;

fun strip_horn A = (strip_imp_prems A, strip_imp_concl A);

fun quickcheck ctxt t =
  let
    val _ = tracing ("Starting quickcheck with " ^ (Syntax.string_of_term ctxt t))
    val ctxt' = ProofContext.theory (Context.copy_thy) ctxt
    val thy = (ProofContext.theory_of ctxt') 
    val (vs, t') = strip_abs t
    val vs' = Variable.variant_frees ctxt' [] vs
    val t'' = subst_bounds (map Free (rev vs'), t')
    val (prems, concl) = strip_horn t''
    val constname = "pred_compile_quickcheck"
    val full_constname = Sign.full_bname thy constname
    val constT = map snd vs' ---> @{typ bool}
    val thy' = Sign.add_consts_i [(Binding.name constname, constT, NoSyn)] thy
    val t = Logic.list_implies
      (map HOLogic.mk_Trueprop (prems @ [HOLogic.mk_not concl]),
       HOLogic.mk_Trueprop (list_comb (Const (full_constname, constT), map Free vs')))
    val tac = fn {...} => setmp quick_and_dirty true (SkipProof.cheat_tac thy')
    val intro = Goal.prove (ProofContext.init thy') (map fst vs') [] t tac
    val _ = tracing (Display.string_of_thm ctxt' intro)
    val thy'' = thy'
      |> Context.theory_map (Predicate_Compile_Preproc_Const_Defs.add_thm intro)
      |> Predicate_Compile.preprocess Predicate_Compile_Aux.default_options full_constname
      |> Predicate_Compile_Core.add_equations Predicate_Compile_Aux.default_options [full_constname]
      (*  |> Predicate_Compile_Core.add_depth_limited_equations Predicate_Compile_Aux.default_options [full_constname]*)
      |> Predicate_Compile_Core.add_quickcheck_equations Predicate_Compile_Aux.default_options [full_constname]
    val depth_limited_modes = Predicate_Compile_Core.depth_limited_modes_of thy'' full_constname
    val modes = Predicate_Compile_Core.generator_modes_of thy'' full_constname  
    val prog =
      if member (op =) modes ([], []) then
        let
          val name = Predicate_Compile_Core.generator_name_of thy'' full_constname ([], [])
          val T = [@{typ bool}, @{typ code_numeral}] ---> (mk_rpredT (HOLogic.mk_tupleT (map snd vs')))
          in Const (name, T) $ @{term True} $ Bound 0 end
      else if member (op =) depth_limited_modes ([], []) then
        let
          val name = Predicate_Compile_Core.depth_limited_function_name_of thy'' full_constname ([], [])
          val T = @{typ code_numeral} --> (mk_predT (HOLogic.mk_tupleT (map snd vs')))
        in lift_pred (Const (name, T) $ Bound 0) end
      else error "Predicate Compile Quickcheck failed"
    val qc_term = Abs ("size", @{typ code_numeral}, mk_bind (prog,
      mk_split_lambda (map Free vs') (mk_return (HOLogic.mk_list @{typ term}
      (map2 HOLogic.mk_term_of (map snd vs') (map Free vs'))))))
    val _ = tracing (Syntax.string_of_term ctxt' qc_term)
    val compile = Code_ML.eval (SOME target) ("Pred_Compile_Quickcheck.test_ref", test_ref)
      (fn proc => fn g => fn s => g s #>> (Predicate.map o map) proc)
      thy'' qc_term []
  in
    ((compile #> Random_Engine.run) #> (Option.map fst o Predicate.yield))
  end

end;
