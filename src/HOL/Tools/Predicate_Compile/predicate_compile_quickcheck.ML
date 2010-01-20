(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_quickcheck.ML
    Author:     Lukas Bulwahn, TU Muenchen

A quickcheck generator based on the predicate compiler.
*)

signature PREDICATE_COMPILE_QUICKCHECK =
sig
  val quickcheck : Proof.context -> term -> int -> term list option
  val test_ref :
    ((unit -> int -> int -> int * int -> term list DSequence.dseq * (int * int)) option) Unsynchronized.ref
  val tracing : bool Unsynchronized.ref;
end;

structure Predicate_Compile_Quickcheck : PREDICATE_COMPILE_QUICKCHECK =
struct

open Predicate_Compile_Aux;

val test_ref =
  Unsynchronized.ref (NONE : (unit -> int -> int -> int * int -> term list DSequence.dseq * (int * int)) option);

val tracing = Unsynchronized.ref false;

val target = "Quickcheck"

val options = Options {
  expected_modes = NONE,
  proposed_modes = NONE,
  proposed_names = [],
  show_steps = true,
  show_intermediate_results = true,
  show_proof_trace = false,
  show_modes = false,
  show_mode_inference = false,
  show_compilation = false,
  skip_proof = false,
  compilation = Random,
  inductify = false
}

fun dest_compfuns (Predicate_Compile_Core.CompilationFuns funs) = funs
val mk_predT = #mk_predT (dest_compfuns Predicate_Compile_Core.pred_compfuns)
val mk_randompredT = #mk_predT (dest_compfuns Predicate_Compile_Core.randompred_compfuns)
val mk_return = #mk_single (dest_compfuns Predicate_Compile_Core.randompred_compfuns)
val mk_bind = #mk_bind (dest_compfuns Predicate_Compile_Core.randompred_compfuns)

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
    (*val () =
      if !tracing then
        tracing ("Starting quickcheck with " ^ (Syntax.string_of_term ctxt t))
      else
        ()*)
    val ctxt' = ProofContext.theory (Context.copy_thy) ctxt
    val thy = (ProofContext.theory_of ctxt') 
    val (vs, t') = strip_abs t
    val vs' = Variable.variant_frees ctxt' [] vs
    val t'' = subst_bounds (map Free (rev vs'), t')
    val (prems, concl) = strip_horn t''
    val constname = "pred_compile_quickcheck"
    val full_constname = Sign.full_bname thy constname
    val constT = map snd vs' ---> @{typ bool}
    val thy1 = Sign.add_consts_i [(Binding.name constname, constT, NoSyn)] thy
    val const = Const (full_constname, constT)
    val t = Logic.list_implies
      (map HOLogic.mk_Trueprop (prems @ [HOLogic.mk_not concl]),                               
       HOLogic.mk_Trueprop (list_comb (Const (full_constname, constT), map Free vs')))
    val tac = fn _ => Skip_Proof.cheat_tac thy1
    val intro = Goal.prove (ProofContext.init thy1) (map fst vs') [] t tac
    (*val _ = tracing (Display.string_of_thm ctxt' intro)*)
    val thy2 = (*Output.cond_timeit (!Quickcheck.timing) "predicate intros"
      (fn () => *)(Context.theory_map (Predicate_Compile_Alternative_Defs.add_thm intro) thy1)
    val thy3 = (*Output.cond_timeit (!Quickcheck.timing) "predicate preprocessing"
        (fn () =>*) (Predicate_Compile.preprocess options const thy2)
    val thy4 = Output.cond_timeit (!Quickcheck.timing) "random_dseq compilation"
        (fn () => Predicate_Compile_Core.add_random_dseq_equations options [full_constname] thy3)
    (*val depth_limited_modes = Predicate_Compile_Core.modes_of Depth_Limited thy'' full_constname*)
    val modes = Predicate_Compile_Core.modes_of Random_DSeq thy4 full_constname
    val output_mode = fold_rev (curry Fun) (map (K Output) (binder_types constT)) Bool
    val prog =
      if member eq_mode modes output_mode then
        let
          val name = Predicate_Compile_Core.function_name_of Random_DSeq thy4 full_constname output_mode
          val T = (mk_randompredT (HOLogic.mk_tupleT (map snd vs')))
        in
          Const (name, T)
        end
      (*else if member (op =) depth_limited_modes ([], []) then
        let
          val name = Predicate_Compile_Core.depth_limited_function_name_of thy'' full_constname ([], [])
          val T = @{typ code_numeral} --> (mk_predT (HOLogic.mk_tupleT (map snd vs')))
        in lift_pred (Const (name, T) $ Bound 0) end*)
      else error "Predicate Compile Quickcheck failed"
    val qc_term = mk_bind (prog,
      mk_split_lambda (map Free vs') (mk_return (HOLogic.mk_list @{typ term}
      (map2 HOLogic.mk_term_of (map snd vs') (map Free vs')))))
    val compilation =
      Code_Eval.eval NONE ("Predicate_Compile_Quickcheck.test_ref", test_ref)
        (fn proc => fn g => fn n => fn size => fn s => g n size s |>> (DSequence.map o map) proc)
        thy4 qc_term []
  in
    (fn size =>
      Option.map fst (DSequence.yield (compilation size size |> Random_Engine.run) size true))
  end

end;
