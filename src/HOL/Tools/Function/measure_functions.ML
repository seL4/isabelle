(*  Title:       HOL/Tools/Function/measure_functions.ML
    Author:      Alexander Krauss, TU Muenchen

Measure functions, generated heuristically.
*)

signature MEASURE_FUNCTIONS =
sig

  val get_measure_functions : Proof.context -> typ -> term list
  val setup : theory -> theory

end

structure MeasureFunctions : MEASURE_FUNCTIONS =
struct

(** User-declared size functions **)
structure Measure_Heuristic_Rules = Named_Thms
(
  val name = @{binding measure_function}
  val description =
    "rules that guide the heuristic generation of measure functions"
);

fun mk_is_measure t =
  Const (@{const_name is_measure}, fastype_of t --> HOLogic.boolT) $ t

fun find_measures ctxt T =
  DEPTH_SOLVE (resolve_tac (Measure_Heuristic_Rules.get ctxt) 1)
    (HOLogic.mk_Trueprop (mk_is_measure (Var (("f",0), T --> HOLogic.natT)))
     |> cterm_of (Proof_Context.theory_of ctxt) |> Goal.init)
  |> Seq.map (prop_of #> (fn _ $ (_ $ (_ $ f)) => f))
  |> Seq.list_of


(** Generating Measure Functions **)

fun constant_0 T = Abs ("x", T, HOLogic.zero)
fun constant_1 T = Abs ("x", T, HOLogic.Suc_zero)

fun mk_funorder_funs (Type (@{type_name Sum_Type.sum}, [fT, sT])) =
  map (fn m => SumTree.mk_sumcase fT sT HOLogic.natT m (constant_0 sT)) (mk_funorder_funs fT)
  @ map (fn m => SumTree.mk_sumcase fT sT HOLogic.natT (constant_0 fT) m) (mk_funorder_funs sT)
  | mk_funorder_funs T = [ constant_1 T ]

fun mk_ext_base_funs ctxt (Type (@{type_name Sum_Type.sum}, [fT, sT])) =
    map_product (SumTree.mk_sumcase fT sT HOLogic.natT)
      (mk_ext_base_funs ctxt fT) (mk_ext_base_funs ctxt sT)
  | mk_ext_base_funs ctxt T = find_measures ctxt T

fun mk_all_measure_funs ctxt (T as Type (@{type_name Sum_Type.sum}, _)) =
    mk_ext_base_funs ctxt T @ mk_funorder_funs T
  | mk_all_measure_funs ctxt T = find_measures ctxt T

val get_measure_functions = mk_all_measure_funs

val setup = Measure_Heuristic_Rules.setup

end
