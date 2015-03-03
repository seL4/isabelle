(*  Title:       HOL/Tools/Function/measure_functions.ML
    Author:      Alexander Krauss, TU Muenchen

Measure functions, generated heuristically.
*)

signature MEASURE_FUNCTIONS =
sig
  val get_measure_functions : Proof.context -> typ -> term list
end

structure Measure_Functions : MEASURE_FUNCTIONS =
struct

(** User-declared size functions **)

fun mk_is_measure t =
  Const (@{const_name is_measure}, fastype_of t --> HOLogic.boolT) $ t

fun find_measures ctxt T =
  DEPTH_SOLVE (resolve_tac ctxt (rev (Named_Theorems.get ctxt @{named_theorems measure_function})) 1)
    (HOLogic.mk_Trueprop (mk_is_measure (Var (("f",0), T --> HOLogic.natT)))
     |> Proof_Context.cterm_of ctxt |> Goal.init)
  |> Seq.map (prop_of #> (fn _ $ (_ $ (_ $ f)) => f))
  |> Seq.list_of


(** Generating Measure Functions **)

fun constant_0 T = Abs ("x", T, HOLogic.zero)
fun constant_1 T = Abs ("x", T, HOLogic.Suc_zero)

fun mk_funorder_funs (Type (@{type_name Sum_Type.sum}, [fT, sT])) =
  map (fn m => Sum_Tree.mk_sumcase fT sT HOLogic.natT m (constant_0 sT)) (mk_funorder_funs fT)
  @ map (fn m => Sum_Tree.mk_sumcase fT sT HOLogic.natT (constant_0 fT) m) (mk_funorder_funs sT)
  | mk_funorder_funs T = [ constant_1 T ]

fun mk_ext_base_funs ctxt (Type (@{type_name Sum_Type.sum}, [fT, sT])) =
    map_product (Sum_Tree.mk_sumcase fT sT HOLogic.natT)
      (mk_ext_base_funs ctxt fT) (mk_ext_base_funs ctxt sT)
  | mk_ext_base_funs ctxt T = find_measures ctxt T

fun mk_all_measure_funs ctxt (T as Type (@{type_name Sum_Type.sum}, _)) =
    mk_ext_base_funs ctxt T @ mk_funorder_funs T
  | mk_all_measure_funs ctxt T = find_measures ctxt T

val get_measure_functions = mk_all_measure_funs

end
