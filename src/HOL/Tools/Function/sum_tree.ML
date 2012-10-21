(*  Title:      HOL/Tools/Function/sum_tree.ML
    Author:     Alexander Krauss, TU Muenchen

Some common tools for working with sum types in balanced tree form.
*)

signature SUM_TREE =
sig
  val sumcase_split_ss: simpset
  val access_top_down: {init: 'a, left: 'a -> 'a, right: 'a -> 'a} -> int -> int -> 'a
  val mk_sumT: typ -> typ -> typ
  val mk_sumcase: typ -> typ -> typ -> term -> term -> term
  val App: term -> term -> term
  val mk_inj: typ -> int -> int -> term -> term
  val mk_proj: typ -> int -> int -> term -> term
  val mk_sumcases: typ -> term list -> term
end

structure SumTree: SUM_TREE =
struct

(* Theory dependencies *)
val sumcase_split_ss =
  HOL_basic_ss addsimps (@{thm Product_Type.split} :: @{thms sum.cases})

(* top-down access in balanced tree *)
fun access_top_down {left, right, init} len i =
  Balanced_Tree.access
    {left = (fn f => f o left), right = (fn f => f o right), init = I} len i init

(* Sum types *)
fun mk_sumT LT RT = Type (@{type_name Sum_Type.sum}, [LT, RT])
fun mk_sumcase TL TR T l r =
  Const (@{const_name sum.sum_case},
    (TL --> T) --> (TR --> T) --> mk_sumT TL TR --> T) $ l $ r

val App = curry op $

fun mk_inj ST n i =
  access_top_down
  { init = (ST, I : term -> term),
    left = (fn (T as Type (@{type_name Sum_Type.sum}, [LT, RT]), inj) =>
      (LT, inj o App (Const (@{const_name Inl}, LT --> T)))),
    right =(fn (T as Type (@{type_name Sum_Type.sum}, [LT, RT]), inj) =>
      (RT, inj o App (Const (@{const_name Inr}, RT --> T))))} n i
  |> snd

fun mk_proj ST n i =
  access_top_down
  { init = (ST, I : term -> term),
    left = (fn (T as Type (@{type_name Sum_Type.sum}, [LT, RT]), proj) =>
      (LT, App (Const (@{const_name Sum_Type.Projl}, T --> LT)) o proj)),
    right =(fn (T as Type (@{type_name Sum_Type.sum}, [LT, RT]), proj) =>
      (RT, App (Const (@{const_name Sum_Type.Projr}, T --> RT)) o proj))} n i
  |> snd

fun mk_sumcases T fs =
  Balanced_Tree.make (fn ((f, fT), (g, gT)) => (mk_sumcase fT gT T f g, mk_sumT fT gT))
    (map (fn f => (f, domain_type (fastype_of f))) fs)
  |> fst

end
