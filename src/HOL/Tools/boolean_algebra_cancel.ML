(*  Title:      HOL/Tools/boolean_algebra_cancel.ML
    Author:     Andreas Lochbihler, ETH Zurich

Simplification procedures for boolean algebras:
- Cancel complementary terms sup and inf.
*)

signature BOOLEAN_ALGEBRA_CANCEL =
sig
  val cancel_sup_conv: conv
  val cancel_inf_conv: conv
end

structure Boolean_Algebra_Cancel: BOOLEAN_ALGEBRA_CANCEL =
struct

fun move_to_front rule path = Conv.rewr_conv (Library.foldl (op RS) (rule, path))

fun add_atoms sup pos path (t as \<^Const_>\<open>sup _ for x y\<close>) =
    if sup then
      add_atoms sup pos (@{thm boolean_algebra_cancel.sup1}::path) x #>
      add_atoms sup pos (@{thm boolean_algebra_cancel.sup2}::path) y
    else cons ((pos, t), path)
  | add_atoms sup pos path (t as \<^Const_>\<open>inf _ for x y\<close>) =
    if not sup then
      add_atoms sup pos (@{thm boolean_algebra_cancel.inf1}::path) x #>
      add_atoms sup pos (@{thm boolean_algebra_cancel.inf2}::path) y
    else cons ((pos, t), path)
  | add_atoms _ _ _ \<^Const_>\<open>bot _\<close> = I
  | add_atoms _ _ _ \<^Const_>\<open>top _\<close> = I
  | add_atoms _ pos path \<^Const_>\<open>uminus _ for x\<close> = cons ((not pos, x), path)
  | add_atoms _ pos path x = cons ((pos, x), path);

fun atoms sup pos t = add_atoms sup pos [] t []

val coeff_ord = prod_ord bool_ord Term_Ord.term_ord

fun find_common ord xs ys =
  let
    fun find (xs as (x, px)::xs') (ys as (y, py)::ys') =
        (case ord (x, y) of
          EQUAL => SOME (fst x, px, py)
        | LESS => find xs' ys
        | GREATER => find xs ys')
      | find _ _ = NONE
    fun ord' ((x, _), (y, _)) = ord (x, y)
  in
    find (sort ord' xs) (sort ord' ys)
  end

fun cancel_conv sup rule ct =
  let
    val rule0 =
      if sup then @{thm boolean_algebra_cancel.sup0} else @{thm boolean_algebra_cancel.inf0}
    fun cancel1_conv (pos, lpath, rpath) =
      let
        val lconv = move_to_front rule0 lpath
        val rconv = move_to_front rule0 rpath
        val conv1 = Conv.combination_conv (Conv.arg_conv lconv) rconv
      in
        conv1 then_conv Conv.rewr_conv (rule pos)
      end
    val ((_, lhs), rhs) = (apfst dest_comb o dest_comb) (Thm.term_of ct)
    val common = find_common coeff_ord (atoms sup true lhs) (atoms sup false rhs)
    val conv =
      case common of NONE => Conv.no_conv
      | SOME x => cancel1_conv x
  in conv ct end

val cancel_sup_conv = cancel_conv true (fn pos => if pos then mk_meta_eq @{thm sup_cancel_left1} else mk_meta_eq @{thm sup_cancel_left2})
val cancel_inf_conv = cancel_conv false (fn pos => if pos then mk_meta_eq @{thm inf_cancel_left1} else mk_meta_eq @{thm inf_cancel_left2})

end
