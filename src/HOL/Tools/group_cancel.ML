(*  Title:      HOL/Tools/group_cancel.ML
    Author:     Brian Huffman, TU Munich

Simplification procedures for abelian groups:
- Cancel complementary terms in sums.
- Cancel like terms on opposite sides of relations.
*)

signature GROUP_CANCEL =
sig
  val cancel_diff_conv: conv
  val cancel_eq_conv: conv
  val cancel_le_conv: conv
  val cancel_less_conv: conv
  val cancel_add_conv: conv
end

structure Group_Cancel: GROUP_CANCEL =
struct

val minus_minus = mk_meta_eq @{thm minus_minus}

fun move_to_front path = Conv.every_conv
    [Conv.rewr_conv (Library.foldl (op RS) (@{thm group_cancel.rule0}, path)),
     Conv.arg1_conv (Conv.repeat_conv (Conv.rewr_conv minus_minus))]

fun add_atoms pos path \<^Const_>\<open>plus _ for x y\<close> =
      add_atoms pos (@{thm group_cancel.add1}::path) x #>
      add_atoms pos (@{thm group_cancel.add2}::path) y
  | add_atoms pos path \<^Const_>\<open>minus _ for x y\<close> =
      add_atoms pos (@{thm group_cancel.sub1}::path) x #>
      add_atoms (not pos) (@{thm group_cancel.sub2}::path) y
  | add_atoms pos path \<^Const_>\<open>uminus _ for x\<close> =
      add_atoms (not pos) (@{thm group_cancel.neg1}::path) x
  | add_atoms _ _ \<^Const_>\<open>Groups.zero _\<close> = I
  | add_atoms pos path x = cons ((pos, x), path)

fun atoms t = add_atoms true [] t []

val coeff_ord = prod_ord bool_ord Term_Ord.term_ord

fun find_all_common ord xs ys =
  let
    fun find (xs as (x, px)::xs') (ys as (y, py)::ys') =
        (case ord (x, y) of
          EQUAL => (px, py) :: find xs' ys'
        | LESS => find xs' ys
        | GREATER => find xs ys')
      | find _ _ = []
    fun ord' ((x, _), (y, _)) = ord (x, y)
  in
    find (sort ord' xs) (sort ord' ys)
  end

fun cancel_conv rule ct =
  let
    fun cancel1_conv (lpath, rpath) =
      let
        val lconv = move_to_front lpath
        val rconv = move_to_front rpath
        val conv1 = Conv.combination_conv (Conv.arg_conv lconv) rconv
      in
        conv1 then_conv Conv.rewr_conv rule
      end
    val ((_, lhs), rhs) = (apfst dest_comb o dest_comb) (Thm.term_of ct)
    val common = find_all_common coeff_ord (atoms lhs) (atoms rhs)
    val conv =
      if null common then Conv.no_conv
      else Conv.every_conv (map cancel1_conv common)
  in conv ct end

val cancel_diff_conv = cancel_conv (mk_meta_eq @{thm add_diff_cancel_left})
val cancel_eq_conv = cancel_conv (mk_meta_eq @{thm add_left_cancel})
val cancel_le_conv = cancel_conv (mk_meta_eq @{thm add_le_cancel_left})
val cancel_less_conv = cancel_conv (mk_meta_eq @{thm add_less_cancel_left})

val diff_minus_eq_add = mk_meta_eq @{thm diff_minus_eq_add}
val add_eq_diff_minus = Thm.symmetric diff_minus_eq_add
val cancel_add_conv = Conv.every_conv
  [Conv.rewr_conv add_eq_diff_minus,
   cancel_diff_conv,
   Conv.rewr_conv diff_minus_eq_add]

end
