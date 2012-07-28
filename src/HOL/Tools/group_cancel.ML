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

val add1 = @{lemma "(A::'a::comm_monoid_add) == k + a ==> A + b == k + (a + b)"
      by (simp only: add_ac)}
val add2 = @{lemma "(B::'a::comm_monoid_add) == k + b ==> a + B == k + (a + b)"
      by (simp only: add_ac)}
val sub1 = @{lemma "(A::'a::ab_group_add) == k + a ==> A - b == k + (a - b)"
      by (simp only: add_diff_eq)}
val sub2 = @{lemma "(B::'a::ab_group_add) == k + b ==> a - B == - k + (a - b)"
      by (simp only: diff_minus minus_add add_ac)}
val neg1 = @{lemma "(A::'a::ab_group_add) == k + a ==> - A == - k + - a"
      by (simp only: minus_add_distrib)}
val rule0 = @{lemma "(a::'a::comm_monoid_add) == a + 0"
      by (simp only: add_0_right)}
val minus_minus = mk_meta_eq @{thm minus_minus}

fun move_to_front path = Conv.every_conv
    [Conv.rewr_conv (Library.foldl (op RS) (rule0, path)),
     Conv.arg1_conv (Conv.repeat_conv (Conv.rewr_conv minus_minus))]

fun add_atoms pos path (Const (@{const_name Groups.plus}, _) $ x $ y) =
      add_atoms pos (add1::path) x #> add_atoms pos (add2::path) y
  | add_atoms pos path (Const (@{const_name Groups.minus}, _) $ x $ y) =
      add_atoms pos (sub1::path) x #> add_atoms (not pos) (sub2::path) y
  | add_atoms pos path (Const (@{const_name Groups.uminus}, _) $ x) =
      add_atoms (not pos) (neg1::path) x
  | add_atoms _ _ (Const (@{const_name Groups.zero}, _)) = I
  | add_atoms pos path x = cons ((pos, x), path)

fun atoms t = add_atoms true [] t []

val coeff_ord = prod_ord bool_ord Term_Ord.term_ord

exception Cancel

fun find_common ord xs ys =
  let
    fun find (xs as (x, px)::xs') (ys as (y, py)::ys') =
        (case ord (x, y) of
          EQUAL => (px, py)
        | LESS => find xs' ys
        | GREATER => find xs ys')
      | find _ _ = raise Cancel
    fun ord' ((x, _), (y, _)) = ord (x, y)
  in
    find (sort ord' xs) (sort ord' ys)
  end

fun cancel_conv rule ct =
  let
    val ((_, lhs), rhs) = (apfst dest_comb o dest_comb) (Thm.term_of ct)
    val (lpath, rpath) = find_common coeff_ord (atoms lhs) (atoms rhs)
    val lconv = move_to_front lpath
    val rconv = move_to_front rpath
    val conv1 = Conv.combination_conv (Conv.arg_conv lconv) rconv
    val conv = conv1 then_conv Conv.rewr_conv rule
  in conv ct end
    handle Cancel => raise CTERM ("no_conversion", [])

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
