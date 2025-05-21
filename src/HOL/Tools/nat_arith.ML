(* Author: Markus Wenzel, Stefan Berghofer, and Tobias Nipkow
   Author: Brian Huffman

Basic arithmetic for natural numbers.
*)

signature NAT_ARITH =
sig
  val cancel_diff_conv: Proof.context -> conv
  val cancel_eq_conv: Proof.context -> conv
  val cancel_le_conv: Proof.context -> conv
  val cancel_less_conv: Proof.context -> conv
end;

structure Nat_Arith: NAT_ARITH =
struct

val norm_rules = map mk_meta_eq @{thms add_0_left add_0_right}

fun move_to_front ctxt path = Conv.every_conv
    [Conv.rewr_conv (Library.foldl (op RS) (@{thm nat_arith.rule0}, path)),
     Conv.arg_conv (Raw_Simplifier.rewrite_wrt ctxt false norm_rules)]

fun add_atoms path \<^Const_>\<open>plus _ for x y\<close> =
      add_atoms (@{thm nat_arith.add1}::path) x #>
      add_atoms (@{thm nat_arith.add2}::path) y
  | add_atoms path \<^Const_>\<open>Suc for x\<close> =
      add_atoms (@{thm nat_arith.suc1}::path) x
  | add_atoms _ \<^Const_>\<open>Groups.zero _\<close> = I
  | add_atoms path x = cons (x, path)

fun atoms t = add_atoms [] t []

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

fun cancel_conv rule ctxt ct =
  let
    val ((_, lhs), rhs) = (apfst dest_comb o dest_comb) (Thm.term_of ct)
    val (lpath, rpath) = find_common Term_Ord.term_ord (atoms lhs) (atoms rhs)
    val lconv = move_to_front ctxt lpath
    val rconv = move_to_front ctxt rpath
    val conv1 = Conv.combination_conv (Conv.arg_conv lconv) rconv
    val conv = conv1 then_conv Conv.rewr_conv rule
  in conv ct end
    handle Cancel => raise CTERM ("no_conversion", [])

val cancel_diff_conv = cancel_conv (mk_meta_eq @{thm add_diff_cancel_left [where ?'a = nat]})
val cancel_eq_conv = cancel_conv (mk_meta_eq @{thm add_left_cancel [where ?'a = nat]})
val cancel_le_conv = cancel_conv (mk_meta_eq @{thm add_le_cancel_left [where ?'a = nat]})
val cancel_less_conv = cancel_conv (mk_meta_eq @{thm add_less_cancel_left [where ?'a = nat]})

end;
