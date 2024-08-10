(*  Title:      HOL/Tools/Lifting/lifting_util.ML
    Author:     Ondrej Kuncar

General-purpose functions used by the Lifting package.
*)

signature LIFTING_UTIL =
sig
  val MRSL: thm list * thm -> thm
  val mk_Quotient: term * term * term * term -> term
  val dest_Quotient: term -> term * term * term * term

  val quot_thm_rel: thm -> term
  val quot_thm_abs: thm -> term
  val quot_thm_rep: thm -> term
  val quot_thm_crel: thm -> term
  val quot_thm_rty_qty: thm -> typ * typ
  val Quotient_conv: conv -> conv -> conv -> conv -> conv
  val Quotient_R_conv: conv -> conv

  val undisch: thm -> thm
  val undisch_all: thm -> thm
  val get_args: int -> term -> term list
  val strip_args: int -> term -> term
  val all_args_conv: conv -> conv
  val Targs: typ -> typ list
  val Tname: typ -> string
  val relation_types: typ -> typ * typ
  val map_interrupt: ('a -> 'b option) -> 'a list -> 'b list option
  val conceal_naming_result: (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory
end

structure Lifting_Util: LIFTING_UTIL =
struct

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

fun mk_Quotient (rel, abs, rep, cr) =
  let val \<^Type>\<open>fun A B\<close> = fastype_of abs
  in \<^Const>\<open>Quotient A B for rel abs rep cr\<close> end

fun dest_Quotient \<^Const_>\<open>Quotient _ _ for rel abs rep cr\<close> = (rel, abs, rep, cr)
  | dest_Quotient t = raise TERM ("dest_Quotient", [t])

val dest_Quotient_thm = dest_Quotient o HOLogic.dest_Trueprop o Thm.prop_of

val quot_thm_rel = #1 o dest_Quotient_thm
val quot_thm_abs = #2 o dest_Quotient_thm
val quot_thm_rep = #3 o dest_Quotient_thm
val quot_thm_crel = #4 o dest_Quotient_thm

fun quot_thm_rty_qty quot_thm =
  let val \<^Type>\<open>fun A B\<close> = fastype_of (quot_thm_abs quot_thm)
  in (A, B) end

fun Quotient_conv R_conv Abs_conv Rep_conv T_conv =
  Conv.combination_conv (Conv.combination_conv
    (Conv.combination_conv (Conv.arg_conv R_conv) Abs_conv) Rep_conv) T_conv

fun Quotient_R_conv R_conv =
  Quotient_conv R_conv Conv.all_conv Conv.all_conv Conv.all_conv

fun undisch thm =
  let val assm = Thm.cprem_of thm 1
  in Thm.implies_elim thm (Thm.assume assm) end

fun undisch_all thm = funpow (Thm.nprems_of thm) undisch thm

fun get_args n = rev o fst o funpow_yield n (swap o dest_comb)

fun strip_args n = funpow n (fst o dest_comb)

fun all_args_conv conv ctm =
  Conv.try_conv (Conv.combination_conv (all_args_conv conv) conv) ctm

fun Targs T = if is_Type T then dest_Type_args T else []
fun Tname T = if is_Type T then dest_Type_name T else ""

fun relation_types typ =
  (case strip_type typ of
    ([typ1, typ2], \<^Type>\<open>bool\<close>) => (typ1, typ2)
  | _ => error "relation_types: not a relation")

fun map_interrupt f l =
  let
    fun map_interrupt' _ [] l = SOME (rev l)
      | map_interrupt' f (x::xs) l =
          (case f x of
            NONE => NONE
          | SOME v => map_interrupt' f xs (v::l))
  in map_interrupt' f l [] end

fun conceal_naming_result f lthy =
  lthy |> Proof_Context.concealed |> f ||> Proof_Context.restore_naming lthy

end
