(*  Title:      HOL/Tools/Lifting/lifting_util.ML
    Author:     Ondrej Kuncar

General-purpose functions used by the Lifting package.
*)

signature LIFTING_UTIL =
sig
  val MRSL: thm list * thm -> thm
  val Trueprop_conv: conv -> conv
  val dest_Quotient: term -> term * term * term * term

  val quot_thm_rel: thm -> term
  val quot_thm_abs: thm -> term
  val quot_thm_rep: thm -> term
  val quot_thm_rty_qty: thm -> typ * typ
end;


structure Lifting_Util: LIFTING_UTIL =
struct

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

fun Trueprop_conv cv ct =
  (case Thm.term_of ct of
    Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv cv ct
  | _ => raise CTERM ("Trueprop_conv", [ct]))

fun dest_Quotient (Const (@{const_name Quotient}, _) $ rel $ abs $ rep $ cr)
      = (rel, abs, rep, cr)
  | dest_Quotient t = raise TERM ("dest_Quotient", [t])

(*
  quot_thm_rel, quot_thm_abs, quot_thm_rep and quot_thm_rty_qty - simple functions
    for destructing quotient theorems (Quotient R Abs Rep T).
*)

fun quot_thm_rel quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (rel, _, _, _) => rel

fun quot_thm_abs quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (_, abs, _, _) => abs

fun quot_thm_rep quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (_, _, rep, _) => rep

fun quot_thm_rty_qty quot_thm =
  let
    val abs = quot_thm_abs quot_thm
    val abs_type = fastype_of abs  
  in
    (domain_type abs_type, range_type abs_type)
  end

end;
