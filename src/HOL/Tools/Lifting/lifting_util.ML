(*  Title:      HOL/Tools/Lifting/lifting_util.ML
    Author:     Ondrej Kuncar

General-purpose functions used by the Lifting package.
*)

signature LIFTING_UTIL =
sig
  val MRSL: thm list * thm -> thm
  val Trueprop_conv: conv -> conv
  val dest_Quotient: term -> term * term * term * term
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

end;
