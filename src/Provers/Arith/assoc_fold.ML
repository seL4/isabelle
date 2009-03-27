(*  Title:      Provers/Arith/assoc_fold.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Simplification procedure for associative operators + and * on numeric
types.  Performs constant folding when the literals are separated, as
in 3+n+4.
*)

signature ASSOC_FOLD_DATA =
sig
  val assoc_ss: simpset
  val eq_reflection: thm
  val is_numeral: term -> bool
end;

signature ASSOC_FOLD =
sig
  val proc: simpset -> term -> thm option
end;

functor Assoc_Fold(Data: ASSOC_FOLD_DATA): ASSOC_FOLD =
struct

exception Assoc_fail;

fun mk_sum plus []  = raise Assoc_fail
  | mk_sum plus tms = foldr1 (fn (x, y) => plus $ x $ y) tms;

(*Separate the literals from the other terms being combined*)
fun sift_terms plus (t, (lits,others)) =
  if Data.is_numeral t then (t::lits, others) (*new literal*) else
  (case t of
    (f as Const _) $ x $ y =>
      if f = plus
      then sift_terms plus (x, sift_terms plus (y, (lits,others)))
      else (lits, t::others)    (*arbitrary summand*)
  | _ => (lits, t::others));

(*A simproc to combine all literals in a associative nest*)
fun proc ss lhs =
  let
    val plus = (case lhs of f $ _ $ _ => f | _ => error "Assoc_fold: bad pattern")
    val (lits, others) = sift_terms plus (lhs, ([],[]))
    val _ = length lits < 2 andalso raise Assoc_fail (*we can't reduce the number of terms*)
    val rhs = plus $ mk_sum plus lits $ mk_sum plus others
    val th = Goal.prove (Simplifier.the_context ss) [] [] (Logic.mk_equals (lhs, rhs))
      (fn _ => rtac Data.eq_reflection 1 THEN
          simp_tac (Simplifier.inherit_context ss Data.assoc_ss) 1)
  in SOME th end handle Assoc_fail => NONE;

end;
