(*  Title:      Provers/Arith/cancel_sums.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Cancel common summands of balanced expressions:

  A + x + B ~~ A' + x + B'  ==  A + B ~~ A' + B'

where + is AC0 and ~~ an appropriate balancing operation (e.g. =, <=, <, -).
*)

signature CANCEL_SUMS_DATA =
sig
  (*abstract syntax*)
  val mk_sum: term list -> term
  val dest_sum: term -> term list
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  (*rules*)
  val prove_conv: tactic -> tactic -> Sign.sg -> term * term -> thm
  val norm_tac: tactic                   	(*AC0 etc.*)
  val uncancel_tac: cterm -> tactic      	(*apply A ~~ B  ==  x + A ~~ x + B*)
end;

signature CANCEL_SUMS =
sig
  val proc: Sign.sg -> thm list -> term -> thm option
end;


functor CancelSumsFun(Data: CANCEL_SUMS_DATA): CANCEL_SUMS =
struct


(* cancel *)

fun cons1 x (xs, y, z) = (x :: xs, y, z);
fun cons2 y (x, ys, z) = (x, y :: ys, z);
fun cons12 x y (xs, ys, z) = (x :: xs, y :: ys, z);

(*symmetric difference of multisets -- assumed to be sorted wrt. Logic.termord*)
fun cancel ts [] vs = (ts, [], vs)
  | cancel [] us vs = ([], us, vs)
  | cancel (t :: ts) (u :: us) vs =
      (case Logic.termord (t, u) of
        EQUAL =>
          if t aconv u then cancel ts us (t :: vs)
          else cons12 t u (cancel ts us vs)
            (*potential incompleteness! -- termord not strictly antisymmetric*)
      | LESS => cons1 t (cancel ts (u :: us) vs)
      | GREATER => cons2 u (cancel (t :: ts) us vs));


(* uncancel *)

fun uncancel_sums_tac _ [] = all_tac
  | uncancel_sums_tac sg (t :: ts) =
      Data.uncancel_tac (Thm.cterm_of sg t) THEN
      uncancel_sums_tac sg ts;


(* the simplification procedure *)

fun proc sg _ t =
  (case try Data.dest_bal t of
    None => None
  | Some bal =>
      let
        val (ts, us) = pairself (sort Logic.termless o Data.dest_sum) bal;
        val (ts', us', vs) = cancel ts us [];
      in
        if null vs then None
        else Some
          (Data.prove_conv (uncancel_sums_tac sg vs) Data.norm_tac sg
            (t, Data.mk_bal (Data.mk_sum ts', Data.mk_sum us')))
      end);


end;
