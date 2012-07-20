(*  Title:      Provers/Arith/cancel_sums.ML
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
  val mk_plus: term * term -> term
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  (*rules*)
  val norm_tac: simpset -> tactic            (*AC0 etc.*)
  val cancel_rule: thm                       (* x + A ~~ x + B == A ~~ B *)
end;

signature CANCEL_SUMS =
sig
  val proc: simpset -> term -> thm option
end;


functor CancelSumsFun(Data: CANCEL_SUMS_DATA): CANCEL_SUMS =
struct


(* cancel *)

fun cons1 x (xs, y, z) = (x :: xs, y, z);
fun cons2 y (x, ys, z) = (x, y :: ys, z);

(*symmetric difference of multisets -- assumed to be sorted wrt. Term_Ord.term_ord*)
fun cancel ts [] vs = (ts, [], vs)
  | cancel [] us vs = ([], us, vs)
  | cancel (t :: ts) (u :: us) vs =
      (case Term_Ord.term_ord (t, u) of
        EQUAL => cancel ts us (t :: vs)
      | LESS => cons1 t (cancel ts (u :: us) vs)
      | GREATER => cons2 u (cancel (t :: ts) us vs));


(* the simplification procedure *)

fun proc ss t =
  (case try Data.dest_bal t of
    NONE => NONE
  | SOME bal =>
      let
        val thy = Proof_Context.theory_of (Simplifier.the_context ss);
        val (ts, us) = pairself (sort Term_Ord.term_ord o Data.dest_sum) bal;
        val (ts', us', vs) = cancel ts us [];
      in
        if null vs then NONE
        else
          let
            val cert = Thm.cterm_of thy
            val t' = Data.mk_sum ts'
            val u' = Data.mk_sum us'
            val v = Data.mk_sum vs
            val t1 = Data.mk_bal (Data.mk_plus (v, t'), Data.mk_plus (v, u'))
            val t2 = Data.mk_bal (t', u')
            val goal1 = Thm.cterm_of thy (Logic.mk_equals (t, t1))
            val goal2 = Thm.cterm_of thy (Logic.mk_equals (t1, t2))
            val thm1 = Goal.prove_internal [] goal1 (K (Data.norm_tac ss))
            val thm2 = Goal.prove_internal [] goal2 (K (rtac Data.cancel_rule 1))
          in
            SOME (Thm.transitive thm1 thm2)
          end
      end);

end;
