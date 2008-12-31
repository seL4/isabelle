(*  Title:      Provers/Arith/cancel_factor.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Cancel common constant factor from balanced exression (e.g. =, <=, < of sums).
*)

signature CANCEL_FACTOR_DATA =
sig
  (*abstract syntax*)
  val mk_sum: term list -> term
  val dest_sum: term -> term list
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  (*rules*)
  val prove_conv: tactic -> tactic -> Proof.context -> term * term -> thm
  val norm_tac: tactic (*AC0 etc.*)
  val multiply_tac: integer -> tactic
    (*apply a ~~ b  ==  k * a ~~ k * b  (for k > 0)*)
end;

signature CANCEL_FACTOR =
sig
  val proc: simpset -> term -> thm option
end;


functor CancelFactorFun(Data: CANCEL_FACTOR_DATA): CANCEL_FACTOR =
struct


(* count terms *)

fun ins_term (t, []) = [(t, 1)]
  | ins_term (t, (u, k) :: uks) =
      if t aconv u then (u, k + 1) :: uks
      else (t, 1) :: (u, k) :: uks;

fun count_terms ts = foldr ins_term (sort TermOrd.term_ord ts, []);


(* divide sum *)

fun div_sum d =
  Data.mk_sum o maps (fn (t, k) => replicate (k div d) t);


(* the simplification procedure *)

fun proc ss t =
  (case try Data.dest_bal t of
    NONE => NONE
  | SOME bal =>
      (case pairself Data.dest_sum bal of
        ([_], _) => NONE
      | (_, [_]) => NONE
      | ts_us =>
          let
            val (tks, uks) = pairself count_terms ts_us;
            val d = 0
              |> fold (Integer.gcd o snd) tks
              |> fold (Integer.gcd o snd) uks;
          in
            if d = 0 orelse d = 1 then NONE
            else SOME
              (Data.prove_conv (Data.multiply_tac d) Data.norm_tac (Simplifier.the_context ss)
                (t, Data.mk_bal (div_sum d tks, div_sum d uks)))
          end));


end;
