(*  Title:      Provers/Arith/cancel_factor.ML
    ID:         $Id$
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
  val prove_conv: tactic -> tactic -> Sign.sg -> term * term -> thm
  val norm_tac: tactic			(*AC0 etc.*)
  val multiply_tac: int -> tactic	(*apply a ~~ b  ==  k * a ~~ k * b  (for k > 0)*)
end;

signature CANCEL_FACTOR =
sig
  val proc: Sign.sg -> thm list -> term -> thm option
end;


functor CancelFactorFun(Data: CANCEL_FACTOR_DATA): CANCEL_FACTOR =
struct


(* greatest common divisor *)

fun gcd (0, n) = n
  | gcd (m, n) = gcd (n mod m, m);

val gcds = foldl gcd;


(* count terms *)

fun ins_term (t, []) = [(t, 1)]
  | ins_term (t, (u, k) :: uks) =
      if t aconv u then (u, k + 1) :: uks
      else (t, 1) :: (u, k) :: uks;

fun count_terms ts = foldr ins_term (sort Logic.termless ts, []);


(* divide sum *)

fun div_sum d tks =
  Data.mk_sum (flat (map (fn (t, k) => replicate (k div d) t) tks));


(* the simplification procedure *)

fun proc sg _ t =
  (case try Data.dest_bal t of
    None => None
  | Some bal =>
      (case pairself Data.dest_sum bal of
        ([_], _) => None
      | (_, [_]) => None
      | ts_us =>
          let
            val (tks, uks) = pairself count_terms ts_us;
            val d = gcds (gcds (0, map snd tks), map snd uks);
          in
            if d = 0 orelse d = 1 then None
            else Some
              (Data.prove_conv (Data.multiply_tac d) Data.norm_tac sg
                (t, Data.mk_bal (div_sum d tks, div_sum d uks)))
          end));


end;
