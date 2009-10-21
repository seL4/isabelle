(*  Title:      Provers/Arith/cancel_div_mod.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen

Cancel div and mod terms:

  A + n*(m div n) + B + (m mod n) + C  ==  A + B + C + m

FIXME: Is parameterized but assumes for simplicity that + and * are named
HOL.plus and HOL.minus
*)

signature CANCEL_DIV_MOD_DATA =
sig
  (*abstract syntax*)
  val div_name: string
  val mod_name: string
  val mk_binop: string -> term * term -> term
  val mk_sum: term list -> term
  val dest_sum: term -> term list
  (*logic*)
  val div_mod_eqs: thm list
  (* (n*(m div n) + m mod n) + k == m + k and
     ((m div n)*n + m mod n) + k == m + k *)
  val prove_eq_sums: simpset -> term * term -> thm
  (* must prove ac0-equivalence of sums *)
end;

signature CANCEL_DIV_MOD =
sig
  val proc: simpset -> term -> thm option
end;


functor CancelDivModFun(Data: CANCEL_DIV_MOD_DATA): CANCEL_DIV_MOD =
struct

fun coll_div_mod (Const(@{const_name HOL.plus},_) $ s $ t) dms =
      coll_div_mod t (coll_div_mod s dms)
  | coll_div_mod (Const(@{const_name HOL.times},_) $ m $ (Const(d,_) $ s $ n))
                 (dms as (divs,mods)) =
      if d = Data.div_name andalso m=n then ((s,n)::divs,mods) else dms
  | coll_div_mod (Const(@{const_name HOL.times},_) $ (Const(d,_) $ s $ n) $ m)
                 (dms as (divs,mods)) =
      if d = Data.div_name andalso m=n then ((s,n)::divs,mods) else dms
  | coll_div_mod (Const(m,_) $ s $ n) (dms as (divs,mods)) =
      if m = Data.mod_name then (divs,(s,n)::mods) else dms
  | coll_div_mod _ dms = dms;


(* Proof principle:
   1. (...div...)+(...mod...) == (div + mod) + rest
      in function rearrange
   2. (div + mod) + ?x = d + ?x
      Data.div_mod_eq
   ==> thesis by transitivity
*)

val mk_plus = Data.mk_binop @{const_name HOL.plus};
val mk_times = Data.mk_binop @{const_name HOL.times};

fun rearrange t pq =
  let val ts = Data.dest_sum t;
      val dpq = Data.mk_binop Data.div_name pq
      val d1 = mk_times (snd pq,dpq) and d2 = mk_times (dpq,snd pq)
      val d = if d1 mem ts then d1 else d2
      val m = Data.mk_binop Data.mod_name pq
  in mk_plus(mk_plus(d,m),Data.mk_sum(ts \ d \ m)) end

fun cancel ss t pq =
  let val teqt' = Data.prove_eq_sums ss (t, rearrange t pq)
  in hd (Data.div_mod_eqs RL [teqt' RS transitive_thm]) end;

fun proc ss t =
  let val (divs,mods) = coll_div_mod t ([],[])
  in if null divs orelse null mods then NONE
     else case inter (op =) (divs, mods) of
            pq :: _ => SOME (cancel ss t pq)
          | [] => NONE
  end

end
