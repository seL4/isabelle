(*  Title:      Pure/General/rat.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Muenchen

Canonical implementation of exact rational numbers.
*)

signature RAT =
sig
  type rat
  exception DIVZERO
  val zero: rat
  val one: rat
  val rat_of_int: int -> rat
  val rat_of_intinf: IntInf.int -> rat
  val rat_of_quotient: IntInf.int * IntInf.int -> rat
  val quotient_of_rat: rat -> IntInf.int * IntInf.int
  val string_of_rat: rat -> string
  val eq: rat * rat -> bool
  val le: rat * rat -> bool
  val lt: rat * rat -> bool
  val ord: rat * rat -> order
  val add: rat * rat -> rat
  val mult: rat * rat -> rat
  val neg: rat -> rat
  val inv: rat -> rat
  val ge0: rat -> bool
  val gt0: rat -> bool
  val roundup: rat -> rat
  val rounddown: rat -> rat
end;

structure Rat: RAT =
struct

(*keep them normalized!*)

datatype rat = Rat of bool * IntInf.int * IntInf.int;

exception DIVZERO;

val zero = Rat (true, 0, 1);

val one = Rat (true, 1, 1);

fun rat_of_intinf i =
  if i < 0
  then Rat (false, ~i, 1)
  else Rat (true, i, 1);

fun rat_of_int i = rat_of_intinf (IntInf.fromInt i);

fun norm (a, 0, q) =
      Rat (true, 0, 1)
  | norm (a, p, q) =
      let
        val absp = abs p
        val m = gcd (absp, q)
      in Rat(a = (0 <= p), absp div m, q div m) end;

fun common (p1, q1, p2, q2) =
  let val q' = lcm (q1, q2)
  in (p1 * (q' div q1), p2 * (q' div q2), q') end

fun rat_of_quotient (p, 0) =
      raise DIVZERO
  | rat_of_quotient (p, q) =
      norm (0 <= q, p, abs q);

fun quotient_of_rat (Rat (a, p, q)) = (if a then p else ~p, q);

fun string_of_rat r =
  let val (p, q) = quotient_of_rat r
  in IntInf.toString p ^ "/" ^ IntInf.toString q end;

fun eq (Rat (false, _, _), Rat (true, _, _)) = false
  | eq (Rat (true, _, _), Rat (false, _, _)) = false
  | eq (Rat (_, p1, q1), Rat (_, p2, q2)) = p1 = p2 andalso q1 = q2

fun le (Rat (false, _, _), Rat (true, _, _)) = true
  | le (Rat (true, _, _), Rat (false, _, _)) = false
  | le (Rat (a, p1, q1), Rat (_, p2, q2)) =
      let val (r1, r2, _) = common (p1, q1, p2, q2)
      in if a then r1 <= r2 else r2 <= r1 end;

fun lt (Rat (false, _, _), Rat (true, _, _)) = true
  | lt (Rat (true, _, _), Rat (false, _, _)) = false
  | lt (Rat (a, p1, q1), Rat (_, p2, q2)) =
      let val (r1, r2, _) = common (p1, q1, p2, q2)
      in if a then r1 <= r2 else r2 <= r1 end;

fun ord (Rat (false, _, _), Rat (true, _, _)) = LESS
  | ord (Rat (true, _, _), Rat (false, _, _)) = GREATER
  | ord (Rat (a, p1, q1), Rat (_, p2, q2)) =
      let val (r1, r2, _) = common (p1, q1, p2, q2)
      in if a then IntInf.compare (r1, r2) else IntInf.compare (r2, r1) end;

fun add (Rat (a1, p1, q1), Rat(a2, p2, q2)) =
  let
    val (r1, r2, den) = common (p1, q1, p2, q2)
    val num = (if a1 then r1 else ~r1) + (if a2 then r2 else ~r2)
  in norm (true, num, den) end;

fun mult (Rat (a1, p1, q1), Rat (a2, p2, q2)) =
  norm (a1=a2, p1*p2, q1*q2);

fun neg (r as Rat (_, 0, _)) = r
  | neg (Rat (b, p, q)) =
      Rat (not b, p, q);

fun inv (Rat (a, 0, q)) =
      raise DIVZERO
  | inv (Rat (a, p, q)) =
      Rat (a, q, p)

fun ge0 (Rat (a, _, _)) = a;
fun gt0 (Rat (a, p, _)) = a andalso p > 0;

fun roundup (r as Rat (_, _, 1)) = r
  | roundup (Rat (a, p, q)) =
      let
        fun round true q = Rat (true, q+1, 1)
          | round false 0 = Rat (true, 0 ,1)
          | round false q = Rat (false, q, 1)
      in round a (p div q) end;

fun rounddown (r as Rat (_, _, 1)) = r
  | rounddown (Rat (a, p, q)) =
      let
        fun round true q = Rat (true, q, 1)
          | round false q = Rat (false, q+1, 1)
      in round a (p div q) end;

end;
