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
  val two: rat
  val rat_of_int: Intt.int -> rat
  val rat_of_quotient: Intt.int * Intt.int -> rat
  val quotient_of_rat: rat -> Intt.int * Intt.int
  val string_of_rat: rat -> string
  val eq: rat * rat -> bool
  val cmp: rat * rat -> order
  val le: rat -> rat -> bool
  val lt: rat -> rat -> bool
  val cmp_zero: rat -> order
  val add: rat -> rat -> rat
  val mult: rat -> rat -> rat
  val neg: rat -> rat
  val inv: rat -> rat
  val roundup: rat -> rat
  val rounddown: rat -> rat
end;

structure Rat: RAT =
struct

datatype rat = Rat of bool * Intt.int * Intt.int;

exception DIVZERO;

val zero = Rat (true, Intt.int 0, Intt.int 1);
val one = Rat (true, Intt.int 1, Intt.int 1);
val two = Rat (true, Intt.int 2, Intt.int 1);

fun rat_of_int i =
  if i < Intt.int 0
  then Rat (false, ~i, Intt.int 1)
  else Rat (true, i, Intt.int 1);

fun norm (a, p, q) =
  if p = Intt.int 0 then Rat (true, Intt.int 0, Intt.int 1)
  else
    let
      val absp = abs p
      val m = gcd (absp, q)
    in Rat(a = (Intt.int 0 <= p), absp div m, q div m) end;

fun common (p1, q1, p2, q2) =
  let val q' = lcm (q1, q2)
  in (p1 * (q' div q1), p2 * (q' div q2), q') end

fun rat_of_quotient (p, q) =
  if q = Intt.int 0 then raise DIVZERO
  else norm (Intt.int 0 <= q, p, abs q);

fun quotient_of_rat (Rat (a, p, q)) = (if a then p else ~p, q);

fun string_of_rat r =
  let val (p, q) = quotient_of_rat r
  in Intt.string_of_int p ^ "/" ^ Intt.string_of_int q end;

fun eq (Rat (false, _, _), Rat (true, _, _)) = false
  | eq (Rat (true, _, _), Rat (false, _, _)) = false
  | eq (Rat (_, p1, q1), Rat (_, p2, q2)) = p1 = p2 andalso q1 = q2

fun le (Rat (false, _, _)) (Rat (true, _, _)) = true
  | le (Rat (true, _, _)) (Rat (false, _, _)) = false
  | le (Rat (a, p1, q1)) (Rat (_, p2, q2)) =
      let val (r1, r2, _) = common (p1, q1, p2, q2)
      in if a then r1 <= r2 else r2 <= r1 end;

fun cmp (Rat (false, _, _), Rat (true, _, _)) = LESS
  | cmp (Rat (true, _, _), Rat (false, _, _)) = GREATER
  | cmp (Rat (a, p1, q1), Rat (_, p2, q2)) =
      let val (r1, r2, _) = common (p1, q1, p2, q2)
      in if a then Intt.cmp (r1, r2) else Intt.cmp (r2, r1) end;

fun lt a b = cmp (a,b) = LESS;
fun cmp_zero (Rat (false, _, _)) = LESS
  | cmp_zero (Rat (_, 0, _)) = EQUAL
  | cmp_zero (Rat (_, _, _)) = GREATER;

fun add (Rat (a1, p1, q1)) (Rat(a2, p2, q2)) =
  let
    val (r1, r2, den) = common (p1, q1, p2, q2)
    val num = (if a1 then r1 else ~r1) + (if a2 then r2 else ~r2)
  in norm (true, num, den) end;

fun mult (Rat (a1, p1, q1)) (Rat (a2, p2, q2)) =
  norm (a1=a2, p1*p2, q1*q2);

fun neg (r as Rat (b, p, q)) =
  if p = Intt.int 0 then r
  else Rat (not b, p, q);

fun inv (Rat (a, p, q)) =
  if p = Intt.int 0 then raise DIVZERO
  else Rat (a, q, p);

fun roundup (r as Rat (a, p, q)) =
  if q = Intt.int 1 then r
  else
    let
      fun round true q = Rat (true, q + Intt.int 1, Intt.int 1)
        | round false q =
            if q = Intt.int 0
            then Rat (true, Intt.int 0, Intt.int 1)
            else Rat (false, q, Intt.int 1);
    in round a (p div q) end;

fun rounddown (r as Rat (a, p, q)) =
  if q = Intt.int 1 then r
  else
    let
      fun round true q = Rat (true, q, Intt.int 1)
        | round false q = Rat (false, q + Intt.int 1, Intt.int 1)
    in round a (p div q) end;

end;

infix 5 +/;
infix 6 -/;
infix 4 */;
infix 3 //;
infix 9 =/ </ <=/ >/ >=/ <>/;

fun a +/ b = Rat.add a b;
fun a -/ b = a +/ (Rat.neg b);
fun a  */ b = Rat.mult a b;
fun a // b = a */ (Rat.inv b); 
fun a =/ b = Rat.eq (a,b);
fun a </ b = Rat.lt a b;
fun a <=/ b = Rat.le a b;
fun a >/ b = b </ a;
fun a >=/ b = b <=/ a;
fun a <>/ b = not (a =/ b);
