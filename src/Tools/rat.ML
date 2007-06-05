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
  val rat_of_int: integer -> rat
  val rat_of_quotient: integer * integer -> rat
  val quotient_of_rat: rat -> integer * integer
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

structure Rat : RAT =
struct

datatype rat = Rat of bool * integer * integer;

exception DIVZERO;

val zero = Rat (true, Integer.zero, Integer.one);
val one = Rat (true, Integer.one, Integer.one);
val two = Rat (true, Integer.two, Integer.one);

fun rat_of_int i =
  let
    val (a, p) = Integer.signabs i
  in Rat (a, p, Integer.one) end;

fun norm (a, p, q) =
  if Integer.cmp_zero p = EQUAL then Rat (true, Integer.zero, Integer.one)
  else
    let
      val (b, absp) = Integer.signabs p;
      val m = Integer.gcd absp q;
    in Rat (a = b, Integer.div absp m, Integer.div q m) end;

fun common (p1, q1, p2, q2) =
  let
    val q' = Integer.lcm q1 q2;
  in (p1 *% (Integer.div q' q1), p2 *% (Integer.div q' q2), q') end

fun rat_of_quotient (p, q) =
  let
    val (a, absq) = Integer.signabs q;
  in
    if Integer.cmp_zero absq = EQUAL then raise DIVZERO
    else norm (a, p, absq)
  end;

fun quotient_of_rat (Rat (a, p, q)) = (if a then p else Integer.neg p, q);

fun string_of_rat r =
  let
    val (p, q) = quotient_of_rat r;
  in Integer.string_of_int p ^ "/" ^ Integer.string_of_int q end;

fun eq (Rat (false, _, _), Rat (true, _, _)) = false
  | eq (Rat (true, _, _), Rat (false, _, _)) = false
  | eq (Rat (_, p1, q1), Rat (_, p2, q2)) = p1 =% p2 andalso q1 =% q2;

fun cmp (Rat (false, _, _), Rat (true, _, _)) = LESS
  | cmp (Rat (true, _, _), Rat (false, _, _)) = GREATER
  | cmp (Rat (a, p1, q1), Rat (_, p2, q2)) =
      let val (r1, r2, _) = common (p1, q1, p2, q2)
      in if a then Integer.cmp (r1, r2) else Integer.cmp (r2, r1) end;

fun le a b = let val order = cmp (a, b) in order = LESS orelse order = EQUAL end;
fun lt a b = (cmp (a, b) = LESS);

fun cmp_zero (Rat (false, _, _)) = LESS
  | cmp_zero (Rat (_, 0, _)) = EQUAL
  | cmp_zero (Rat (_, _, _)) = GREATER;

fun add (Rat (a1, p1, q1)) (Rat(a2, p2, q2)) =
  let
    val (r1, r2, den) = common (p1, q1, p2, q2);
    val num = (if a1 then r1 else Integer.neg r1)
      +% (if a2 then r2 else Integer.neg r2);
  in norm (true, num, den) end;

fun mult (Rat (a1, p1, q1)) (Rat (a2, p2, q2)) =
  norm (a1 = a2, p1 *% p2, q1 *% q2);

fun neg (r as Rat (b, p, q)) =
  if Integer.cmp_zero p = EQUAL then r
  else Rat (not b, p, q);

fun inv (Rat (a, p, q)) =
  if Integer.cmp_zero q = EQUAL then raise DIVZERO
  else Rat (a, q, p);

fun roundup (r as Rat (a, p, q)) =
  if q = Integer.one then r
  else
    let
      fun round true q = Rat (true, Integer.inc q, Integer.one)
        | round false q =
            Rat (Integer.cmp_zero q = EQUAL, Integer.int 0, Integer.int 1);
    in round a (Integer.div p q) end;

fun rounddown (r as Rat (a, p, q)) =
  if q = Integer.one then r
  else
    let
      fun round true q = Rat (true, q, Integer.one)
        | round false q = Rat (false, Integer.inc q, Integer.one)
    in round a (Integer.div p q) end;

end;

infix 7 */ //;
infix 6 +/ -/; 
infix 4 =/ </ <=/ >/ >=/ <>/;

fun a +/ b = Rat.add a b;
fun a -/ b = a +/ Rat.neg b;
fun a */ b = Rat.mult a b;
fun a // b = a */ Rat.inv b; 
fun a =/ b = Rat.eq (a, b);
fun a </ b = Rat.lt a b;
fun a <=/ b = Rat.le a b;
fun a >/ b = b </ a;
fun a >=/ b = b <=/ a;
fun a <>/ b = not (a =/ b);
