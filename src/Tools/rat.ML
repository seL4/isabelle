(*  Title:      Pure/General/rat.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen

Canonical implementation of exact rational numbers.
*)

signature RAT =
sig
  eqtype rat
  exception DIVZERO
  val zero: rat
  val one: rat
  val two: rat
  val rat_of_int: integer -> rat
  val rat_of_quotient: integer * integer -> rat
  val quotient_of_rat: rat -> integer * integer
  val string_of_rat: rat -> string
  val eq: rat * rat -> bool
  val ord: rat * rat -> order
  val le: rat -> rat -> bool
  val lt: rat -> rat -> bool
  val signabs: rat -> order * rat
  val sign: rat -> order
  val abs: rat -> rat
  val add: rat -> rat -> rat
  val mult: rat -> rat -> rat
  val neg: rat -> rat
  val inv: rat -> rat
  val rounddown: rat -> rat
  val roundup: rat -> rat
end;

structure Rat : RAT =
struct

fun common (p1, q1) (p2, q2) =
  let
    val m = Integer.lcm q1 q2;
  in ((Integer.mult p1 (Integer.div m q1), Integer.mult p2 (Integer.div m q2)), m) end;

datatype rat = Rat of integer * integer; (* nominator, denominator (positive!) *)

exception DIVZERO;

fun rat_of_quotient (p, q) =
  let
    val m = Integer.gcd (Integer.abs p) q
  in Rat (Integer.div p m, Integer.div q m) end handle Div => raise DIVZERO;

fun quotient_of_rat (Rat r) = r;

fun rat_of_int i = Rat (i, 1);

val zero = rat_of_int 0;
val one = rat_of_int 1;
val two = rat_of_int 2;

fun string_of_rat (Rat (p, q)) =
  Integer.string_of_int p ^ "/" ^ Integer.string_of_int q;

fun eq (Rat (p1, q1), Rat (p2, q2)) = (p1 = p2 andalso q1 = q2);

fun ord (Rat (p1, q1), Rat (p2, q2)) = case (Integer.sign p1, Integer.sign p2)
 of (LESS, EQUAL) => LESS
  | (LESS, GREATER) => LESS
  | (EQUAL, LESS) => GREATER
  | (EQUAL, EQUAL) => EQUAL
  | (EQUAL, GREATER) => LESS
  | (GREATER, LESS) => GREATER
  | (GREATER, EQUAL) => GREATER
  | _ => Integer.ord (fst (common (p1, q1) (p2, q2)));

fun le a b = not (ord (a, b) = GREATER);
fun lt a b = (ord (a, b) = LESS);

fun sign (Rat (p, _)) = Integer.sign p;

fun abs (Rat (p, q)) = Rat (Integer.abs p, q);

fun signabs (Rat (p, q)) =
  let
    val (s, p') = Integer.signabs p;
  in (s, Rat (p', q)) end;

fun add (Rat (p1, q1)) (Rat (p2, q2)) =
  let
    val ((m1, m2), n) = common (p1, q1) (p2, q2);
  in rat_of_quotient (Integer.add m1 m2, n) end;

fun mult (Rat (p1, q1)) (Rat (p2, q2)) =
  rat_of_quotient (Integer.mult p1 p2, Integer.mult q1 q2);

fun neg (Rat (p, q)) = Rat (Integer.neg p, q);

fun inv (Rat (p, q)) = case Integer.sign p
 of LESS => Rat (Integer.neg q, Integer.neg p)
  | EQUAL => raise DIVZERO
  | GREATER => Rat (q, p);

fun rounddown (Rat (p, q)) = Rat (Integer.div p q, 1);

fun roundup (Rat (p, q)) = case Integer.divmod p q
 of (m, 0) => Rat (m, 1)
  | (m, _) => Rat (m + 1, 1);

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
