(*  Title:      Tools/rat.ML
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
  val rat_of_int: int -> rat
  val rat_of_quotient: int * int -> rat
  val quotient_of_rat: rat -> int * int
  val string_of_rat: rat -> string
  val eq: rat * rat -> bool
  val ord: rat * rat -> order
  val le: rat -> rat -> bool
  val lt: rat -> rat -> bool
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
  in ((p1 * (m div q1), p2 * (m div q2)), m) end;

datatype rat = Rat of int * int;  (*nominator, denominator (positive!)*)

exception DIVZERO;

fun rat_of_quotient (p, q) =
  let
    val m = Integer.gcd (Int.abs p) q
  in Rat (p div m, q div m) end handle Div => raise DIVZERO;

fun quotient_of_rat (Rat r) = r;

fun rat_of_int i = Rat (i, 1);

val zero = rat_of_int 0;
val one = rat_of_int 1;
val two = rat_of_int 2;

fun string_of_rat (Rat (p, q)) =
  string_of_int p ^ "/" ^ string_of_int q;

fun eq (Rat (p1, q1), Rat (p2, q2)) = (p1 = p2 andalso q1 = q2);

fun ord (Rat (p1, q1), Rat (p2, q2)) =
 case (Integer.sign p1, Integer.sign p2)
 of (LESS, EQUAL) => LESS
  | (LESS, GREATER) => LESS
  | (EQUAL, LESS) => GREATER
  | (EQUAL, EQUAL) => EQUAL
  | (EQUAL, GREATER) => LESS
  | (GREATER, LESS) => GREATER
  | (GREATER, EQUAL) => GREATER
  | _ => int_ord (fst (common (p1, q1) (p2, q2)));

fun le a b = not (ord (a, b) = GREATER);
fun lt a b = (ord (a, b) = LESS);

fun sign (Rat (p, _)) = Integer.sign p;

fun abs (Rat (p, q)) = Rat (Int.abs p, q);

fun add (Rat (p1, q1)) (Rat (p2, q2)) =
  let
    val ((m1, m2), n) = common (p1, q1) (p2, q2);
  in rat_of_quotient (m1 + m2, n) end;

fun mult (Rat (p1, q1)) (Rat (p2, q2)) =
  rat_of_quotient (p1 * p2, q1 * q2);

fun neg (Rat (p, q)) = Rat (~ p, q);

fun inv (Rat (p, q)) =
 case Integer.sign p
 of LESS => Rat (~ q, ~ p)
  | EQUAL => raise DIVZERO
  | GREATER => Rat (q, p);

fun rounddown (Rat (p, q)) = Rat (p div q, 1);

fun roundup (Rat (p, q)) =
 case Integer.div_mod p q
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
