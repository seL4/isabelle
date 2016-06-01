(*  Title:      Pure/General/rat.ML
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
  val of_int: int -> rat
  val make: int * int -> rat
  val dest: rat -> int * int
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

datatype rat = Rat of int * int;  (*nominator, denominator (positive!)*)

fun common (p1, q1) (p2, q2) =
  let val m = PolyML.IntInf.lcm (q1, q2)
  in ((p1 * (m div q1), p2 * (m div q2)), m) end;

exception DIVZERO;

fun make (p, q) =
  let
    val m = PolyML.IntInf.gcd (p, q);
    val (p', q') = (p div m, q div m) handle Div => raise DIVZERO;
  in Rat (if q' < 0 then (~ p', ~ q') else (p', q')) end

fun dest (Rat r) = r;

fun of_int i = Rat (i, 1);

val zero = of_int 0;
val one = of_int 1;
val two = of_int 2;

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
  in make (m1 + m2, n) end;

fun mult (Rat (p1, q1)) (Rat (p2, q2)) =
  make (p1 * p2, q1 * q2);

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

ML_system_overload (uncurry Rat.add) "+";
ML_system_overload (fn (a, b) => Rat.add a (Rat.neg b)) "-";
ML_system_overload (uncurry Rat.mult) "*";
ML_system_overload (fn (a, b) => Rat.mult a (Rat.inv b)) "/";
ML_system_overload Rat.eq "=";
ML_system_overload (uncurry Rat.lt) "<";
ML_system_overload (uncurry Rat.le) "<=";
ML_system_overload (fn (a, b) => Rat.lt b a) ">";
ML_system_overload (fn (a, b) => Rat.le b a) ">=";
ML_system_overload (not o Rat.eq) "<>";
