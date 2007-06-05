(*  Title:      Pure/General/float.ML
    ID:         $Id$
    Author:     Steven Obua, Florian Haftmann, TU Muenchen

Implementation of real numbers as mantisse-exponent pairs.
*)

signature FLOAT =
sig
  type float = Intt.int * Intt.int
  val zero: float
  val eq: float * float -> bool
  val cmp: float * float -> order
  val cmp_zero: float -> order
  val min: float -> float -> float
  val max: float -> float -> float
  val add: float -> float -> float
  val sub: float -> float -> float
  val neg: float -> float
  val mult: float -> float -> float
  val positive_part: float -> float
  val negative_part: float -> float
end;

structure Float : FLOAT =
struct

type float = Intt.int * Intt.int;

val zero = (Intt.zero, Intt.zero);

fun add (a1, b1) (a2, b2) =
  if Intt.cmp (b1, b2) = LESS then
    (Intt.add a1 (Intt.mult a2 (Intt.exp (Intt.sub b2 b1))), b1)
  else
    (Intt.add (Intt.mult a1 (Intt.exp (Intt.sub b1 b2))) a2, b2);

fun sub (a1, b1) (a2, b2) =
  if Intt.cmp (b1, b2) = LESS then
    (Intt.sub a1 (Intt.mult a2 (Intt.exp (Intt.sub b2 b1))), b1)
  else
    (Intt.sub (Intt.mult a1 (Intt.exp (Intt.sub b1 b2))) a2, b2);

fun neg (a, b) = (Intt.neg a, b);

fun mult (a1, b1) (a2, b2) = (Intt.mult a1 a2, Intt.add b1 b2);

fun cmp_zero (a, b) = Intt.cmp_zero a;

fun cmp (r, s) = cmp_zero (sub r s);

fun eq (r, s) = cmp (r, s) = EQUAL;

fun min r s = case cmp (r, s) of LESS => r | _ => s;
fun max r s = case cmp (r, s) of LESS => s | _ => r;

fun positive_part (a, b) = (Intt.max Intt.zero a, b);
fun negative_part (a, b) = (Intt.min Intt.zero a, b);

end;
