(*  Title:      Pure/General/float.ML
    ID:         $Id$
    Author:     Steven Obua, Florian Haftmann, TU Muenchen

Implementation of real numbers as mantisse-exponent pairs.
*)

signature FLOAT =
sig
  type float = integer * integer
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

type float = integer * integer;

val zero: float = (0, 0);

fun add (a1, b1) (a2, b2) =
  if Integer.cmp (b1, b2) = LESS then
    (a1 +% a2 *% Integer.exp (b2 -% b1), b1)
  else
    (a1 *% Integer.exp (b1 -% b2) +% a2, b2);

fun sub (a1, b1) (a2, b2) =
  if Integer.cmp (b1, b2) = LESS then
    (a1 -% a2 *% Integer.exp (b2 -% b1), b1)
  else
    (a1 *% Integer.exp (b1 -% b2) -% a2, b2);

fun neg (a, b) = (Integer.neg a, b);

fun mult (a1, b1) (a2, b2) = (a1 *% a2, b1 +% b2);

fun cmp_zero (a, b) = Integer.cmp_zero a;

fun cmp (r, s) = cmp_zero (sub r s);

fun eq (r, s) = cmp (r, s) = EQUAL;

fun min r s = case cmp (r, s) of LESS => r | _ => s;
fun max r s = case cmp (r, s) of LESS => s | _ => r;

fun positive_part (a, b) = (Integer.max 0 a, b);
fun negative_part (a, b) = (Integer.min 0 a, b);

end;
