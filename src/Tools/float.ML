(*  Title:      Tools/float.ML
    Author:     Steven Obua, Florian Haftmann, TU Muenchen

Implementation of real numbers as mantisse-exponent pairs.
*)

signature FLOAT =
sig
  type float = int * int
  val zero: float
  val eq: float * float -> bool
  val ord: float * float -> order
  val sign: float -> order
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

type float = int * int;

val zero: float = (0, 0);

fun add (a1, b1) (a2, b2) =
  if b1 < b2 then
    (a1 + a2 * Integer.square (b2 - b1), b1)
  else
    (a1 * Integer.square (b1 - b2) + a2, b2);

fun sub (a1, b1) (a2, b2) =
  if b1 < b2 then
    (a1 - a2 * Integer.square (b2 - b1), b1)
  else
    (a1 * Integer.square (b1 - b2) - a2, b2);

fun neg (a, b) = (~ a, b);

fun mult (a1, b1) (a2, b2) = (a1 * a2, b1 + b2);

fun sign (a, b) = Integer.sign a;

fun ord (r, s) = sign (sub r s);

fun eq (r, s) = ord (r, s) = EQUAL;

fun min r s = case ord (r, s) of LESS => r | _ => s;
fun max r s = case ord (r, s) of LESS => s | _ => r;

fun positive_part (a, b) = (Int.max (0, a), b);
fun negative_part (a, b) = (Int.min (0, a), b);

end;
