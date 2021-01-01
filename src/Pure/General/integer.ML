(*  Title:      Pure/General/integer.ML
    Author:     Florian Haftmann, TU Muenchen

Auxiliary operations on (unbounded) integers.
*)

signature INTEGER =
sig
  val min: int -> int -> int
  val max: int -> int -> int
  val add: int -> int -> int
  val mult: int -> int -> int
  val sum: int list -> int
  val prod: int list -> int
  val sign: int -> order
  val div_mod: int -> int -> int * int
  val quot_rem: int -> int -> int * int
  val square: int -> int
  val pow: int -> int -> int (* exponent -> base -> result *)
  val log2: int -> int
  val gcd: int -> int -> int
  val lcm: int -> int -> int
  val gcds: int list -> int
  val lcms: int list -> int
  val radicify: int -> int -> int -> int list (* base -> number of positions -> value -> coefficients *)
  val eval_radix: int -> int list -> int (* base -> coefficients -> value *)
end;

structure Integer : INTEGER =
struct

fun min x y = Int.min (x, y);
fun max x y = Int.max (x, y);

fun add x y = x + y;
fun mult x y = x * y;

fun sum xs = fold add xs 0;
fun prod xs = fold mult xs 1;

fun sign x = int_ord (x, 0);

fun div_mod x y = IntInf.divMod (x, y);
fun quot_rem x y = IntInf.quotRem (x, y);

fun square x = x * x;

fun pow k l = IntInf.pow (l, k);

val log2 = IntInf.log2;

fun gcd x y = PolyML.IntInf.gcd (x, y);
fun lcm x y = abs (PolyML.IntInf.lcm (x, y));

fun gcds [] = 0
  | gcds (x :: xs) = fold gcd xs x;

fun lcms [] = 1
  | lcms (x :: xs) = abs (Library.foldl PolyML.IntInf.lcm (x, xs));

fun radicify base len k =
  let
    val _ = if base < 2
      then error ("Bad radix base: " ^ string_of_int base) else ();
    fun shift i = swap (div_mod i base);
  in funpow_yield len shift k |> fst end;

fun eval_radix base ks =
  fold_rev (fn k => fn i => k + i * base) ks 0;

end;
