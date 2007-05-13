(*  Title:      Pure/General/int.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Unbounded integers.
*)

signature INTT =
sig
  type int
  val zero: int
  val one: int
  val two: int
  val int: Int.int -> int
  val machine_int: int -> Int.int
  val string_of_int: int -> string
  val int_of_string: string -> int option
  val eq: int * int -> bool
  val cmp: int * int -> order
  val le: int -> int -> bool
  val cmp_zero: int -> order
  val add: int -> int -> int
  val sub: int -> int -> int
  val mult: int -> int -> int
  val divmod: int -> int -> int * int
  val div: int -> int -> int
  val mod: int -> int -> int
  val neg: int -> int
  val exp: int -> int
end;

structure Intt: INTT =
struct

open IntInf;

val int = IntInf.fromInt;

val zero = int 0;
val one = int 1;
val two = int 2;

val machine_int = IntInf.toInt;
val string_of_int = IntInf.toString;
val int_of_string = IntInf.fromString;

val eq = op =;
val cmp = compare;
val le = curry (op <=);
val cmp_zero = curry cmp zero;
val add = curry (op +);
val sub = curry (op -);
val mult = curry ( op * );
val divmod = curry divMod;
nonfix div
val div = curry div;
nonfix mod
val mod = curry mod;
val neg = IntInf.~;
fun exp n = pow (2, IntInf.toInt n);

end;
