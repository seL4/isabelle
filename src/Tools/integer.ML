(*  Title:      Tools/integer.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Unbounded integers.
*)

signature INTEGER =
sig
  eqtype int
  val zero: int
  val one: int
  val two: int
  val int: Int.int -> int
  val machine_int: int -> Int.int
  val string_of_int: int -> string
  val int_of_string: string -> int option
  val eq: int * int -> bool
  val ord: int * int -> order
  val le: int -> int -> bool
  val lt: int -> int -> bool
  val signabs: int -> order * int
  val sign: int -> order
  val abs: int -> int
  val min: int -> int -> int
  val max: int -> int -> int
  val inc: int -> int
  val add: int -> int -> int
  val sub: int -> int -> int
  val mult: int -> int -> int
  val divmod: int -> int -> int * int
  val div: int -> int -> int
  val mod: int -> int -> int
  val neg: int -> int
  val exp: int -> int
  val log: int -> int
  val pow: int -> int -> int (* exponent -> base -> result *)
  val gcd: int -> int -> int
  val lcm: int -> int -> int
end;

structure Integer : INTEGER =
struct

open IntInf;

val int = fromInt;

val zero = int 0;
val one = int 1;
val two = int 2;

val machine_int = toInt;
val string_of_int = toString;
val int_of_string = fromString;

val eq = op = : int * int -> bool;
val ord = compare;
val le = curry (op <=);
val lt = curry (op <);

fun sign k = ord (k, zero);
fun signabs k = (ord (k, zero), abs k);

val min = curry min;
val max = curry max;

val inc = curry (op +) one;

val add = curry (op +);
val sub = curry (op -);
val mult = curry ( op * );
val divmod = curry divMod;
nonfix div val div = curry div;
nonfix mod val mod = curry mod;
val neg = ~;

fun pow k l =
  let
    fun pw 0 _ = 1
      | pw 1 l = l
      | pw k l =
          let
            val (k', r) = divmod k 2;
            val l' = pw k' (mult l l);
          in if r = 0 then l' else mult l' l end;
  in if k < zero
    then error "pow: negative exponent"
    else pw k l
  end;

fun exp k = pow k two;
val log = int o log2;

fun gcd x y =
  let
    fun gxd x y = if y = zero then x else gxd y (mod x y)
  in if lt x y then gxd y x else gxd x y end;

fun lcm x y = div (mult x y) (gcd x y);

end;

type integer = Integer.int;

infix 7 *%;
infix 6 +% -%;
infix 4 =% <% <=% >% >=% <>%;

fun a +% b = Integer.add a b;
fun a -% b = Integer.sub a b;
fun a *% b = Integer.mult a b;
fun a =% b = Integer.eq (a, b);
fun a <% b = Integer.lt a b;
fun a <=% b = Integer.le a b;
fun a >% b = b <% a;
fun a >=% b = b <=% a;
fun a <>% b = not (a =% b);
