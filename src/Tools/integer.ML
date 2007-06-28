(*  Title:      Pure/General/int.ML
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
  val cmp: int * int -> order
  val le: int -> int -> bool
  val lt: int -> int -> bool
  val cmp_zero: int -> order
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
  val signabs: int -> bool * int
  val exp: int -> int
  val log: int -> int
  val pow: int -> int -> int (* exponent -> base -> result *)
  val gcd: int -> int -> int
  val lcm: int -> int -> int
end;

structure Integer : INTEGER =
struct

open IntInf;

type integer = int;

val int = fromInt;

val zero = int 0;
val one = int 1;
val two = int 2;

val machine_int = toInt;
val string_of_int = toString;
val int_of_string = fromString;

val eq = op = : int * int -> bool;
val cmp = compare;
val le = curry (op <=);
val lt = curry (op <);
fun cmp_zero k = cmp (k, zero);

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

fun signabs k = if cmp_zero k = LESS then (false, neg k) else (true, k);

fun pow k l =
  let
    fun pw 0 = 1
      | pw k = mult l (pw (sub k 1));
  in if k < zero
    then error "pow: negative exponent"
    else pw k
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
