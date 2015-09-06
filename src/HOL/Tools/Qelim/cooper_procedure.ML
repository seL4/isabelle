(* Generated from Cooper.thy; DO NOT EDIT! *)

structure Cooper_Procedure : sig
  datatype inta = Int_of_integer of int
  val integer_of_int : inta -> int
  type nat
  val integer_of_nat : nat -> int
  datatype numa = C of inta | Bound of nat | CN of nat * inta * numa |
    Neg of numa | Add of numa * numa | Sub of numa * numa | Mul of inta * numa
  datatype fm = T | F | Lt of numa | Le of numa | Gt of numa | Ge of numa |
    Eq of numa | NEq of numa | Dvd of inta * numa | NDvd of inta * numa |
    NOT of fm | And of fm * fm | Or of fm * fm | Imp of fm * fm | Iff of fm * fm
    | E of fm | A of fm | Closed of nat | NClosed of nat
  val pa : fm -> fm
  val nat_of_integer : int -> nat
end = struct

datatype inta = Int_of_integer of int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = integer_of_int k = integer_of_int l;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : inta equal;

fun times_inta k l = Int_of_integer (integer_of_int k * integer_of_int l);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_int = {times = times_inta} : inta times;

val dvd_int = {times_dvd = times_int} : inta dvd;

datatype num = One | Bit0 of num | Bit1 of num;

val one_inta : inta = Int_of_integer (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : inta one;

fun sgn_integer k =
  (if k = (0 : IntInf.int) then (0 : IntInf.int)
    else (if k < (0 : IntInf.int) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun abs_integer k = (if k < (0 : IntInf.int) then ~ k else k);

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if k = (0 : IntInf.int) then ((0 : IntInf.int), (0 : IntInf.int))
    else (if l = (0 : IntInf.int) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => a * b) o sgn_integer) l
                  (if sgn_integer k = sgn_integer l
                    then Integer.div_mod (abs k) (abs l)
                    else let
                           val (r, s) = Integer.div_mod (abs k) (abs l);
                         in
                           (if s = (0 : IntInf.int) then (~ r, (0 : IntInf.int))
                             else (~ r - (1 : IntInf.int), abs_integer l - s))
                         end)));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_inta k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

fun snd (x1, x2) = x2;

fun mod_integer k l = snd (divmod_integer k l);

fun mod_int k l =
  Int_of_integer (mod_integer (integer_of_int k) (integer_of_int l));

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

type 'a diva =
  {divide_div : 'a divide, dvd_div : 'a dvd, moda : 'a -> 'a -> 'a};
val divide_div = #divide_div : 'a diva -> 'a divide;
val dvd_div = #dvd_div : 'a diva -> 'a dvd;
val moda = #moda : 'a diva -> 'a -> 'a -> 'a;

val divide_int = {divide = divide_inta} : inta divide;

val div_int = {divide_div = divide_int, dvd_div = dvd_int, moda = mod_int} :
  inta diva;

fun plus_inta k l = Int_of_integer (integer_of_int k + integer_of_int l);

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : inta plus;

val zero_inta : inta = Int_of_integer (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = zero_inta} : inta zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_int = {plus_semigroup_add = plus_int} : inta semigroup_add;

val numeral_int =
  {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} :
  inta numeral;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val power_int = {one_power = one_int, times_power = times_int} : inta power;

fun minus_inta k l = Int_of_integer (integer_of_int k - integer_of_int l);

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_int = {minus = minus_inta} : inta minus;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors =
  #semiring_1_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors =
  #semiring_no_zero_divisors_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a semidom =
  {semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors,
    comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel};
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : inta ab_semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  inta monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : inta comm_monoid_add;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_int} :
  inta mult_zero;

val semigroup_mult_int = {times_semigroup_mult = times_int} :
  inta semigroup_mult;

val semiring_int =
  {ab_semigroup_add_semiring = ab_semigroup_add_int,
    semigroup_mult_semiring = semigroup_mult_int}
  : inta semiring;

val semiring_0_int =
  {comm_monoid_add_semiring_0 = comm_monoid_add_int,
    mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int}
  : inta semiring_0;

val semiring_no_zero_divisors_int =
  {semiring_0_semiring_no_zero_divisors = semiring_0_int} :
  inta semiring_no_zero_divisors;

val monoid_mult_int =
  {semigroup_mult_monoid_mult = semigroup_mult_int,
    power_monoid_mult = power_int}
  : inta monoid_mult;

val semiring_numeral_int =
  {monoid_mult_semiring_numeral = monoid_mult_int,
    numeral_semiring_numeral = numeral_int,
    semiring_semiring_numeral = semiring_int}
  : inta semiring_numeral;

val zero_neq_one_int =
  {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} :
  inta zero_neq_one;

val semiring_1_int =
  {semiring_numeral_semiring_1 = semiring_numeral_int,
    semiring_0_semiring_1 = semiring_0_int,
    zero_neq_one_semiring_1 = zero_neq_one_int}
  : inta semiring_1;

val semiring_1_no_zero_divisors_int =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_int,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_int}
  : inta semiring_1_no_zero_divisors;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  inta cancel_semigroup_add;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : inta cancel_ab_semigroup_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : inta cancel_comm_monoid_add;

val semiring_0_cancel_int =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int,
    semiring_0_semiring_0_cancel = semiring_0_int}
  : inta semiring_0_cancel;

val ab_semigroup_mult_int =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
  inta ab_semigroup_mult;

val comm_semiring_int =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int,
    semiring_comm_semiring = semiring_int}
  : inta comm_semiring;

val comm_semiring_0_int =
  {comm_semiring_comm_semiring_0 = comm_semiring_int,
    semiring_0_comm_semiring_0 = semiring_0_int}
  : inta comm_semiring_0;

val comm_semiring_0_cancel_int =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
  : inta comm_semiring_0_cancel;

val semiring_1_cancel_int =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int,
    semiring_1_semiring_1_cancel = semiring_1_int}
  : inta semiring_1_cancel;

val comm_monoid_mult_int =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int,
    monoid_mult_comm_monoid_mult = monoid_mult_int,
    dvd_comm_monoid_mult = dvd_int}
  : inta comm_monoid_mult;

val comm_semiring_1_int =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_int,
    semiring_1_comm_semiring_1 = semiring_1_int}
  : inta comm_semiring_1;

val comm_semiring_1_cancel_int =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
  : inta comm_semiring_1_cancel;

val semidom_int =
  {semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int,
    comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int}
  : inta semidom;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a semidom_divide =
  {divide_semidom_divide : 'a divide, semidom_semidom_divide : 'a semidom,
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};
val divide_semidom_divide = #divide_semidom_divide :
  'a semidom_divide -> 'a divide;
val semidom_semidom_divide = #semidom_semidom_divide :
  'a semidom_divide -> 'a semidom;
val semiring_no_zero_divisors_cancel_semidom_divide =
  #semiring_no_zero_divisors_cancel_semidom_divide :
  'a semidom_divide -> 'a semiring_no_zero_divisors_cancel;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};
val semidom_divide_algebraic_semidom = #semidom_divide_algebraic_semidom :
  'a algebraic_semidom -> 'a semidom_divide;

type 'a semiring_div =
  {div_semiring_div : 'a diva,
    algebraic_semidom_semiring_div : 'a algebraic_semidom};
val div_semiring_div = #div_semiring_div : 'a semiring_div -> 'a diva;
val algebraic_semidom_semiring_div = #algebraic_semidom_semiring_div :
  'a semiring_div -> 'a algebraic_semidom;

val semiring_no_zero_divisors_cancel_int =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_int}
  : inta semiring_no_zero_divisors_cancel;

val semidom_divide_int =
  {divide_semidom_divide = divide_int, semidom_semidom_divide = semidom_int,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_int}
  : inta semidom_divide;

val algebraic_semidom_int =
  {semidom_divide_algebraic_semidom = semidom_divide_int} :
  inta algebraic_semidom;

val semiring_div_int =
  {div_semiring_div = div_int,
    algebraic_semidom_semiring_div = algebraic_semidom_int}
  : inta semiring_div;

datatype nat = Nat of int;

fun integer_of_nat (Nat x) = x;

fun equal_nat m n = integer_of_nat m = integer_of_nat n;

datatype numa = C of inta | Bound of nat | CN of nat * inta * numa | Neg of numa
  | Add of numa * numa | Sub of numa * numa | Mul of inta * numa;

fun equal_numa (Sub (x61, x62)) (Mul (x71, x72)) = false
  | equal_numa (Mul (x71, x72)) (Sub (x61, x62)) = false
  | equal_numa (Add (x51, x52)) (Mul (x71, x72)) = false
  | equal_numa (Mul (x71, x72)) (Add (x51, x52)) = false
  | equal_numa (Add (x51, x52)) (Sub (x61, x62)) = false
  | equal_numa (Sub (x61, x62)) (Add (x51, x52)) = false
  | equal_numa (Neg x4) (Mul (x71, x72)) = false
  | equal_numa (Mul (x71, x72)) (Neg x4) = false
  | equal_numa (Neg x4) (Sub (x61, x62)) = false
  | equal_numa (Sub (x61, x62)) (Neg x4) = false
  | equal_numa (Neg x4) (Add (x51, x52)) = false
  | equal_numa (Add (x51, x52)) (Neg x4) = false
  | equal_numa (CN (x31, x32, x33)) (Mul (x71, x72)) = false
  | equal_numa (Mul (x71, x72)) (CN (x31, x32, x33)) = false
  | equal_numa (CN (x31, x32, x33)) (Sub (x61, x62)) = false
  | equal_numa (Sub (x61, x62)) (CN (x31, x32, x33)) = false
  | equal_numa (CN (x31, x32, x33)) (Add (x51, x52)) = false
  | equal_numa (Add (x51, x52)) (CN (x31, x32, x33)) = false
  | equal_numa (CN (x31, x32, x33)) (Neg x4) = false
  | equal_numa (Neg x4) (CN (x31, x32, x33)) = false
  | equal_numa (Bound x2) (Mul (x71, x72)) = false
  | equal_numa (Mul (x71, x72)) (Bound x2) = false
  | equal_numa (Bound x2) (Sub (x61, x62)) = false
  | equal_numa (Sub (x61, x62)) (Bound x2) = false
  | equal_numa (Bound x2) (Add (x51, x52)) = false
  | equal_numa (Add (x51, x52)) (Bound x2) = false
  | equal_numa (Bound x2) (Neg x4) = false
  | equal_numa (Neg x4) (Bound x2) = false
  | equal_numa (Bound x2) (CN (x31, x32, x33)) = false
  | equal_numa (CN (x31, x32, x33)) (Bound x2) = false
  | equal_numa (C x1) (Mul (x71, x72)) = false
  | equal_numa (Mul (x71, x72)) (C x1) = false
  | equal_numa (C x1) (Sub (x61, x62)) = false
  | equal_numa (Sub (x61, x62)) (C x1) = false
  | equal_numa (C x1) (Add (x51, x52)) = false
  | equal_numa (Add (x51, x52)) (C x1) = false
  | equal_numa (C x1) (Neg x4) = false
  | equal_numa (Neg x4) (C x1) = false
  | equal_numa (C x1) (CN (x31, x32, x33)) = false
  | equal_numa (CN (x31, x32, x33)) (C x1) = false
  | equal_numa (C x1) (Bound x2) = false
  | equal_numa (Bound x2) (C x1) = false
  | equal_numa (Mul (x71, x72)) (Mul (y71, y72)) =
    equal_inta x71 y71 andalso equal_numa x72 y72
  | equal_numa (Sub (x61, x62)) (Sub (y61, y62)) =
    equal_numa x61 y61 andalso equal_numa x62 y62
  | equal_numa (Add (x51, x52)) (Add (y51, y52)) =
    equal_numa x51 y51 andalso equal_numa x52 y52
  | equal_numa (Neg x4) (Neg y4) = equal_numa x4 y4
  | equal_numa (CN (x31, x32, x33)) (CN (y31, y32, y33)) =
    equal_nat x31 y31 andalso (equal_inta x32 y32 andalso equal_numa x33 y33)
  | equal_numa (Bound x2) (Bound y2) = equal_nat x2 y2
  | equal_numa (C x1) (C y1) = equal_inta x1 y1;

val equal_num = {equal = equal_numa} : numa equal;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => a <= b), less = (fn a => fn b => a < b)} :
  int ord;

datatype fm = T | F | Lt of numa | Le of numa | Gt of numa | Ge of numa |
  Eq of numa | NEq of numa | Dvd of inta * numa | NDvd of inta * numa |
  NOT of fm | And of fm * fm | Or of fm * fm | Imp of fm * fm | Iff of fm * fm |
  E of fm | A of fm | Closed of nat | NClosed of nat;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun disjuncts (Or (p, q)) = disjuncts p @ disjuncts q
  | disjuncts F = []
  | disjuncts T = [T]
  | disjuncts (Lt v) = [Lt v]
  | disjuncts (Le v) = [Le v]
  | disjuncts (Gt v) = [Gt v]
  | disjuncts (Ge v) = [Ge v]
  | disjuncts (Eq v) = [Eq v]
  | disjuncts (NEq v) = [NEq v]
  | disjuncts (Dvd (v, va)) = [Dvd (v, va)]
  | disjuncts (NDvd (v, va)) = [NDvd (v, va)]
  | disjuncts (NOT v) = [NOT v]
  | disjuncts (And (v, va)) = [And (v, va)]
  | disjuncts (Imp (v, va)) = [Imp (v, va)]
  | disjuncts (Iff (v, va)) = [Iff (v, va)]
  | disjuncts (E v) = [E v]
  | disjuncts (A v) = [A v]
  | disjuncts (Closed v) = [Closed v]
  | disjuncts (NClosed v) = [NClosed v];

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun equal_fm (Closed x18) (NClosed x19) = false
  | equal_fm (NClosed x19) (Closed x18) = false
  | equal_fm (A x17) (NClosed x19) = false
  | equal_fm (NClosed x19) (A x17) = false
  | equal_fm (A x17) (Closed x18) = false
  | equal_fm (Closed x18) (A x17) = false
  | equal_fm (E x16) (NClosed x19) = false
  | equal_fm (NClosed x19) (E x16) = false
  | equal_fm (E x16) (Closed x18) = false
  | equal_fm (Closed x18) (E x16) = false
  | equal_fm (E x16) (A x17) = false
  | equal_fm (A x17) (E x16) = false
  | equal_fm (Iff (x151, x152)) (NClosed x19) = false
  | equal_fm (NClosed x19) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Closed x18) = false
  | equal_fm (Closed x18) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (A x17) = false
  | equal_fm (A x17) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (E x16) = false
  | equal_fm (E x16) (Iff (x151, x152)) = false
  | equal_fm (Imp (x141, x142)) (NClosed x19) = false
  | equal_fm (NClosed x19) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Closed x18) = false
  | equal_fm (Closed x18) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (A x17) = false
  | equal_fm (A x17) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (E x16) = false
  | equal_fm (E x16) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Imp (x141, x142)) = false
  | equal_fm (Or (x131, x132)) (NClosed x19) = false
  | equal_fm (NClosed x19) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Closed x18) = false
  | equal_fm (Closed x18) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (A x17) = false
  | equal_fm (A x17) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (E x16) = false
  | equal_fm (E x16) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Or (x131, x132)) = false
  | equal_fm (And (x121, x122)) (NClosed x19) = false
  | equal_fm (NClosed x19) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Closed x18) = false
  | equal_fm (Closed x18) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (A x17) = false
  | equal_fm (A x17) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (E x16) = false
  | equal_fm (E x16) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (And (x121, x122)) = false
  | equal_fm (NOT x11) (NClosed x19) = false
  | equal_fm (NClosed x19) (NOT x11) = false
  | equal_fm (NOT x11) (Closed x18) = false
  | equal_fm (Closed x18) (NOT x11) = false
  | equal_fm (NOT x11) (A x17) = false
  | equal_fm (A x17) (NOT x11) = false
  | equal_fm (NOT x11) (E x16) = false
  | equal_fm (E x16) (NOT x11) = false
  | equal_fm (NOT x11) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (NOT x11) = false
  | equal_fm (NOT x11) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (NOT x11) = false
  | equal_fm (NOT x11) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (NOT x11) = false
  | equal_fm (NOT x11) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (NOT x11) = false
  | equal_fm (NDvd (x101, x102)) (NClosed x19) = false
  | equal_fm (NClosed x19) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Closed x18) = false
  | equal_fm (Closed x18) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (A x17) = false
  | equal_fm (A x17) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (E x16) = false
  | equal_fm (E x16) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (NOT x11) = false
  | equal_fm (NOT x11) (NDvd (x101, x102)) = false
  | equal_fm (Dvd (x91, x92)) (NClosed x19) = false
  | equal_fm (NClosed x19) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Closed x18) = false
  | equal_fm (Closed x18) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (A x17) = false
  | equal_fm (A x17) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (E x16) = false
  | equal_fm (E x16) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (NOT x11) = false
  | equal_fm (NOT x11) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Dvd (x91, x92)) = false
  | equal_fm (NEq x8) (NClosed x19) = false
  | equal_fm (NClosed x19) (NEq x8) = false
  | equal_fm (NEq x8) (Closed x18) = false
  | equal_fm (Closed x18) (NEq x8) = false
  | equal_fm (NEq x8) (A x17) = false
  | equal_fm (A x17) (NEq x8) = false
  | equal_fm (NEq x8) (E x16) = false
  | equal_fm (E x16) (NEq x8) = false
  | equal_fm (NEq x8) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (NEq x8) = false
  | equal_fm (NEq x8) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (NEq x8) = false
  | equal_fm (NEq x8) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (NEq x8) = false
  | equal_fm (NEq x8) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (NEq x8) = false
  | equal_fm (NEq x8) (NOT x11) = false
  | equal_fm (NOT x11) (NEq x8) = false
  | equal_fm (NEq x8) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (NEq x8) = false
  | equal_fm (NEq x8) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (NEq x8) = false
  | equal_fm (Eq x7) (NClosed x19) = false
  | equal_fm (NClosed x19) (Eq x7) = false
  | equal_fm (Eq x7) (Closed x18) = false
  | equal_fm (Closed x18) (Eq x7) = false
  | equal_fm (Eq x7) (A x17) = false
  | equal_fm (A x17) (Eq x7) = false
  | equal_fm (Eq x7) (E x16) = false
  | equal_fm (E x16) (Eq x7) = false
  | equal_fm (Eq x7) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Eq x7) = false
  | equal_fm (Eq x7) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Eq x7) = false
  | equal_fm (Eq x7) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Eq x7) = false
  | equal_fm (Eq x7) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Eq x7) = false
  | equal_fm (Eq x7) (NOT x11) = false
  | equal_fm (NOT x11) (Eq x7) = false
  | equal_fm (Eq x7) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Eq x7) = false
  | equal_fm (Eq x7) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Eq x7) = false
  | equal_fm (Eq x7) (NEq x8) = false
  | equal_fm (NEq x8) (Eq x7) = false
  | equal_fm (Ge x6) (NClosed x19) = false
  | equal_fm (NClosed x19) (Ge x6) = false
  | equal_fm (Ge x6) (Closed x18) = false
  | equal_fm (Closed x18) (Ge x6) = false
  | equal_fm (Ge x6) (A x17) = false
  | equal_fm (A x17) (Ge x6) = false
  | equal_fm (Ge x6) (E x16) = false
  | equal_fm (E x16) (Ge x6) = false
  | equal_fm (Ge x6) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Ge x6) = false
  | equal_fm (Ge x6) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Ge x6) = false
  | equal_fm (Ge x6) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Ge x6) = false
  | equal_fm (Ge x6) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Ge x6) = false
  | equal_fm (Ge x6) (NOT x11) = false
  | equal_fm (NOT x11) (Ge x6) = false
  | equal_fm (Ge x6) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Ge x6) = false
  | equal_fm (Ge x6) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Ge x6) = false
  | equal_fm (Ge x6) (NEq x8) = false
  | equal_fm (NEq x8) (Ge x6) = false
  | equal_fm (Ge x6) (Eq x7) = false
  | equal_fm (Eq x7) (Ge x6) = false
  | equal_fm (Gt x5) (NClosed x19) = false
  | equal_fm (NClosed x19) (Gt x5) = false
  | equal_fm (Gt x5) (Closed x18) = false
  | equal_fm (Closed x18) (Gt x5) = false
  | equal_fm (Gt x5) (A x17) = false
  | equal_fm (A x17) (Gt x5) = false
  | equal_fm (Gt x5) (E x16) = false
  | equal_fm (E x16) (Gt x5) = false
  | equal_fm (Gt x5) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Gt x5) = false
  | equal_fm (Gt x5) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Gt x5) = false
  | equal_fm (Gt x5) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Gt x5) = false
  | equal_fm (Gt x5) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Gt x5) = false
  | equal_fm (Gt x5) (NOT x11) = false
  | equal_fm (NOT x11) (Gt x5) = false
  | equal_fm (Gt x5) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Gt x5) = false
  | equal_fm (Gt x5) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Gt x5) = false
  | equal_fm (Gt x5) (NEq x8) = false
  | equal_fm (NEq x8) (Gt x5) = false
  | equal_fm (Gt x5) (Eq x7) = false
  | equal_fm (Eq x7) (Gt x5) = false
  | equal_fm (Gt x5) (Ge x6) = false
  | equal_fm (Ge x6) (Gt x5) = false
  | equal_fm (Le x4) (NClosed x19) = false
  | equal_fm (NClosed x19) (Le x4) = false
  | equal_fm (Le x4) (Closed x18) = false
  | equal_fm (Closed x18) (Le x4) = false
  | equal_fm (Le x4) (A x17) = false
  | equal_fm (A x17) (Le x4) = false
  | equal_fm (Le x4) (E x16) = false
  | equal_fm (E x16) (Le x4) = false
  | equal_fm (Le x4) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Le x4) = false
  | equal_fm (Le x4) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Le x4) = false
  | equal_fm (Le x4) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Le x4) = false
  | equal_fm (Le x4) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Le x4) = false
  | equal_fm (Le x4) (NOT x11) = false
  | equal_fm (NOT x11) (Le x4) = false
  | equal_fm (Le x4) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Le x4) = false
  | equal_fm (Le x4) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Le x4) = false
  | equal_fm (Le x4) (NEq x8) = false
  | equal_fm (NEq x8) (Le x4) = false
  | equal_fm (Le x4) (Eq x7) = false
  | equal_fm (Eq x7) (Le x4) = false
  | equal_fm (Le x4) (Ge x6) = false
  | equal_fm (Ge x6) (Le x4) = false
  | equal_fm (Le x4) (Gt x5) = false
  | equal_fm (Gt x5) (Le x4) = false
  | equal_fm (Lt x3) (NClosed x19) = false
  | equal_fm (NClosed x19) (Lt x3) = false
  | equal_fm (Lt x3) (Closed x18) = false
  | equal_fm (Closed x18) (Lt x3) = false
  | equal_fm (Lt x3) (A x17) = false
  | equal_fm (A x17) (Lt x3) = false
  | equal_fm (Lt x3) (E x16) = false
  | equal_fm (E x16) (Lt x3) = false
  | equal_fm (Lt x3) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Lt x3) = false
  | equal_fm (Lt x3) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Lt x3) = false
  | equal_fm (Lt x3) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Lt x3) = false
  | equal_fm (Lt x3) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Lt x3) = false
  | equal_fm (Lt x3) (NOT x11) = false
  | equal_fm (NOT x11) (Lt x3) = false
  | equal_fm (Lt x3) (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) (Lt x3) = false
  | equal_fm (Lt x3) (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) (Lt x3) = false
  | equal_fm (Lt x3) (NEq x8) = false
  | equal_fm (NEq x8) (Lt x3) = false
  | equal_fm (Lt x3) (Eq x7) = false
  | equal_fm (Eq x7) (Lt x3) = false
  | equal_fm (Lt x3) (Ge x6) = false
  | equal_fm (Ge x6) (Lt x3) = false
  | equal_fm (Lt x3) (Gt x5) = false
  | equal_fm (Gt x5) (Lt x3) = false
  | equal_fm (Lt x3) (Le x4) = false
  | equal_fm (Le x4) (Lt x3) = false
  | equal_fm F (NClosed x19) = false
  | equal_fm (NClosed x19) F = false
  | equal_fm F (Closed x18) = false
  | equal_fm (Closed x18) F = false
  | equal_fm F (A x17) = false
  | equal_fm (A x17) F = false
  | equal_fm F (E x16) = false
  | equal_fm (E x16) F = false
  | equal_fm F (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) F = false
  | equal_fm F (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) F = false
  | equal_fm F (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) F = false
  | equal_fm F (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) F = false
  | equal_fm F (NOT x11) = false
  | equal_fm (NOT x11) F = false
  | equal_fm F (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) F = false
  | equal_fm F (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) F = false
  | equal_fm F (NEq x8) = false
  | equal_fm (NEq x8) F = false
  | equal_fm F (Eq x7) = false
  | equal_fm (Eq x7) F = false
  | equal_fm F (Ge x6) = false
  | equal_fm (Ge x6) F = false
  | equal_fm F (Gt x5) = false
  | equal_fm (Gt x5) F = false
  | equal_fm F (Le x4) = false
  | equal_fm (Le x4) F = false
  | equal_fm F (Lt x3) = false
  | equal_fm (Lt x3) F = false
  | equal_fm T (NClosed x19) = false
  | equal_fm (NClosed x19) T = false
  | equal_fm T (Closed x18) = false
  | equal_fm (Closed x18) T = false
  | equal_fm T (A x17) = false
  | equal_fm (A x17) T = false
  | equal_fm T (E x16) = false
  | equal_fm (E x16) T = false
  | equal_fm T (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) T = false
  | equal_fm T (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) T = false
  | equal_fm T (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) T = false
  | equal_fm T (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) T = false
  | equal_fm T (NOT x11) = false
  | equal_fm (NOT x11) T = false
  | equal_fm T (NDvd (x101, x102)) = false
  | equal_fm (NDvd (x101, x102)) T = false
  | equal_fm T (Dvd (x91, x92)) = false
  | equal_fm (Dvd (x91, x92)) T = false
  | equal_fm T (NEq x8) = false
  | equal_fm (NEq x8) T = false
  | equal_fm T (Eq x7) = false
  | equal_fm (Eq x7) T = false
  | equal_fm T (Ge x6) = false
  | equal_fm (Ge x6) T = false
  | equal_fm T (Gt x5) = false
  | equal_fm (Gt x5) T = false
  | equal_fm T (Le x4) = false
  | equal_fm (Le x4) T = false
  | equal_fm T (Lt x3) = false
  | equal_fm (Lt x3) T = false
  | equal_fm T F = false
  | equal_fm F T = false
  | equal_fm (NClosed x19) (NClosed y19) = equal_nat x19 y19
  | equal_fm (Closed x18) (Closed y18) = equal_nat x18 y18
  | equal_fm (A x17) (A y17) = equal_fm x17 y17
  | equal_fm (E x16) (E y16) = equal_fm x16 y16
  | equal_fm (Iff (x151, x152)) (Iff (y151, y152)) =
    equal_fm x151 y151 andalso equal_fm x152 y152
  | equal_fm (Imp (x141, x142)) (Imp (y141, y142)) =
    equal_fm x141 y141 andalso equal_fm x142 y142
  | equal_fm (Or (x131, x132)) (Or (y131, y132)) =
    equal_fm x131 y131 andalso equal_fm x132 y132
  | equal_fm (And (x121, x122)) (And (y121, y122)) =
    equal_fm x121 y121 andalso equal_fm x122 y122
  | equal_fm (NOT x11) (NOT y11) = equal_fm x11 y11
  | equal_fm (NDvd (x101, x102)) (NDvd (y101, y102)) =
    equal_inta x101 y101 andalso equal_numa x102 y102
  | equal_fm (Dvd (x91, x92)) (Dvd (y91, y92)) =
    equal_inta x91 y91 andalso equal_numa x92 y92
  | equal_fm (NEq x8) (NEq y8) = equal_numa x8 y8
  | equal_fm (Eq x7) (Eq y7) = equal_numa x7 y7
  | equal_fm (Ge x6) (Ge y6) = equal_numa x6 y6
  | equal_fm (Gt x5) (Gt y5) = equal_numa x5 y5
  | equal_fm (Le x4) (Le y4) = equal_numa x4 y4
  | equal_fm (Lt x3) (Lt y3) = equal_numa x3 y3
  | equal_fm F F = true
  | equal_fm T T = true;

fun djf f p q =
  (if equal_fm q T then T
    else (if equal_fm q F then f p
           else (case f p of T => T | F => q | Lt _ => Or (f p, q)
                  | Le _ => Or (f p, q) | Gt _ => Or (f p, q)
                  | Ge _ => Or (f p, q) | Eq _ => Or (f p, q)
                  | NEq _ => Or (f p, q) | Dvd (_, _) => Or (f p, q)
                  | NDvd (_, _) => Or (f p, q) | NOT _ => Or (f p, q)
                  | And (_, _) => Or (f p, q) | Or (_, _) => Or (f p, q)
                  | Imp (_, _) => Or (f p, q) | Iff (_, _) => Or (f p, q)
                  | E _ => Or (f p, q) | A _ => Or (f p, q)
                  | Closed _ => Or (f p, q) | NClosed _ => Or (f p, q))));

fun evaldjf f ps = foldr (djf f) ps F;

fun dj f p = evaldjf f (disjuncts p);

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int) (integer_of_nat m - integer_of_nat n));

val zero_nat : nat = Nat (0 : IntInf.int);

fun minusinf (And (p, q)) = And (minusinf p, minusinf q)
  | minusinf (Or (p, q)) = Or (minusinf p, minusinf q)
  | minusinf T = T
  | minusinf F = F
  | minusinf (Lt (C bo)) = Lt (C bo)
  | minusinf (Lt (Bound bp)) = Lt (Bound bp)
  | minusinf (Lt (Neg bt)) = Lt (Neg bt)
  | minusinf (Lt (Add (bu, bv))) = Lt (Add (bu, bv))
  | minusinf (Lt (Sub (bw, bx))) = Lt (Sub (bw, bx))
  | minusinf (Lt (Mul (by, bz))) = Lt (Mul (by, bz))
  | minusinf (Le (C co)) = Le (C co)
  | minusinf (Le (Bound cp)) = Le (Bound cp)
  | minusinf (Le (Neg ct)) = Le (Neg ct)
  | minusinf (Le (Add (cu, cv))) = Le (Add (cu, cv))
  | minusinf (Le (Sub (cw, cx))) = Le (Sub (cw, cx))
  | minusinf (Le (Mul (cy, cz))) = Le (Mul (cy, cz))
  | minusinf (Gt (C doa)) = Gt (C doa)
  | minusinf (Gt (Bound dp)) = Gt (Bound dp)
  | minusinf (Gt (Neg dt)) = Gt (Neg dt)
  | minusinf (Gt (Add (du, dv))) = Gt (Add (du, dv))
  | minusinf (Gt (Sub (dw, dx))) = Gt (Sub (dw, dx))
  | minusinf (Gt (Mul (dy, dz))) = Gt (Mul (dy, dz))
  | minusinf (Ge (C eo)) = Ge (C eo)
  | minusinf (Ge (Bound ep)) = Ge (Bound ep)
  | minusinf (Ge (Neg et)) = Ge (Neg et)
  | minusinf (Ge (Add (eu, ev))) = Ge (Add (eu, ev))
  | minusinf (Ge (Sub (ew, ex))) = Ge (Sub (ew, ex))
  | minusinf (Ge (Mul (ey, ez))) = Ge (Mul (ey, ez))
  | minusinf (Eq (C fo)) = Eq (C fo)
  | minusinf (Eq (Bound fp)) = Eq (Bound fp)
  | minusinf (Eq (Neg ft)) = Eq (Neg ft)
  | minusinf (Eq (Add (fu, fv))) = Eq (Add (fu, fv))
  | minusinf (Eq (Sub (fw, fx))) = Eq (Sub (fw, fx))
  | minusinf (Eq (Mul (fy, fz))) = Eq (Mul (fy, fz))
  | minusinf (NEq (C go)) = NEq (C go)
  | minusinf (NEq (Bound gp)) = NEq (Bound gp)
  | minusinf (NEq (Neg gt)) = NEq (Neg gt)
  | minusinf (NEq (Add (gu, gv))) = NEq (Add (gu, gv))
  | minusinf (NEq (Sub (gw, gx))) = NEq (Sub (gw, gx))
  | minusinf (NEq (Mul (gy, gz))) = NEq (Mul (gy, gz))
  | minusinf (Dvd (aa, ab)) = Dvd (aa, ab)
  | minusinf (NDvd (ac, ad)) = NDvd (ac, ad)
  | minusinf (NOT ae) = NOT ae
  | minusinf (Imp (aj, ak)) = Imp (aj, ak)
  | minusinf (Iff (al, am)) = Iff (al, am)
  | minusinf (E an) = E an
  | minusinf (A ao) = A ao
  | minusinf (Closed ap) = Closed ap
  | minusinf (NClosed aq) = NClosed aq
  | minusinf (Lt (CN (cm, c, e))) =
    (if equal_nat cm zero_nat then T
      else Lt (CN (suc (minus_nat cm one_nat), c, e)))
  | minusinf (Le (CN (dm, c, e))) =
    (if equal_nat dm zero_nat then T
      else Le (CN (suc (minus_nat dm one_nat), c, e)))
  | minusinf (Gt (CN (em, c, e))) =
    (if equal_nat em zero_nat then F
      else Gt (CN (suc (minus_nat em one_nat), c, e)))
  | minusinf (Ge (CN (fm, c, e))) =
    (if equal_nat fm zero_nat then F
      else Ge (CN (suc (minus_nat fm one_nat), c, e)))
  | minusinf (Eq (CN (gm, c, e))) =
    (if equal_nat gm zero_nat then F
      else Eq (CN (suc (minus_nat gm one_nat), c, e)))
  | minusinf (NEq (CN (hm, c, e))) =
    (if equal_nat hm zero_nat then T
      else NEq (CN (suc (minus_nat hm one_nat), c, e)));

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun numsubst0 t (C c) = C c
  | numsubst0 t (Bound n) = (if equal_nat n zero_nat then t else Bound n)
  | numsubst0 t (Neg a) = Neg (numsubst0 t a)
  | numsubst0 t (Add (a, b)) = Add (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Sub (a, b)) = Sub (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Mul (i, a)) = Mul (i, numsubst0 t a)
  | numsubst0 t (CN (v, i, a)) =
    (if equal_nat v zero_nat then Add (Mul (i, t), numsubst0 t a)
      else CN (suc (minus_nat v one_nat), i, numsubst0 t a));

fun subst0 t T = T
  | subst0 t F = F
  | subst0 t (Lt a) = Lt (numsubst0 t a)
  | subst0 t (Le a) = Le (numsubst0 t a)
  | subst0 t (Gt a) = Gt (numsubst0 t a)
  | subst0 t (Ge a) = Ge (numsubst0 t a)
  | subst0 t (Eq a) = Eq (numsubst0 t a)
  | subst0 t (NEq a) = NEq (numsubst0 t a)
  | subst0 t (Dvd (i, a)) = Dvd (i, numsubst0 t a)
  | subst0 t (NDvd (i, a)) = NDvd (i, numsubst0 t a)
  | subst0 t (NOT p) = NOT (subst0 t p)
  | subst0 t (And (p, q)) = And (subst0 t p, subst0 t q)
  | subst0 t (Or (p, q)) = Or (subst0 t p, subst0 t q)
  | subst0 t (Imp (p, q)) = Imp (subst0 t p, subst0 t q)
  | subst0 t (Iff (p, q)) = Iff (subst0 t p, subst0 t q)
  | subst0 t (Closed p) = Closed p
  | subst0 t (NClosed p) = NClosed p;

fun less_eq_int k l = integer_of_int k <= integer_of_int l;

fun less_int k l = integer_of_int k < integer_of_int l;

fun uminus_int k = Int_of_integer (~ (integer_of_int k));

fun abs_int i = (if less_int i zero_inta then uminus_int i else i);

fun dvd (A1_, A2_) a b =
  eq A2_ (moda (div_semiring_div A1_) b a)
    (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semidom o semidom_semidom_divide o
             semidom_divide_algebraic_semidom o algebraic_semidom_semiring_div)
            A1_));

fun nummul i (C j) = C (times_inta i j)
  | nummul i (CN (n, c, t)) = CN (n, times_inta c i, nummul i t)
  | nummul i (Bound v) = Mul (i, Bound v)
  | nummul i (Neg v) = Mul (i, Neg v)
  | nummul i (Add (v, va)) = Mul (i, Add (v, va))
  | nummul i (Sub (v, va)) = Mul (i, Sub (v, va))
  | nummul i (Mul (v, va)) = Mul (i, Mul (v, va));

fun numneg t = nummul (uminus_int (Int_of_integer (1 : IntInf.int))) t;

fun less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

fun numadd (CN (n1, c1, r1), CN (n2, c2, r2)) =
  (if equal_nat n1 n2
    then let
           val c = plus_inta c1 c2;
         in
           (if equal_inta c zero_inta then numadd (r1, r2)
             else CN (n1, c, numadd (r1, r2)))
         end
    else (if less_eq_nat n1 n2
           then CN (n1, c1, numadd (r1, Add (Mul (c2, Bound n2), r2)))
           else CN (n2, c2, numadd (Add (Mul (c1, Bound n1), r1), r2))))
  | numadd (CN (n1, c1, r1), C dd) = CN (n1, c1, numadd (r1, C dd))
  | numadd (CN (n1, c1, r1), Bound de) = CN (n1, c1, numadd (r1, Bound de))
  | numadd (CN (n1, c1, r1), Neg di) = CN (n1, c1, numadd (r1, Neg di))
  | numadd (CN (n1, c1, r1), Add (dj, dk)) =
    CN (n1, c1, numadd (r1, Add (dj, dk)))
  | numadd (CN (n1, c1, r1), Sub (dl, dm)) =
    CN (n1, c1, numadd (r1, Sub (dl, dm)))
  | numadd (CN (n1, c1, r1), Mul (dn, doa)) =
    CN (n1, c1, numadd (r1, Mul (dn, doa)))
  | numadd (C w, CN (n2, c2, r2)) = CN (n2, c2, numadd (C w, r2))
  | numadd (Bound x, CN (n2, c2, r2)) = CN (n2, c2, numadd (Bound x, r2))
  | numadd (Neg ac, CN (n2, c2, r2)) = CN (n2, c2, numadd (Neg ac, r2))
  | numadd (Add (ad, ae), CN (n2, c2, r2)) =
    CN (n2, c2, numadd (Add (ad, ae), r2))
  | numadd (Sub (af, ag), CN (n2, c2, r2)) =
    CN (n2, c2, numadd (Sub (af, ag), r2))
  | numadd (Mul (ah, ai), CN (n2, c2, r2)) =
    CN (n2, c2, numadd (Mul (ah, ai), r2))
  | numadd (C b1, C b2) = C (plus_inta b1 b2)
  | numadd (C aj, Bound bi) = Add (C aj, Bound bi)
  | numadd (C aj, Neg bm) = Add (C aj, Neg bm)
  | numadd (C aj, Add (bn, bo)) = Add (C aj, Add (bn, bo))
  | numadd (C aj, Sub (bp, bq)) = Add (C aj, Sub (bp, bq))
  | numadd (C aj, Mul (br, bs)) = Add (C aj, Mul (br, bs))
  | numadd (Bound ak, C cf) = Add (Bound ak, C cf)
  | numadd (Bound ak, Bound cg) = Add (Bound ak, Bound cg)
  | numadd (Bound ak, Neg ck) = Add (Bound ak, Neg ck)
  | numadd (Bound ak, Add (cl, cm)) = Add (Bound ak, Add (cl, cm))
  | numadd (Bound ak, Sub (cn, co)) = Add (Bound ak, Sub (cn, co))
  | numadd (Bound ak, Mul (cp, cq)) = Add (Bound ak, Mul (cp, cq))
  | numadd (Neg ao, C en) = Add (Neg ao, C en)
  | numadd (Neg ao, Bound eo) = Add (Neg ao, Bound eo)
  | numadd (Neg ao, Neg et) = Add (Neg ao, Neg et)
  | numadd (Neg ao, Add (eu, ev)) = Add (Neg ao, Add (eu, ev))
  | numadd (Neg ao, Sub (ew, ex)) = Add (Neg ao, Sub (ew, ex))
  | numadd (Neg ao, Mul (ey, ez)) = Add (Neg ao, Mul (ey, ez))
  | numadd (Add (ap, aq), C fm) = Add (Add (ap, aq), C fm)
  | numadd (Add (ap, aq), Bound fna) = Add (Add (ap, aq), Bound fna)
  | numadd (Add (ap, aq), Neg fr) = Add (Add (ap, aq), Neg fr)
  | numadd (Add (ap, aq), Add (fs, ft)) = Add (Add (ap, aq), Add (fs, ft))
  | numadd (Add (ap, aq), Sub (fu, fv)) = Add (Add (ap, aq), Sub (fu, fv))
  | numadd (Add (ap, aq), Mul (fw, fx)) = Add (Add (ap, aq), Mul (fw, fx))
  | numadd (Sub (ar, asa), C gk) = Add (Sub (ar, asa), C gk)
  | numadd (Sub (ar, asa), Bound gl) = Add (Sub (ar, asa), Bound gl)
  | numadd (Sub (ar, asa), Neg gp) = Add (Sub (ar, asa), Neg gp)
  | numadd (Sub (ar, asa), Add (gq, gr)) = Add (Sub (ar, asa), Add (gq, gr))
  | numadd (Sub (ar, asa), Sub (gs, gt)) = Add (Sub (ar, asa), Sub (gs, gt))
  | numadd (Sub (ar, asa), Mul (gu, gv)) = Add (Sub (ar, asa), Mul (gu, gv))
  | numadd (Mul (at, au), C hi) = Add (Mul (at, au), C hi)
  | numadd (Mul (at, au), Bound hj) = Add (Mul (at, au), Bound hj)
  | numadd (Mul (at, au), Neg hn) = Add (Mul (at, au), Neg hn)
  | numadd (Mul (at, au), Add (ho, hp)) = Add (Mul (at, au), Add (ho, hp))
  | numadd (Mul (at, au), Sub (hq, hr)) = Add (Mul (at, au), Sub (hq, hr))
  | numadd (Mul (at, au), Mul (hs, ht)) = Add (Mul (at, au), Mul (hs, ht));

fun numsub s t = (if equal_numa s t then C zero_inta else numadd (s, numneg t));

fun simpnum (C j) = C j
  | simpnum (Bound n) = CN (n, Int_of_integer (1 : IntInf.int), C zero_inta)
  | simpnum (Neg t) = numneg (simpnum t)
  | simpnum (Add (t, s)) = numadd (simpnum t, simpnum s)
  | simpnum (Sub (t, s)) = numsub (simpnum t) (simpnum s)
  | simpnum (Mul (i, t)) =
    (if equal_inta i zero_inta then C zero_inta else nummul i (simpnum t))
  | simpnum (CN (v, va, vb)) = CN (v, va, vb);

fun disj p q =
  (if equal_fm p T orelse equal_fm q T then T
    else (if equal_fm p F then q else (if equal_fm q F then p else Or (p, q))));

fun conj p q =
  (if equal_fm p F orelse equal_fm q F then F
    else (if equal_fm p T then q
           else (if equal_fm q T then p else And (p, q))));

fun nota (NOT p) = p
  | nota T = F
  | nota F = T
  | nota (Lt v) = NOT (Lt v)
  | nota (Le v) = NOT (Le v)
  | nota (Gt v) = NOT (Gt v)
  | nota (Ge v) = NOT (Ge v)
  | nota (Eq v) = NOT (Eq v)
  | nota (NEq v) = NOT (NEq v)
  | nota (Dvd (v, va)) = NOT (Dvd (v, va))
  | nota (NDvd (v, va)) = NOT (NDvd (v, va))
  | nota (And (v, va)) = NOT (And (v, va))
  | nota (Or (v, va)) = NOT (Or (v, va))
  | nota (Imp (v, va)) = NOT (Imp (v, va))
  | nota (Iff (v, va)) = NOT (Iff (v, va))
  | nota (E v) = NOT (E v)
  | nota (A v) = NOT (A v)
  | nota (Closed v) = NOT (Closed v)
  | nota (NClosed v) = NOT (NClosed v);

fun imp p q =
  (if equal_fm p F orelse equal_fm q T then T
    else (if equal_fm p T then q
           else (if equal_fm q F then nota p else Imp (p, q))));

fun iff p q =
  (if equal_fm p q then T
    else (if equal_fm p (nota q) orelse equal_fm (nota p) q then F
           else (if equal_fm p F then nota q
                  else (if equal_fm q F then nota p
                         else (if equal_fm p T then q
                                else (if equal_fm q T then p
                                       else Iff (p, q)))))));

fun simpfm (And (p, q)) = conj (simpfm p) (simpfm q)
  | simpfm (Or (p, q)) = disj (simpfm p) (simpfm q)
  | simpfm (Imp (p, q)) = imp (simpfm p) (simpfm q)
  | simpfm (Iff (p, q)) = iff (simpfm p) (simpfm q)
  | simpfm (NOT p) = nota (simpfm p)
  | simpfm (Lt a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if less_int v zero_inta then T else F)
        | Bound _ => Lt aa | CN (_, _, _) => Lt aa | Neg _ => Lt aa
        | Add (_, _) => Lt aa | Sub (_, _) => Lt aa | Mul (_, _) => Lt aa)
    end
  | simpfm (Le a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if less_eq_int v zero_inta then T else F)
        | Bound _ => Le aa | CN (_, _, _) => Le aa | Neg _ => Le aa
        | Add (_, _) => Le aa | Sub (_, _) => Le aa | Mul (_, _) => Le aa)
    end
  | simpfm (Gt a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if less_int zero_inta v then T else F)
        | Bound _ => Gt aa | CN (_, _, _) => Gt aa | Neg _ => Gt aa
        | Add (_, _) => Gt aa | Sub (_, _) => Gt aa | Mul (_, _) => Gt aa)
    end
  | simpfm (Ge a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if less_eq_int zero_inta v then T else F)
        | Bound _ => Ge aa | CN (_, _, _) => Ge aa | Neg _ => Ge aa
        | Add (_, _) => Ge aa | Sub (_, _) => Ge aa | Mul (_, _) => Ge aa)
    end
  | simpfm (Eq a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if equal_inta v zero_inta then T else F)
        | Bound _ => Eq aa | CN (_, _, _) => Eq aa | Neg _ => Eq aa
        | Add (_, _) => Eq aa | Sub (_, _) => Eq aa | Mul (_, _) => Eq aa)
    end
  | simpfm (NEq a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if not (equal_inta v zero_inta) then T else F)
        | Bound _ => NEq aa | CN (_, _, _) => NEq aa | Neg _ => NEq aa
        | Add (_, _) => NEq aa | Sub (_, _) => NEq aa | Mul (_, _) => NEq aa)
    end
  | simpfm (Dvd (i, a)) =
    (if equal_inta i zero_inta then simpfm (Eq a)
      else (if equal_inta (abs_int i) (Int_of_integer (1 : IntInf.int)) then T
             else let
                    val aa = simpnum a;
                  in
                    (case aa
                      of C v =>
                        (if dvd (semiring_div_int, equal_int) i v then T else F)
                      | Bound _ => Dvd (i, aa) | CN (_, _, _) => Dvd (i, aa)
                      | Neg _ => Dvd (i, aa) | Add (_, _) => Dvd (i, aa)
                      | Sub (_, _) => Dvd (i, aa) | Mul (_, _) => Dvd (i, aa))
                  end))
  | simpfm (NDvd (i, a)) =
    (if equal_inta i zero_inta then simpfm (NEq a)
      else (if equal_inta (abs_int i) (Int_of_integer (1 : IntInf.int)) then F
             else let
                    val aa = simpnum a;
                  in
                    (case aa
                      of C v =>
                        (if not (dvd (semiring_div_int, equal_int) i v) then T
                          else F)
                      | Bound _ => NDvd (i, aa) | CN (_, _, _) => NDvd (i, aa)
                      | Neg _ => NDvd (i, aa) | Add (_, _) => NDvd (i, aa)
                      | Sub (_, _) => NDvd (i, aa) | Mul (_, _) => NDvd (i, aa))
                  end))
  | simpfm T = T
  | simpfm F = F
  | simpfm (E v) = E v
  | simpfm (A v) = A v
  | simpfm (Closed v) = Closed v
  | simpfm (NClosed v) = NClosed v;

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length zero_nat x;

fun a_beta (And (p, q)) = (fn k => And (a_beta p k, a_beta q k))
  | a_beta (Or (p, q)) = (fn k => Or (a_beta p k, a_beta q k))
  | a_beta T = (fn _ => T)
  | a_beta F = (fn _ => F)
  | a_beta (Lt (C bo)) = (fn _ => Lt (C bo))
  | a_beta (Lt (Bound bp)) = (fn _ => Lt (Bound bp))
  | a_beta (Lt (Neg bt)) = (fn _ => Lt (Neg bt))
  | a_beta (Lt (Add (bu, bv))) = (fn _ => Lt (Add (bu, bv)))
  | a_beta (Lt (Sub (bw, bx))) = (fn _ => Lt (Sub (bw, bx)))
  | a_beta (Lt (Mul (by, bz))) = (fn _ => Lt (Mul (by, bz)))
  | a_beta (Le (C co)) = (fn _ => Le (C co))
  | a_beta (Le (Bound cp)) = (fn _ => Le (Bound cp))
  | a_beta (Le (Neg ct)) = (fn _ => Le (Neg ct))
  | a_beta (Le (Add (cu, cv))) = (fn _ => Le (Add (cu, cv)))
  | a_beta (Le (Sub (cw, cx))) = (fn _ => Le (Sub (cw, cx)))
  | a_beta (Le (Mul (cy, cz))) = (fn _ => Le (Mul (cy, cz)))
  | a_beta (Gt (C doa)) = (fn _ => Gt (C doa))
  | a_beta (Gt (Bound dp)) = (fn _ => Gt (Bound dp))
  | a_beta (Gt (Neg dt)) = (fn _ => Gt (Neg dt))
  | a_beta (Gt (Add (du, dv))) = (fn _ => Gt (Add (du, dv)))
  | a_beta (Gt (Sub (dw, dx))) = (fn _ => Gt (Sub (dw, dx)))
  | a_beta (Gt (Mul (dy, dz))) = (fn _ => Gt (Mul (dy, dz)))
  | a_beta (Ge (C eo)) = (fn _ => Ge (C eo))
  | a_beta (Ge (Bound ep)) = (fn _ => Ge (Bound ep))
  | a_beta (Ge (Neg et)) = (fn _ => Ge (Neg et))
  | a_beta (Ge (Add (eu, ev))) = (fn _ => Ge (Add (eu, ev)))
  | a_beta (Ge (Sub (ew, ex))) = (fn _ => Ge (Sub (ew, ex)))
  | a_beta (Ge (Mul (ey, ez))) = (fn _ => Ge (Mul (ey, ez)))
  | a_beta (Eq (C fo)) = (fn _ => Eq (C fo))
  | a_beta (Eq (Bound fp)) = (fn _ => Eq (Bound fp))
  | a_beta (Eq (Neg ft)) = (fn _ => Eq (Neg ft))
  | a_beta (Eq (Add (fu, fv))) = (fn _ => Eq (Add (fu, fv)))
  | a_beta (Eq (Sub (fw, fx))) = (fn _ => Eq (Sub (fw, fx)))
  | a_beta (Eq (Mul (fy, fz))) = (fn _ => Eq (Mul (fy, fz)))
  | a_beta (NEq (C go)) = (fn _ => NEq (C go))
  | a_beta (NEq (Bound gp)) = (fn _ => NEq (Bound gp))
  | a_beta (NEq (Neg gt)) = (fn _ => NEq (Neg gt))
  | a_beta (NEq (Add (gu, gv))) = (fn _ => NEq (Add (gu, gv)))
  | a_beta (NEq (Sub (gw, gx))) = (fn _ => NEq (Sub (gw, gx)))
  | a_beta (NEq (Mul (gy, gz))) = (fn _ => NEq (Mul (gy, gz)))
  | a_beta (Dvd (aa, C ho)) = (fn _ => Dvd (aa, C ho))
  | a_beta (Dvd (aa, Bound hp)) = (fn _ => Dvd (aa, Bound hp))
  | a_beta (Dvd (aa, Neg ht)) = (fn _ => Dvd (aa, Neg ht))
  | a_beta (Dvd (aa, Add (hu, hv))) = (fn _ => Dvd (aa, Add (hu, hv)))
  | a_beta (Dvd (aa, Sub (hw, hx))) = (fn _ => Dvd (aa, Sub (hw, hx)))
  | a_beta (Dvd (aa, Mul (hy, hz))) = (fn _ => Dvd (aa, Mul (hy, hz)))
  | a_beta (NDvd (ac, C io)) = (fn _ => NDvd (ac, C io))
  | a_beta (NDvd (ac, Bound ip)) = (fn _ => NDvd (ac, Bound ip))
  | a_beta (NDvd (ac, Neg it)) = (fn _ => NDvd (ac, Neg it))
  | a_beta (NDvd (ac, Add (iu, iv))) = (fn _ => NDvd (ac, Add (iu, iv)))
  | a_beta (NDvd (ac, Sub (iw, ix))) = (fn _ => NDvd (ac, Sub (iw, ix)))
  | a_beta (NDvd (ac, Mul (iy, iz))) = (fn _ => NDvd (ac, Mul (iy, iz)))
  | a_beta (NOT ae) = (fn _ => NOT ae)
  | a_beta (Imp (aj, ak)) = (fn _ => Imp (aj, ak))
  | a_beta (Iff (al, am)) = (fn _ => Iff (al, am))
  | a_beta (E an) = (fn _ => E an)
  | a_beta (A ao) = (fn _ => A ao)
  | a_beta (Closed ap) = (fn _ => Closed ap)
  | a_beta (NClosed aq) = (fn _ => NClosed aq)
  | a_beta (Lt (CN (cm, c, e))) =
    (if equal_nat cm zero_nat
      then (fn k =>
             Lt (CN (zero_nat, Int_of_integer (1 : IntInf.int),
                      Mul (divide_inta k c, e))))
      else (fn _ => Lt (CN (suc (minus_nat cm one_nat), c, e))))
  | a_beta (Le (CN (dm, c, e))) =
    (if equal_nat dm zero_nat
      then (fn k =>
             Le (CN (zero_nat, Int_of_integer (1 : IntInf.int),
                      Mul (divide_inta k c, e))))
      else (fn _ => Le (CN (suc (minus_nat dm one_nat), c, e))))
  | a_beta (Gt (CN (em, c, e))) =
    (if equal_nat em zero_nat
      then (fn k =>
             Gt (CN (zero_nat, Int_of_integer (1 : IntInf.int),
                      Mul (divide_inta k c, e))))
      else (fn _ => Gt (CN (suc (minus_nat em one_nat), c, e))))
  | a_beta (Ge (CN (fm, c, e))) =
    (if equal_nat fm zero_nat
      then (fn k =>
             Ge (CN (zero_nat, Int_of_integer (1 : IntInf.int),
                      Mul (divide_inta k c, e))))
      else (fn _ => Ge (CN (suc (minus_nat fm one_nat), c, e))))
  | a_beta (Eq (CN (gm, c, e))) =
    (if equal_nat gm zero_nat
      then (fn k =>
             Eq (CN (zero_nat, Int_of_integer (1 : IntInf.int),
                      Mul (divide_inta k c, e))))
      else (fn _ => Eq (CN (suc (minus_nat gm one_nat), c, e))))
  | a_beta (NEq (CN (hm, c, e))) =
    (if equal_nat hm zero_nat
      then (fn k =>
             NEq (CN (zero_nat, Int_of_integer (1 : IntInf.int),
                       Mul (divide_inta k c, e))))
      else (fn _ => NEq (CN (suc (minus_nat hm one_nat), c, e))))
  | a_beta (Dvd (i, CN (im, c, e))) =
    (if equal_nat im zero_nat
      then (fn k =>
             Dvd (times_inta (divide_inta k c) i,
                   CN (zero_nat, Int_of_integer (1 : IntInf.int),
                        Mul (divide_inta k c, e))))
      else (fn _ => Dvd (i, CN (suc (minus_nat im one_nat), c, e))))
  | a_beta (NDvd (i, CN (jm, c, e))) =
    (if equal_nat jm zero_nat
      then (fn k =>
             NDvd (times_inta (divide_inta k c) i,
                    CN (zero_nat, Int_of_integer (1 : IntInf.int),
                         Mul (divide_inta k c, e))))
      else (fn _ => NDvd (i, CN (suc (minus_nat jm one_nat), c, e))));

fun gcd_int k l =
  abs_int
    (if equal_inta l zero_inta then k
      else gcd_int l (mod_int (abs_int k) (abs_int l)));

fun lcm_int a b =
  divide_inta (times_inta (abs_int a) (abs_int b)) (gcd_int a b);

fun delta (And (p, q)) = lcm_int (delta p) (delta q)
  | delta (Or (p, q)) = lcm_int (delta p) (delta q)
  | delta T = Int_of_integer (1 : IntInf.int)
  | delta F = Int_of_integer (1 : IntInf.int)
  | delta (Lt u) = Int_of_integer (1 : IntInf.int)
  | delta (Le v) = Int_of_integer (1 : IntInf.int)
  | delta (Gt w) = Int_of_integer (1 : IntInf.int)
  | delta (Ge x) = Int_of_integer (1 : IntInf.int)
  | delta (Eq y) = Int_of_integer (1 : IntInf.int)
  | delta (NEq z) = Int_of_integer (1 : IntInf.int)
  | delta (Dvd (aa, C bo)) = Int_of_integer (1 : IntInf.int)
  | delta (Dvd (aa, Bound bp)) = Int_of_integer (1 : IntInf.int)
  | delta (Dvd (aa, Neg bt)) = Int_of_integer (1 : IntInf.int)
  | delta (Dvd (aa, Add (bu, bv))) = Int_of_integer (1 : IntInf.int)
  | delta (Dvd (aa, Sub (bw, bx))) = Int_of_integer (1 : IntInf.int)
  | delta (Dvd (aa, Mul (by, bz))) = Int_of_integer (1 : IntInf.int)
  | delta (NDvd (ac, C co)) = Int_of_integer (1 : IntInf.int)
  | delta (NDvd (ac, Bound cp)) = Int_of_integer (1 : IntInf.int)
  | delta (NDvd (ac, Neg ct)) = Int_of_integer (1 : IntInf.int)
  | delta (NDvd (ac, Add (cu, cv))) = Int_of_integer (1 : IntInf.int)
  | delta (NDvd (ac, Sub (cw, cx))) = Int_of_integer (1 : IntInf.int)
  | delta (NDvd (ac, Mul (cy, cz))) = Int_of_integer (1 : IntInf.int)
  | delta (NOT ae) = Int_of_integer (1 : IntInf.int)
  | delta (Imp (aj, ak)) = Int_of_integer (1 : IntInf.int)
  | delta (Iff (al, am)) = Int_of_integer (1 : IntInf.int)
  | delta (E an) = Int_of_integer (1 : IntInf.int)
  | delta (A ao) = Int_of_integer (1 : IntInf.int)
  | delta (Closed ap) = Int_of_integer (1 : IntInf.int)
  | delta (NClosed aq) = Int_of_integer (1 : IntInf.int)
  | delta (Dvd (i, CN (cm, c, e))) =
    (if equal_nat cm zero_nat then i else Int_of_integer (1 : IntInf.int))
  | delta (NDvd (i, CN (dm, c, e))) =
    (if equal_nat dm zero_nat then i else Int_of_integer (1 : IntInf.int));

fun alpha (And (p, q)) = alpha p @ alpha q
  | alpha (Or (p, q)) = alpha p @ alpha q
  | alpha T = []
  | alpha F = []
  | alpha (Lt (C bo)) = []
  | alpha (Lt (Bound bp)) = []
  | alpha (Lt (Neg bt)) = []
  | alpha (Lt (Add (bu, bv))) = []
  | alpha (Lt (Sub (bw, bx))) = []
  | alpha (Lt (Mul (by, bz))) = []
  | alpha (Le (C co)) = []
  | alpha (Le (Bound cp)) = []
  | alpha (Le (Neg ct)) = []
  | alpha (Le (Add (cu, cv))) = []
  | alpha (Le (Sub (cw, cx))) = []
  | alpha (Le (Mul (cy, cz))) = []
  | alpha (Gt (C doa)) = []
  | alpha (Gt (Bound dp)) = []
  | alpha (Gt (Neg dt)) = []
  | alpha (Gt (Add (du, dv))) = []
  | alpha (Gt (Sub (dw, dx))) = []
  | alpha (Gt (Mul (dy, dz))) = []
  | alpha (Ge (C eo)) = []
  | alpha (Ge (Bound ep)) = []
  | alpha (Ge (Neg et)) = []
  | alpha (Ge (Add (eu, ev))) = []
  | alpha (Ge (Sub (ew, ex))) = []
  | alpha (Ge (Mul (ey, ez))) = []
  | alpha (Eq (C fo)) = []
  | alpha (Eq (Bound fp)) = []
  | alpha (Eq (Neg ft)) = []
  | alpha (Eq (Add (fu, fv))) = []
  | alpha (Eq (Sub (fw, fx))) = []
  | alpha (Eq (Mul (fy, fz))) = []
  | alpha (NEq (C go)) = []
  | alpha (NEq (Bound gp)) = []
  | alpha (NEq (Neg gt)) = []
  | alpha (NEq (Add (gu, gv))) = []
  | alpha (NEq (Sub (gw, gx))) = []
  | alpha (NEq (Mul (gy, gz))) = []
  | alpha (Dvd (aa, ab)) = []
  | alpha (NDvd (ac, ad)) = []
  | alpha (NOT ae) = []
  | alpha (Imp (aj, ak)) = []
  | alpha (Iff (al, am)) = []
  | alpha (E an) = []
  | alpha (A ao) = []
  | alpha (Closed ap) = []
  | alpha (NClosed aq) = []
  | alpha (Lt (CN (cm, c, e))) = (if equal_nat cm zero_nat then [e] else [])
  | alpha (Le (CN (dm, c, e))) =
    (if equal_nat dm zero_nat
      then [Add (C (uminus_int (Int_of_integer (1 : IntInf.int))), e)] else [])
  | alpha (Gt (CN (em, c, e))) = (if equal_nat em zero_nat then [] else [])
  | alpha (Ge (CN (fm, c, e))) = (if equal_nat fm zero_nat then [] else [])
  | alpha (Eq (CN (gm, c, e))) =
    (if equal_nat gm zero_nat
      then [Add (C (uminus_int (Int_of_integer (1 : IntInf.int))), e)] else [])
  | alpha (NEq (CN (hm, c, e))) = (if equal_nat hm zero_nat then [e] else []);

fun zeta (And (p, q)) = lcm_int (zeta p) (zeta q)
  | zeta (Or (p, q)) = lcm_int (zeta p) (zeta q)
  | zeta T = Int_of_integer (1 : IntInf.int)
  | zeta F = Int_of_integer (1 : IntInf.int)
  | zeta (Lt (C bo)) = Int_of_integer (1 : IntInf.int)
  | zeta (Lt (Bound bp)) = Int_of_integer (1 : IntInf.int)
  | zeta (Lt (Neg bt)) = Int_of_integer (1 : IntInf.int)
  | zeta (Lt (Add (bu, bv))) = Int_of_integer (1 : IntInf.int)
  | zeta (Lt (Sub (bw, bx))) = Int_of_integer (1 : IntInf.int)
  | zeta (Lt (Mul (by, bz))) = Int_of_integer (1 : IntInf.int)
  | zeta (Le (C co)) = Int_of_integer (1 : IntInf.int)
  | zeta (Le (Bound cp)) = Int_of_integer (1 : IntInf.int)
  | zeta (Le (Neg ct)) = Int_of_integer (1 : IntInf.int)
  | zeta (Le (Add (cu, cv))) = Int_of_integer (1 : IntInf.int)
  | zeta (Le (Sub (cw, cx))) = Int_of_integer (1 : IntInf.int)
  | zeta (Le (Mul (cy, cz))) = Int_of_integer (1 : IntInf.int)
  | zeta (Gt (C doa)) = Int_of_integer (1 : IntInf.int)
  | zeta (Gt (Bound dp)) = Int_of_integer (1 : IntInf.int)
  | zeta (Gt (Neg dt)) = Int_of_integer (1 : IntInf.int)
  | zeta (Gt (Add (du, dv))) = Int_of_integer (1 : IntInf.int)
  | zeta (Gt (Sub (dw, dx))) = Int_of_integer (1 : IntInf.int)
  | zeta (Gt (Mul (dy, dz))) = Int_of_integer (1 : IntInf.int)
  | zeta (Ge (C eo)) = Int_of_integer (1 : IntInf.int)
  | zeta (Ge (Bound ep)) = Int_of_integer (1 : IntInf.int)
  | zeta (Ge (Neg et)) = Int_of_integer (1 : IntInf.int)
  | zeta (Ge (Add (eu, ev))) = Int_of_integer (1 : IntInf.int)
  | zeta (Ge (Sub (ew, ex))) = Int_of_integer (1 : IntInf.int)
  | zeta (Ge (Mul (ey, ez))) = Int_of_integer (1 : IntInf.int)
  | zeta (Eq (C fo)) = Int_of_integer (1 : IntInf.int)
  | zeta (Eq (Bound fp)) = Int_of_integer (1 : IntInf.int)
  | zeta (Eq (Neg ft)) = Int_of_integer (1 : IntInf.int)
  | zeta (Eq (Add (fu, fv))) = Int_of_integer (1 : IntInf.int)
  | zeta (Eq (Sub (fw, fx))) = Int_of_integer (1 : IntInf.int)
  | zeta (Eq (Mul (fy, fz))) = Int_of_integer (1 : IntInf.int)
  | zeta (NEq (C go)) = Int_of_integer (1 : IntInf.int)
  | zeta (NEq (Bound gp)) = Int_of_integer (1 : IntInf.int)
  | zeta (NEq (Neg gt)) = Int_of_integer (1 : IntInf.int)
  | zeta (NEq (Add (gu, gv))) = Int_of_integer (1 : IntInf.int)
  | zeta (NEq (Sub (gw, gx))) = Int_of_integer (1 : IntInf.int)
  | zeta (NEq (Mul (gy, gz))) = Int_of_integer (1 : IntInf.int)
  | zeta (Dvd (aa, C ho)) = Int_of_integer (1 : IntInf.int)
  | zeta (Dvd (aa, Bound hp)) = Int_of_integer (1 : IntInf.int)
  | zeta (Dvd (aa, Neg ht)) = Int_of_integer (1 : IntInf.int)
  | zeta (Dvd (aa, Add (hu, hv))) = Int_of_integer (1 : IntInf.int)
  | zeta (Dvd (aa, Sub (hw, hx))) = Int_of_integer (1 : IntInf.int)
  | zeta (Dvd (aa, Mul (hy, hz))) = Int_of_integer (1 : IntInf.int)
  | zeta (NDvd (ac, C io)) = Int_of_integer (1 : IntInf.int)
  | zeta (NDvd (ac, Bound ip)) = Int_of_integer (1 : IntInf.int)
  | zeta (NDvd (ac, Neg it)) = Int_of_integer (1 : IntInf.int)
  | zeta (NDvd (ac, Add (iu, iv))) = Int_of_integer (1 : IntInf.int)
  | zeta (NDvd (ac, Sub (iw, ix))) = Int_of_integer (1 : IntInf.int)
  | zeta (NDvd (ac, Mul (iy, iz))) = Int_of_integer (1 : IntInf.int)
  | zeta (NOT ae) = Int_of_integer (1 : IntInf.int)
  | zeta (Imp (aj, ak)) = Int_of_integer (1 : IntInf.int)
  | zeta (Iff (al, am)) = Int_of_integer (1 : IntInf.int)
  | zeta (E an) = Int_of_integer (1 : IntInf.int)
  | zeta (A ao) = Int_of_integer (1 : IntInf.int)
  | zeta (Closed ap) = Int_of_integer (1 : IntInf.int)
  | zeta (NClosed aq) = Int_of_integer (1 : IntInf.int)
  | zeta (Lt (CN (cm, c, e))) =
    (if equal_nat cm zero_nat then c else Int_of_integer (1 : IntInf.int))
  | zeta (Le (CN (dm, c, e))) =
    (if equal_nat dm zero_nat then c else Int_of_integer (1 : IntInf.int))
  | zeta (Gt (CN (em, c, e))) =
    (if equal_nat em zero_nat then c else Int_of_integer (1 : IntInf.int))
  | zeta (Ge (CN (fm, c, e))) =
    (if equal_nat fm zero_nat then c else Int_of_integer (1 : IntInf.int))
  | zeta (Eq (CN (gm, c, e))) =
    (if equal_nat gm zero_nat then c else Int_of_integer (1 : IntInf.int))
  | zeta (NEq (CN (hm, c, e))) =
    (if equal_nat hm zero_nat then c else Int_of_integer (1 : IntInf.int))
  | zeta (Dvd (i, CN (im, c, e))) =
    (if equal_nat im zero_nat then c else Int_of_integer (1 : IntInf.int))
  | zeta (NDvd (i, CN (jm, c, e))) =
    (if equal_nat jm zero_nat then c else Int_of_integer (1 : IntInf.int));

fun beta (And (p, q)) = beta p @ beta q
  | beta (Or (p, q)) = beta p @ beta q
  | beta T = []
  | beta F = []
  | beta (Lt (C bo)) = []
  | beta (Lt (Bound bp)) = []
  | beta (Lt (Neg bt)) = []
  | beta (Lt (Add (bu, bv))) = []
  | beta (Lt (Sub (bw, bx))) = []
  | beta (Lt (Mul (by, bz))) = []
  | beta (Le (C co)) = []
  | beta (Le (Bound cp)) = []
  | beta (Le (Neg ct)) = []
  | beta (Le (Add (cu, cv))) = []
  | beta (Le (Sub (cw, cx))) = []
  | beta (Le (Mul (cy, cz))) = []
  | beta (Gt (C doa)) = []
  | beta (Gt (Bound dp)) = []
  | beta (Gt (Neg dt)) = []
  | beta (Gt (Add (du, dv))) = []
  | beta (Gt (Sub (dw, dx))) = []
  | beta (Gt (Mul (dy, dz))) = []
  | beta (Ge (C eo)) = []
  | beta (Ge (Bound ep)) = []
  | beta (Ge (Neg et)) = []
  | beta (Ge (Add (eu, ev))) = []
  | beta (Ge (Sub (ew, ex))) = []
  | beta (Ge (Mul (ey, ez))) = []
  | beta (Eq (C fo)) = []
  | beta (Eq (Bound fp)) = []
  | beta (Eq (Neg ft)) = []
  | beta (Eq (Add (fu, fv))) = []
  | beta (Eq (Sub (fw, fx))) = []
  | beta (Eq (Mul (fy, fz))) = []
  | beta (NEq (C go)) = []
  | beta (NEq (Bound gp)) = []
  | beta (NEq (Neg gt)) = []
  | beta (NEq (Add (gu, gv))) = []
  | beta (NEq (Sub (gw, gx))) = []
  | beta (NEq (Mul (gy, gz))) = []
  | beta (Dvd (aa, ab)) = []
  | beta (NDvd (ac, ad)) = []
  | beta (NOT ae) = []
  | beta (Imp (aj, ak)) = []
  | beta (Iff (al, am)) = []
  | beta (E an) = []
  | beta (A ao) = []
  | beta (Closed ap) = []
  | beta (NClosed aq) = []
  | beta (Lt (CN (cm, c, e))) = (if equal_nat cm zero_nat then [] else [])
  | beta (Le (CN (dm, c, e))) = (if equal_nat dm zero_nat then [] else [])
  | beta (Gt (CN (em, c, e))) = (if equal_nat em zero_nat then [Neg e] else [])
  | beta (Ge (CN (fm, c, e))) =
    (if equal_nat fm zero_nat
      then [Sub (C (uminus_int (Int_of_integer (1 : IntInf.int))), e)] else [])
  | beta (Eq (CN (gm, c, e))) =
    (if equal_nat gm zero_nat
      then [Sub (C (uminus_int (Int_of_integer (1 : IntInf.int))), e)] else [])
  | beta (NEq (CN (hm, c, e))) =
    (if equal_nat hm zero_nat then [Neg e] else []);

fun mirror (And (p, q)) = And (mirror p, mirror q)
  | mirror (Or (p, q)) = Or (mirror p, mirror q)
  | mirror T = T
  | mirror F = F
  | mirror (Lt (C bo)) = Lt (C bo)
  | mirror (Lt (Bound bp)) = Lt (Bound bp)
  | mirror (Lt (Neg bt)) = Lt (Neg bt)
  | mirror (Lt (Add (bu, bv))) = Lt (Add (bu, bv))
  | mirror (Lt (Sub (bw, bx))) = Lt (Sub (bw, bx))
  | mirror (Lt (Mul (by, bz))) = Lt (Mul (by, bz))
  | mirror (Le (C co)) = Le (C co)
  | mirror (Le (Bound cp)) = Le (Bound cp)
  | mirror (Le (Neg ct)) = Le (Neg ct)
  | mirror (Le (Add (cu, cv))) = Le (Add (cu, cv))
  | mirror (Le (Sub (cw, cx))) = Le (Sub (cw, cx))
  | mirror (Le (Mul (cy, cz))) = Le (Mul (cy, cz))
  | mirror (Gt (C doa)) = Gt (C doa)
  | mirror (Gt (Bound dp)) = Gt (Bound dp)
  | mirror (Gt (Neg dt)) = Gt (Neg dt)
  | mirror (Gt (Add (du, dv))) = Gt (Add (du, dv))
  | mirror (Gt (Sub (dw, dx))) = Gt (Sub (dw, dx))
  | mirror (Gt (Mul (dy, dz))) = Gt (Mul (dy, dz))
  | mirror (Ge (C eo)) = Ge (C eo)
  | mirror (Ge (Bound ep)) = Ge (Bound ep)
  | mirror (Ge (Neg et)) = Ge (Neg et)
  | mirror (Ge (Add (eu, ev))) = Ge (Add (eu, ev))
  | mirror (Ge (Sub (ew, ex))) = Ge (Sub (ew, ex))
  | mirror (Ge (Mul (ey, ez))) = Ge (Mul (ey, ez))
  | mirror (Eq (C fo)) = Eq (C fo)
  | mirror (Eq (Bound fp)) = Eq (Bound fp)
  | mirror (Eq (Neg ft)) = Eq (Neg ft)
  | mirror (Eq (Add (fu, fv))) = Eq (Add (fu, fv))
  | mirror (Eq (Sub (fw, fx))) = Eq (Sub (fw, fx))
  | mirror (Eq (Mul (fy, fz))) = Eq (Mul (fy, fz))
  | mirror (NEq (C go)) = NEq (C go)
  | mirror (NEq (Bound gp)) = NEq (Bound gp)
  | mirror (NEq (Neg gt)) = NEq (Neg gt)
  | mirror (NEq (Add (gu, gv))) = NEq (Add (gu, gv))
  | mirror (NEq (Sub (gw, gx))) = NEq (Sub (gw, gx))
  | mirror (NEq (Mul (gy, gz))) = NEq (Mul (gy, gz))
  | mirror (Dvd (aa, C ho)) = Dvd (aa, C ho)
  | mirror (Dvd (aa, Bound hp)) = Dvd (aa, Bound hp)
  | mirror (Dvd (aa, Neg ht)) = Dvd (aa, Neg ht)
  | mirror (Dvd (aa, Add (hu, hv))) = Dvd (aa, Add (hu, hv))
  | mirror (Dvd (aa, Sub (hw, hx))) = Dvd (aa, Sub (hw, hx))
  | mirror (Dvd (aa, Mul (hy, hz))) = Dvd (aa, Mul (hy, hz))
  | mirror (NDvd (ac, C io)) = NDvd (ac, C io)
  | mirror (NDvd (ac, Bound ip)) = NDvd (ac, Bound ip)
  | mirror (NDvd (ac, Neg it)) = NDvd (ac, Neg it)
  | mirror (NDvd (ac, Add (iu, iv))) = NDvd (ac, Add (iu, iv))
  | mirror (NDvd (ac, Sub (iw, ix))) = NDvd (ac, Sub (iw, ix))
  | mirror (NDvd (ac, Mul (iy, iz))) = NDvd (ac, Mul (iy, iz))
  | mirror (NOT ae) = NOT ae
  | mirror (Imp (aj, ak)) = Imp (aj, ak)
  | mirror (Iff (al, am)) = Iff (al, am)
  | mirror (E an) = E an
  | mirror (A ao) = A ao
  | mirror (Closed ap) = Closed ap
  | mirror (NClosed aq) = NClosed aq
  | mirror (Lt (CN (cm, c, e))) =
    (if equal_nat cm zero_nat then Gt (CN (zero_nat, c, Neg e))
      else Lt (CN (suc (minus_nat cm one_nat), c, e)))
  | mirror (Le (CN (dm, c, e))) =
    (if equal_nat dm zero_nat then Ge (CN (zero_nat, c, Neg e))
      else Le (CN (suc (minus_nat dm one_nat), c, e)))
  | mirror (Gt (CN (em, c, e))) =
    (if equal_nat em zero_nat then Lt (CN (zero_nat, c, Neg e))
      else Gt (CN (suc (minus_nat em one_nat), c, e)))
  | mirror (Ge (CN (fm, c, e))) =
    (if equal_nat fm zero_nat then Le (CN (zero_nat, c, Neg e))
      else Ge (CN (suc (minus_nat fm one_nat), c, e)))
  | mirror (Eq (CN (gm, c, e))) =
    (if equal_nat gm zero_nat then Eq (CN (zero_nat, c, Neg e))
      else Eq (CN (suc (minus_nat gm one_nat), c, e)))
  | mirror (NEq (CN (hm, c, e))) =
    (if equal_nat hm zero_nat then NEq (CN (zero_nat, c, Neg e))
      else NEq (CN (suc (minus_nat hm one_nat), c, e)))
  | mirror (Dvd (i, CN (im, c, e))) =
    (if equal_nat im zero_nat then Dvd (i, CN (zero_nat, c, Neg e))
      else Dvd (i, CN (suc (minus_nat im one_nat), c, e)))
  | mirror (NDvd (i, CN (jm, c, e))) =
    (if equal_nat jm zero_nat then NDvd (i, CN (zero_nat, c, Neg e))
      else NDvd (i, CN (suc (minus_nat jm one_nat), c, e)));

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun zsplit0 (C c) = (zero_inta, C c)
  | zsplit0 (Bound n) =
    (if equal_nat n zero_nat then (Int_of_integer (1 : IntInf.int), C zero_inta)
      else (zero_inta, Bound n))
  | zsplit0 (CN (n, i, a)) =
    let
      val aa = zsplit0 a;
      val (ia, ab) = aa;
    in
      (if equal_nat n zero_nat then (plus_inta i ia, ab)
        else (ia, CN (n, i, ab)))
    end
  | zsplit0 (Neg a) =
    let
      val aa = zsplit0 a;
      val (i, ab) = aa;
    in
      (uminus_int i, Neg ab)
    end
  | zsplit0 (Add (a, b)) =
    let
      val aa = zsplit0 a;
      val (ia, ab) = aa;
      val ba = zsplit0 b;
      val (ib, bb) = ba;
    in
      (plus_inta ia ib, Add (ab, bb))
    end
  | zsplit0 (Sub (a, b)) =
    let
      val aa = zsplit0 a;
      val (ia, ab) = aa;
      val ba = zsplit0 b;
      val (ib, bb) = ba;
    in
      (minus_inta ia ib, Sub (ab, bb))
    end
  | zsplit0 (Mul (i, a)) =
    let
      val aa = zsplit0 a;
      val (ia, ab) = aa;
    in
      (times_inta i ia, Mul (i, ab))
    end;

fun zlfm (And (p, q)) = And (zlfm p, zlfm q)
  | zlfm (Or (p, q)) = Or (zlfm p, zlfm q)
  | zlfm (Imp (p, q)) = Or (zlfm (NOT p), zlfm q)
  | zlfm (Iff (p, q)) =
    Or (And (zlfm p, zlfm q), And (zlfm (NOT p), zlfm (NOT q)))
  | zlfm (Lt a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if equal_inta c zero_inta then Lt r
        else (if less_int zero_inta c then Lt (CN (zero_nat, c, r))
               else Gt (CN (zero_nat, uminus_int c, Neg r))))
    end
  | zlfm (Le a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if equal_inta c zero_inta then Le r
        else (if less_int zero_inta c then Le (CN (zero_nat, c, r))
               else Ge (CN (zero_nat, uminus_int c, Neg r))))
    end
  | zlfm (Gt a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if equal_inta c zero_inta then Gt r
        else (if less_int zero_inta c then Gt (CN (zero_nat, c, r))
               else Lt (CN (zero_nat, uminus_int c, Neg r))))
    end
  | zlfm (Ge a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if equal_inta c zero_inta then Ge r
        else (if less_int zero_inta c then Ge (CN (zero_nat, c, r))
               else Le (CN (zero_nat, uminus_int c, Neg r))))
    end
  | zlfm (Eq a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if equal_inta c zero_inta then Eq r
        else (if less_int zero_inta c then Eq (CN (zero_nat, c, r))
               else Eq (CN (zero_nat, uminus_int c, Neg r))))
    end
  | zlfm (NEq a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if equal_inta c zero_inta then NEq r
        else (if less_int zero_inta c then NEq (CN (zero_nat, c, r))
               else NEq (CN (zero_nat, uminus_int c, Neg r))))
    end
  | zlfm (Dvd (i, a)) =
    (if equal_inta i zero_inta then zlfm (Eq a)
      else let
             val (c, r) = zsplit0 a;
           in
             (if equal_inta c zero_inta then Dvd (abs_int i, r)
               else (if less_int zero_inta c
                      then Dvd (abs_int i, CN (zero_nat, c, r))
                      else Dvd (abs_int i, CN (zero_nat, uminus_int c, Neg r))))
           end)
  | zlfm (NDvd (i, a)) =
    (if equal_inta i zero_inta then zlfm (NEq a)
      else let
             val (c, r) = zsplit0 a;
           in
             (if equal_inta c zero_inta then NDvd (abs_int i, r)
               else (if less_int zero_inta c
                      then NDvd (abs_int i, CN (zero_nat, c, r))
                      else NDvd (abs_int i,
                                  CN (zero_nat, uminus_int c, Neg r))))
           end)
  | zlfm (NOT (And (p, q))) = Or (zlfm (NOT p), zlfm (NOT q))
  | zlfm (NOT (Or (p, q))) = And (zlfm (NOT p), zlfm (NOT q))
  | zlfm (NOT (Imp (p, q))) = And (zlfm p, zlfm (NOT q))
  | zlfm (NOT (Iff (p, q))) =
    Or (And (zlfm p, zlfm (NOT q)), And (zlfm (NOT p), zlfm q))
  | zlfm (NOT (NOT p)) = zlfm p
  | zlfm (NOT T) = F
  | zlfm (NOT F) = T
  | zlfm (NOT (Lt a)) = zlfm (Ge a)
  | zlfm (NOT (Le a)) = zlfm (Gt a)
  | zlfm (NOT (Gt a)) = zlfm (Le a)
  | zlfm (NOT (Ge a)) = zlfm (Lt a)
  | zlfm (NOT (Eq a)) = zlfm (NEq a)
  | zlfm (NOT (NEq a)) = zlfm (Eq a)
  | zlfm (NOT (Dvd (i, a))) = zlfm (NDvd (i, a))
  | zlfm (NOT (NDvd (i, a))) = zlfm (Dvd (i, a))
  | zlfm (NOT (Closed p)) = NClosed p
  | zlfm (NOT (NClosed p)) = Closed p
  | zlfm T = T
  | zlfm F = F
  | zlfm (NOT (E ci)) = NOT (E ci)
  | zlfm (NOT (A cj)) = NOT (A cj)
  | zlfm (E ao) = E ao
  | zlfm (A ap) = A ap
  | zlfm (Closed aq) = Closed aq
  | zlfm (NClosed ar) = NClosed ar;

fun unita p =
  let
    val pa = zlfm p;
    val l = zeta pa;
    val q =
      And (Dvd (l, CN (zero_nat, Int_of_integer (1 : IntInf.int), C zero_inta)),
            a_beta pa l);
    val d = delta q;
    val b = remdups equal_num (map simpnum (beta q));
    val a = remdups equal_num (map simpnum (alpha q));
  in
    (if less_eq_nat (size_list b) (size_list a) then (q, (b, d))
      else (mirror q, (a, d)))
  end;

fun decrnum (Bound n) = Bound (minus_nat n one_nat)
  | decrnum (Neg a) = Neg (decrnum a)
  | decrnum (Add (a, b)) = Add (decrnum a, decrnum b)
  | decrnum (Sub (a, b)) = Sub (decrnum a, decrnum b)
  | decrnum (Mul (c, a)) = Mul (c, decrnum a)
  | decrnum (CN (n, i, a)) = CN (minus_nat n one_nat, i, decrnum a)
  | decrnum (C v) = C v;

fun decr (Lt a) = Lt (decrnum a)
  | decr (Le a) = Le (decrnum a)
  | decr (Gt a) = Gt (decrnum a)
  | decr (Ge a) = Ge (decrnum a)
  | decr (Eq a) = Eq (decrnum a)
  | decr (NEq a) = NEq (decrnum a)
  | decr (Dvd (i, a)) = Dvd (i, decrnum a)
  | decr (NDvd (i, a)) = NDvd (i, decrnum a)
  | decr (NOT p) = NOT (decr p)
  | decr (And (p, q)) = And (decr p, decr q)
  | decr (Or (p, q)) = Or (decr p, decr q)
  | decr (Imp (p, q)) = Imp (decr p, decr q)
  | decr (Iff (p, q)) = Iff (decr p, decr q)
  | decr T = T
  | decr F = F
  | decr (E v) = E v
  | decr (A v) = A v
  | decr (Closed v) = Closed v
  | decr (NClosed v) = NClosed v;

fun upto_aux i j js =
  (if less_int j i then js
    else upto_aux i (minus_inta j (Int_of_integer (1 : IntInf.int))) (j :: js));

fun uptoa i j = upto_aux i j [];

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun cooper p =
  let
    val (q, (b, d)) = unita p;
    val js = uptoa (Int_of_integer (1 : IntInf.int)) d;
    val mq = simpfm (minusinf q);
    val md = evaldjf (fn j => simpfm (subst0 (C j) mq)) js;
  in
    (if equal_fm md T then T
      else let
             val qd =
               evaldjf (fn (ba, j) => simpfm (subst0 (Add (ba, C j)) q))
                 (maps (fn ba => map (fn a => (ba, a)) js) b);
           in
             decr (disj md qd)
           end)
  end;

fun qelim (E p) = (fn qe => dj qe (qelim p qe))
  | qelim (A p) = (fn qe => nota (qe (qelim (NOT p) qe)))
  | qelim (NOT p) = (fn qe => nota (qelim p qe))
  | qelim (And (p, q)) = (fn qe => conj (qelim p qe) (qelim q qe))
  | qelim (Or (p, q)) = (fn qe => disj (qelim p qe) (qelim q qe))
  | qelim (Imp (p, q)) = (fn qe => imp (qelim p qe) (qelim q qe))
  | qelim (Iff (p, q)) = (fn qe => iff (qelim p qe) (qelim q qe))
  | qelim T = (fn _ => simpfm T)
  | qelim F = (fn _ => simpfm F)
  | qelim (Lt v) = (fn _ => simpfm (Lt v))
  | qelim (Le v) = (fn _ => simpfm (Le v))
  | qelim (Gt v) = (fn _ => simpfm (Gt v))
  | qelim (Ge v) = (fn _ => simpfm (Ge v))
  | qelim (Eq v) = (fn _ => simpfm (Eq v))
  | qelim (NEq v) = (fn _ => simpfm (NEq v))
  | qelim (Dvd (v, va)) = (fn _ => simpfm (Dvd (v, va)))
  | qelim (NDvd (v, va)) = (fn _ => simpfm (NDvd (v, va)))
  | qelim (Closed v) = (fn _ => simpfm (Closed v))
  | qelim (NClosed v) = (fn _ => simpfm (NClosed v));

fun prep (E T) = T
  | prep (E F) = F
  | prep (E (Or (p, q))) = Or (prep (E p), prep (E q))
  | prep (E (Imp (p, q))) = Or (prep (E (NOT p)), prep (E q))
  | prep (E (Iff (p, q))) =
    Or (prep (E (And (p, q))), prep (E (And (NOT p, NOT q))))
  | prep (E (NOT (And (p, q)))) = Or (prep (E (NOT p)), prep (E (NOT q)))
  | prep (E (NOT (Imp (p, q)))) = prep (E (And (p, NOT q)))
  | prep (E (NOT (Iff (p, q)))) =
    Or (prep (E (And (p, NOT q))), prep (E (And (NOT p, q))))
  | prep (E (Lt ef)) = E (prep (Lt ef))
  | prep (E (Le eg)) = E (prep (Le eg))
  | prep (E (Gt eh)) = E (prep (Gt eh))
  | prep (E (Ge ei)) = E (prep (Ge ei))
  | prep (E (Eq ej)) = E (prep (Eq ej))
  | prep (E (NEq ek)) = E (prep (NEq ek))
  | prep (E (Dvd (el, em))) = E (prep (Dvd (el, em)))
  | prep (E (NDvd (en, eo))) = E (prep (NDvd (en, eo)))
  | prep (E (NOT T)) = E (prep (NOT T))
  | prep (E (NOT F)) = E (prep (NOT F))
  | prep (E (NOT (Lt gw))) = E (prep (NOT (Lt gw)))
  | prep (E (NOT (Le gx))) = E (prep (NOT (Le gx)))
  | prep (E (NOT (Gt gy))) = E (prep (NOT (Gt gy)))
  | prep (E (NOT (Ge gz))) = E (prep (NOT (Ge gz)))
  | prep (E (NOT (Eq ha))) = E (prep (NOT (Eq ha)))
  | prep (E (NOT (NEq hb))) = E (prep (NOT (NEq hb)))
  | prep (E (NOT (Dvd (hc, hd)))) = E (prep (NOT (Dvd (hc, hd))))
  | prep (E (NOT (NDvd (he, hf)))) = E (prep (NOT (NDvd (he, hf))))
  | prep (E (NOT (NOT hg))) = E (prep (NOT (NOT hg)))
  | prep (E (NOT (Or (hj, hk)))) = E (prep (NOT (Or (hj, hk))))
  | prep (E (NOT (E hp))) = E (prep (NOT (E hp)))
  | prep (E (NOT (A hq))) = E (prep (NOT (A hq)))
  | prep (E (NOT (Closed hr))) = E (prep (NOT (Closed hr)))
  | prep (E (NOT (NClosed hs))) = E (prep (NOT (NClosed hs)))
  | prep (E (And (eq, er))) = E (prep (And (eq, er)))
  | prep (E (E ey)) = E (prep (E ey))
  | prep (E (A ez)) = E (prep (A ez))
  | prep (E (Closed fa)) = E (prep (Closed fa))
  | prep (E (NClosed fb)) = E (prep (NClosed fb))
  | prep (A (And (p, q))) = And (prep (A p), prep (A q))
  | prep (A T) = prep (NOT (E (NOT T)))
  | prep (A F) = prep (NOT (E (NOT F)))
  | prep (A (Lt jn)) = prep (NOT (E (NOT (Lt jn))))
  | prep (A (Le jo)) = prep (NOT (E (NOT (Le jo))))
  | prep (A (Gt jp)) = prep (NOT (E (NOT (Gt jp))))
  | prep (A (Ge jq)) = prep (NOT (E (NOT (Ge jq))))
  | prep (A (Eq jr)) = prep (NOT (E (NOT (Eq jr))))
  | prep (A (NEq js)) = prep (NOT (E (NOT (NEq js))))
  | prep (A (Dvd (jt, ju))) = prep (NOT (E (NOT (Dvd (jt, ju)))))
  | prep (A (NDvd (jv, jw))) = prep (NOT (E (NOT (NDvd (jv, jw)))))
  | prep (A (NOT jx)) = prep (NOT (E (NOT (NOT jx))))
  | prep (A (Or (ka, kb))) = prep (NOT (E (NOT (Or (ka, kb)))))
  | prep (A (Imp (kc, kd))) = prep (NOT (E (NOT (Imp (kc, kd)))))
  | prep (A (Iff (ke, kf))) = prep (NOT (E (NOT (Iff (ke, kf)))))
  | prep (A (E kg)) = prep (NOT (E (NOT (E kg))))
  | prep (A (A kh)) = prep (NOT (E (NOT (A kh))))
  | prep (A (Closed ki)) = prep (NOT (E (NOT (Closed ki))))
  | prep (A (NClosed kj)) = prep (NOT (E (NOT (NClosed kj))))
  | prep (NOT (NOT p)) = prep p
  | prep (NOT (And (p, q))) = Or (prep (NOT p), prep (NOT q))
  | prep (NOT (A p)) = prep (E (NOT p))
  | prep (NOT (Or (p, q))) = And (prep (NOT p), prep (NOT q))
  | prep (NOT (Imp (p, q))) = And (prep p, prep (NOT q))
  | prep (NOT (Iff (p, q))) = Or (prep (And (p, NOT q)), prep (And (NOT p, q)))
  | prep (NOT T) = NOT (prep T)
  | prep (NOT F) = NOT (prep F)
  | prep (NOT (Lt bo)) = NOT (prep (Lt bo))
  | prep (NOT (Le bp)) = NOT (prep (Le bp))
  | prep (NOT (Gt bq)) = NOT (prep (Gt bq))
  | prep (NOT (Ge br)) = NOT (prep (Ge br))
  | prep (NOT (Eq bs)) = NOT (prep (Eq bs))
  | prep (NOT (NEq bt)) = NOT (prep (NEq bt))
  | prep (NOT (Dvd (bu, bv))) = NOT (prep (Dvd (bu, bv)))
  | prep (NOT (NDvd (bw, bx))) = NOT (prep (NDvd (bw, bx)))
  | prep (NOT (E ch)) = NOT (prep (E ch))
  | prep (NOT (Closed cj)) = NOT (prep (Closed cj))
  | prep (NOT (NClosed ck)) = NOT (prep (NClosed ck))
  | prep (Or (p, q)) = Or (prep p, prep q)
  | prep (And (p, q)) = And (prep p, prep q)
  | prep (Imp (p, q)) = prep (Or (NOT p, q))
  | prep (Iff (p, q)) = Or (prep (And (p, q)), prep (And (NOT p, NOT q)))
  | prep T = T
  | prep F = F
  | prep (Lt u) = Lt u
  | prep (Le v) = Le v
  | prep (Gt w) = Gt w
  | prep (Ge x) = Ge x
  | prep (Eq y) = Eq y
  | prep (NEq z) = NEq z
  | prep (Dvd (aa, ab)) = Dvd (aa, ab)
  | prep (NDvd (ac, ad)) = NDvd (ac, ad)
  | prep (Closed ap) = Closed ap
  | prep (NClosed aq) = NClosed aq;

fun pa p = qelim (prep p) cooper;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

end; (*struct Cooper_Procedure*)
