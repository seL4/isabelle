structure Cooper_Procedure : sig
  datatype inta = Int_of_integer of int
  val integer_of_int : inta -> int
  type nat
  val integer_of_nat : nat -> int
  datatype numa = C of inta | Bound of nat | CN of nat * inta * numa |
    Neg of numa | Add of numa * numa | Sub of numa * numa | Mul of inta * numa
  datatype fm = T | F | Lt of numa | Le of numa | Gt of numa | Ge of numa |
    Eq of numa | NEq of numa | Dvd of inta * numa | NDvd of inta * numa |
    Not of fm | And of fm * fm | Or of fm * fm | Imp of fm * fm | Iff of fm * fm
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

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if k = (0 : IntInf.int) then ((0 : IntInf.int), (0 : IntInf.int))
    else (if (0 : IntInf.int) < l
           then (if (0 : IntInf.int) < k then Integer.div_mod (abs k) (abs l)
                  else let
                         val (r, s) = Integer.div_mod (abs k) (abs l);
                       in
                         (if s = (0 : IntInf.int) then (~ r, (0 : IntInf.int))
                           else (~ r - (1 : IntInf.int), l - s))
                       end)
           else (if l = (0 : IntInf.int) then ((0 : IntInf.int), k)
                  else apsnd (fn a => ~ a)
                         (if k < (0 : IntInf.int)
                           then Integer.div_mod (abs k) (abs l)
                           else let
                                  val (r, s) = Integer.div_mod (abs k) (abs l);
                                in
                                  (if s = (0 : IntInf.int)
                                    then (~ r, (0 : IntInf.int))
                                    else (~ r - (1 : IntInf.int), ~ l - s))
                                end))));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_inta k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

val divide_int = {divide = divide_inta} : inta divide;

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_inta k l =
  Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

type 'a modulo =
  {divide_modulo : 'a divide, dvd_modulo : 'a dvd, modulo : 'a -> 'a -> 'a};
val divide_modulo = #divide_modulo : 'a modulo -> 'a divide;
val dvd_modulo = #dvd_modulo : 'a modulo -> 'a dvd;
val modulo = #modulo : 'a modulo -> 'a -> 'a -> 'a;

val modulo_int =
  {divide_modulo = divide_int, dvd_modulo = dvd_int, modulo = modulo_inta} :
  inta modulo;

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
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

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
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int}
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

val semiring_no_zero_divisors_cancel_int =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_int}
  : inta semiring_no_zero_divisors_cancel;

val semidom_divide_int =
  {divide_semidom_divide = divide_int, semidom_semidom_divide = semidom_int,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_int}
  : inta semidom_divide;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};
val semidom_divide_algebraic_semidom = #semidom_divide_algebraic_semidom :
  'a algebraic_semidom -> 'a semidom_divide;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel,
    modulo_semiring_modulo : 'a modulo};
val comm_semiring_1_cancel_semiring_modulo =
  #comm_semiring_1_cancel_semiring_modulo :
  'a semiring_modulo -> 'a comm_semiring_1_cancel;
val modulo_semiring_modulo = #modulo_semiring_modulo :
  'a semiring_modulo -> 'a modulo;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom,
    semiring_modulo_semidom_modulo : 'a semiring_modulo};
val algebraic_semidom_semidom_modulo = #algebraic_semidom_semidom_modulo :
  'a semidom_modulo -> 'a algebraic_semidom;
val semiring_modulo_semidom_modulo = #semiring_modulo_semidom_modulo :
  'a semidom_modulo -> 'a semiring_modulo;

val algebraic_semidom_int =
  {semidom_divide_algebraic_semidom = semidom_divide_int} :
  inta algebraic_semidom;

val semiring_modulo_int =
  {comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_int,
    modulo_semiring_modulo = modulo_int}
  : inta semiring_modulo;

val semidom_modulo_int =
  {algebraic_semidom_semidom_modulo = algebraic_semidom_int,
    semiring_modulo_semidom_modulo = semiring_modulo_int}
  : inta semidom_modulo;

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
  Not of fm | And of fm * fm | Or of fm * fm | Imp of fm * fm | Iff of fm * fm |
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
  | disjuncts (Not v) = [Not v]
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
  | equal_fm (Not x11) (NClosed x19) = false
  | equal_fm (NClosed x19) (Not x11) = false
  | equal_fm (Not x11) (Closed x18) = false
  | equal_fm (Closed x18) (Not x11) = false
  | equal_fm (Not x11) (A x17) = false
  | equal_fm (A x17) (Not x11) = false
  | equal_fm (Not x11) (E x16) = false
  | equal_fm (E x16) (Not x11) = false
  | equal_fm (Not x11) (Iff (x151, x152)) = false
  | equal_fm (Iff (x151, x152)) (Not x11) = false
  | equal_fm (Not x11) (Imp (x141, x142)) = false
  | equal_fm (Imp (x141, x142)) (Not x11) = false
  | equal_fm (Not x11) (Or (x131, x132)) = false
  | equal_fm (Or (x131, x132)) (Not x11) = false
  | equal_fm (Not x11) (And (x121, x122)) = false
  | equal_fm (And (x121, x122)) (Not x11) = false
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
  | equal_fm (NDvd (x101, x102)) (Not x11) = false
  | equal_fm (Not x11) (NDvd (x101, x102)) = false
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
  | equal_fm (Dvd (x91, x92)) (Not x11) = false
  | equal_fm (Not x11) (Dvd (x91, x92)) = false
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
  | equal_fm (NEq x8) (Not x11) = false
  | equal_fm (Not x11) (NEq x8) = false
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
  | equal_fm (Eq x7) (Not x11) = false
  | equal_fm (Not x11) (Eq x7) = false
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
  | equal_fm (Ge x6) (Not x11) = false
  | equal_fm (Not x11) (Ge x6) = false
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
  | equal_fm (Gt x5) (Not x11) = false
  | equal_fm (Not x11) (Gt x5) = false
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
  | equal_fm (Le x4) (Not x11) = false
  | equal_fm (Not x11) (Le x4) = false
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
  | equal_fm (Lt x3) (Not x11) = false
  | equal_fm (Not x11) (Lt x3) = false
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
  | equal_fm F (Not x11) = false
  | equal_fm (Not x11) F = false
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
  | equal_fm T (Not x11) = false
  | equal_fm (Not x11) T = false
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
  | equal_fm (Not x11) (Not y11) = equal_fm x11 y11
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
                  | NDvd (_, _) => Or (f p, q) | Not _ => Or (f p, q)
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
  | minusinf (Lt (C va)) = Lt (C va)
  | minusinf (Lt (Bound va)) = Lt (Bound va)
  | minusinf (Lt (Neg va)) = Lt (Neg va)
  | minusinf (Lt (Add (va, vb))) = Lt (Add (va, vb))
  | minusinf (Lt (Sub (va, vb))) = Lt (Sub (va, vb))
  | minusinf (Lt (Mul (va, vb))) = Lt (Mul (va, vb))
  | minusinf (Le (C va)) = Le (C va)
  | minusinf (Le (Bound va)) = Le (Bound va)
  | minusinf (Le (Neg va)) = Le (Neg va)
  | minusinf (Le (Add (va, vb))) = Le (Add (va, vb))
  | minusinf (Le (Sub (va, vb))) = Le (Sub (va, vb))
  | minusinf (Le (Mul (va, vb))) = Le (Mul (va, vb))
  | minusinf (Gt (C va)) = Gt (C va)
  | minusinf (Gt (Bound va)) = Gt (Bound va)
  | minusinf (Gt (Neg va)) = Gt (Neg va)
  | minusinf (Gt (Add (va, vb))) = Gt (Add (va, vb))
  | minusinf (Gt (Sub (va, vb))) = Gt (Sub (va, vb))
  | minusinf (Gt (Mul (va, vb))) = Gt (Mul (va, vb))
  | minusinf (Ge (C va)) = Ge (C va)
  | minusinf (Ge (Bound va)) = Ge (Bound va)
  | minusinf (Ge (Neg va)) = Ge (Neg va)
  | minusinf (Ge (Add (va, vb))) = Ge (Add (va, vb))
  | minusinf (Ge (Sub (va, vb))) = Ge (Sub (va, vb))
  | minusinf (Ge (Mul (va, vb))) = Ge (Mul (va, vb))
  | minusinf (Eq (C va)) = Eq (C va)
  | minusinf (Eq (Bound va)) = Eq (Bound va)
  | minusinf (Eq (Neg va)) = Eq (Neg va)
  | minusinf (Eq (Add (va, vb))) = Eq (Add (va, vb))
  | minusinf (Eq (Sub (va, vb))) = Eq (Sub (va, vb))
  | minusinf (Eq (Mul (va, vb))) = Eq (Mul (va, vb))
  | minusinf (NEq (C va)) = NEq (C va)
  | minusinf (NEq (Bound va)) = NEq (Bound va)
  | minusinf (NEq (Neg va)) = NEq (Neg va)
  | minusinf (NEq (Add (va, vb))) = NEq (Add (va, vb))
  | minusinf (NEq (Sub (va, vb))) = NEq (Sub (va, vb))
  | minusinf (NEq (Mul (va, vb))) = NEq (Mul (va, vb))
  | minusinf (Dvd (v, va)) = Dvd (v, va)
  | minusinf (NDvd (v, va)) = NDvd (v, va)
  | minusinf (Not v) = Not v
  | minusinf (Imp (v, va)) = Imp (v, va)
  | minusinf (Iff (v, va)) = Iff (v, va)
  | minusinf (E v) = E v
  | minusinf (A v) = A v
  | minusinf (Closed v) = Closed v
  | minusinf (NClosed v) = NClosed v
  | minusinf (Lt (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then T
      else Lt (CN (suc (minus_nat vd one_nat), c, e)))
  | minusinf (Le (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then T
      else Le (CN (suc (minus_nat vd one_nat), c, e)))
  | minusinf (Gt (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then F
      else Gt (CN (suc (minus_nat vd one_nat), c, e)))
  | minusinf (Ge (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then F
      else Ge (CN (suc (minus_nat vd one_nat), c, e)))
  | minusinf (Eq (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then F
      else Eq (CN (suc (minus_nat vd one_nat), c, e)))
  | minusinf (NEq (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then T
      else NEq (CN (suc (minus_nat vd one_nat), c, e)));

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
  | subst0 t (Not p) = Not (subst0 t p)
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
  eq A1_
    (modulo ((modulo_semiring_modulo o semiring_modulo_semidom_modulo) A2_) b a)
    (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semidom o semidom_semidom_divide o
             semidom_divide_algebraic_semidom o
             algebraic_semidom_semidom_modulo)
            A2_));

fun nummul i (C j) = C (times_inta i j)
  | nummul i (CN (n, c, t)) = CN (n, times_inta c i, nummul i t)
  | nummul i (Bound v) = Mul (i, Bound v)
  | nummul i (Neg v) = Mul (i, Neg v)
  | nummul i (Add (v, va)) = Mul (i, Add (v, va))
  | nummul i (Sub (v, va)) = Mul (i, Sub (v, va))
  | nummul i (Mul (v, va)) = Mul (i, Mul (v, va));

fun numneg t = nummul (uminus_int one_inta) t;

fun less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

fun numadd (CN (n1, c1, r1)) (CN (n2, c2, r2)) =
  (if equal_nat n1 n2
    then let
           val c = plus_inta c1 c2;
         in
           (if equal_inta c zero_inta then numadd r1 r2
             else CN (n1, c, numadd r1 r2))
         end
    else (if less_eq_nat n1 n2
           then CN (n1, c1, numadd r1 (Add (Mul (c2, Bound n2), r2)))
           else CN (n2, c2, numadd (Add (Mul (c1, Bound n1), r1)) r2)))
  | numadd (CN (n1, c1, r1)) (C v) = CN (n1, c1, numadd r1 (C v))
  | numadd (CN (n1, c1, r1)) (Bound v) = CN (n1, c1, numadd r1 (Bound v))
  | numadd (CN (n1, c1, r1)) (Neg v) = CN (n1, c1, numadd r1 (Neg v))
  | numadd (CN (n1, c1, r1)) (Add (v, va)) =
    CN (n1, c1, numadd r1 (Add (v, va)))
  | numadd (CN (n1, c1, r1)) (Sub (v, va)) =
    CN (n1, c1, numadd r1 (Sub (v, va)))
  | numadd (CN (n1, c1, r1)) (Mul (v, va)) =
    CN (n1, c1, numadd r1 (Mul (v, va)))
  | numadd (C v) (CN (n2, c2, r2)) = CN (n2, c2, numadd (C v) r2)
  | numadd (Bound v) (CN (n2, c2, r2)) = CN (n2, c2, numadd (Bound v) r2)
  | numadd (Neg v) (CN (n2, c2, r2)) = CN (n2, c2, numadd (Neg v) r2)
  | numadd (Add (v, va)) (CN (n2, c2, r2)) =
    CN (n2, c2, numadd (Add (v, va)) r2)
  | numadd (Sub (v, va)) (CN (n2, c2, r2)) =
    CN (n2, c2, numadd (Sub (v, va)) r2)
  | numadd (Mul (v, va)) (CN (n2, c2, r2)) =
    CN (n2, c2, numadd (Mul (v, va)) r2)
  | numadd (C b1) (C b2) = C (plus_inta b1 b2)
  | numadd (C v) (Bound va) = Add (C v, Bound va)
  | numadd (C v) (Neg va) = Add (C v, Neg va)
  | numadd (C v) (Add (va, vb)) = Add (C v, Add (va, vb))
  | numadd (C v) (Sub (va, vb)) = Add (C v, Sub (va, vb))
  | numadd (C v) (Mul (va, vb)) = Add (C v, Mul (va, vb))
  | numadd (Bound v) (C va) = Add (Bound v, C va)
  | numadd (Bound v) (Bound va) = Add (Bound v, Bound va)
  | numadd (Bound v) (Neg va) = Add (Bound v, Neg va)
  | numadd (Bound v) (Add (va, vb)) = Add (Bound v, Add (va, vb))
  | numadd (Bound v) (Sub (va, vb)) = Add (Bound v, Sub (va, vb))
  | numadd (Bound v) (Mul (va, vb)) = Add (Bound v, Mul (va, vb))
  | numadd (Neg v) (C va) = Add (Neg v, C va)
  | numadd (Neg v) (Bound va) = Add (Neg v, Bound va)
  | numadd (Neg v) (Neg va) = Add (Neg v, Neg va)
  | numadd (Neg v) (Add (va, vb)) = Add (Neg v, Add (va, vb))
  | numadd (Neg v) (Sub (va, vb)) = Add (Neg v, Sub (va, vb))
  | numadd (Neg v) (Mul (va, vb)) = Add (Neg v, Mul (va, vb))
  | numadd (Add (v, va)) (C vb) = Add (Add (v, va), C vb)
  | numadd (Add (v, va)) (Bound vb) = Add (Add (v, va), Bound vb)
  | numadd (Add (v, va)) (Neg vb) = Add (Add (v, va), Neg vb)
  | numadd (Add (v, va)) (Add (vb, vc)) = Add (Add (v, va), Add (vb, vc))
  | numadd (Add (v, va)) (Sub (vb, vc)) = Add (Add (v, va), Sub (vb, vc))
  | numadd (Add (v, va)) (Mul (vb, vc)) = Add (Add (v, va), Mul (vb, vc))
  | numadd (Sub (v, va)) (C vb) = Add (Sub (v, va), C vb)
  | numadd (Sub (v, va)) (Bound vb) = Add (Sub (v, va), Bound vb)
  | numadd (Sub (v, va)) (Neg vb) = Add (Sub (v, va), Neg vb)
  | numadd (Sub (v, va)) (Add (vb, vc)) = Add (Sub (v, va), Add (vb, vc))
  | numadd (Sub (v, va)) (Sub (vb, vc)) = Add (Sub (v, va), Sub (vb, vc))
  | numadd (Sub (v, va)) (Mul (vb, vc)) = Add (Sub (v, va), Mul (vb, vc))
  | numadd (Mul (v, va)) (C vb) = Add (Mul (v, va), C vb)
  | numadd (Mul (v, va)) (Bound vb) = Add (Mul (v, va), Bound vb)
  | numadd (Mul (v, va)) (Neg vb) = Add (Mul (v, va), Neg vb)
  | numadd (Mul (v, va)) (Add (vb, vc)) = Add (Mul (v, va), Add (vb, vc))
  | numadd (Mul (v, va)) (Sub (vb, vc)) = Add (Mul (v, va), Sub (vb, vc))
  | numadd (Mul (v, va)) (Mul (vb, vc)) = Add (Mul (v, va), Mul (vb, vc));

fun numsub s t = (if equal_numa s t then C zero_inta else numadd s (numneg t));

fun simpnum (C j) = C j
  | simpnum (Bound n) = CN (n, one_inta, C zero_inta)
  | simpnum (Neg t) = numneg (simpnum t)
  | simpnum (Add (t, s)) = numadd (simpnum t) (simpnum s)
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

fun nota (Not p) = p
  | nota T = F
  | nota F = T
  | nota (Lt v) = Not (Lt v)
  | nota (Le v) = Not (Le v)
  | nota (Gt v) = Not (Gt v)
  | nota (Ge v) = Not (Ge v)
  | nota (Eq v) = Not (Eq v)
  | nota (NEq v) = Not (NEq v)
  | nota (Dvd (v, va)) = Not (Dvd (v, va))
  | nota (NDvd (v, va)) = Not (NDvd (v, va))
  | nota (And (v, va)) = Not (And (v, va))
  | nota (Or (v, va)) = Not (Or (v, va))
  | nota (Imp (v, va)) = Not (Imp (v, va))
  | nota (Iff (v, va)) = Not (Iff (v, va))
  | nota (E v) = Not (E v)
  | nota (A v) = Not (A v)
  | nota (Closed v) = Not (Closed v)
  | nota (NClosed v) = Not (NClosed v);

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
  | simpfm (Not p) = nota (simpfm p)
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
      else (if equal_inta (abs_int i) one_inta then T
             else let
                    val aa = simpnum a;
                  in
                    (case aa
                      of C v =>
                        (if dvd (equal_int, semidom_modulo_int) i v then T
                          else F)
                      | Bound _ => Dvd (i, aa) | CN (_, _, _) => Dvd (i, aa)
                      | Neg _ => Dvd (i, aa) | Add (_, _) => Dvd (i, aa)
                      | Sub (_, _) => Dvd (i, aa) | Mul (_, _) => Dvd (i, aa))
                  end))
  | simpfm (NDvd (i, a)) =
    (if equal_inta i zero_inta then simpfm (NEq a)
      else (if equal_inta (abs_int i) one_inta then F
             else let
                    val aa = simpnum a;
                  in
                    (case aa
                      of C v =>
                        (if not (dvd (equal_int, semidom_modulo_int) i v) then T
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

fun a_beta (And (p, q)) k = And (a_beta p k, a_beta q k)
  | a_beta (Or (p, q)) k = Or (a_beta p k, a_beta q k)
  | a_beta T k = T
  | a_beta F k = F
  | a_beta (Lt (C va)) k = Lt (C va)
  | a_beta (Lt (Bound va)) k = Lt (Bound va)
  | a_beta (Lt (Neg va)) k = Lt (Neg va)
  | a_beta (Lt (Add (va, vb))) k = Lt (Add (va, vb))
  | a_beta (Lt (Sub (va, vb))) k = Lt (Sub (va, vb))
  | a_beta (Lt (Mul (va, vb))) k = Lt (Mul (va, vb))
  | a_beta (Le (C va)) k = Le (C va)
  | a_beta (Le (Bound va)) k = Le (Bound va)
  | a_beta (Le (Neg va)) k = Le (Neg va)
  | a_beta (Le (Add (va, vb))) k = Le (Add (va, vb))
  | a_beta (Le (Sub (va, vb))) k = Le (Sub (va, vb))
  | a_beta (Le (Mul (va, vb))) k = Le (Mul (va, vb))
  | a_beta (Gt (C va)) k = Gt (C va)
  | a_beta (Gt (Bound va)) k = Gt (Bound va)
  | a_beta (Gt (Neg va)) k = Gt (Neg va)
  | a_beta (Gt (Add (va, vb))) k = Gt (Add (va, vb))
  | a_beta (Gt (Sub (va, vb))) k = Gt (Sub (va, vb))
  | a_beta (Gt (Mul (va, vb))) k = Gt (Mul (va, vb))
  | a_beta (Ge (C va)) k = Ge (C va)
  | a_beta (Ge (Bound va)) k = Ge (Bound va)
  | a_beta (Ge (Neg va)) k = Ge (Neg va)
  | a_beta (Ge (Add (va, vb))) k = Ge (Add (va, vb))
  | a_beta (Ge (Sub (va, vb))) k = Ge (Sub (va, vb))
  | a_beta (Ge (Mul (va, vb))) k = Ge (Mul (va, vb))
  | a_beta (Eq (C va)) k = Eq (C va)
  | a_beta (Eq (Bound va)) k = Eq (Bound va)
  | a_beta (Eq (Neg va)) k = Eq (Neg va)
  | a_beta (Eq (Add (va, vb))) k = Eq (Add (va, vb))
  | a_beta (Eq (Sub (va, vb))) k = Eq (Sub (va, vb))
  | a_beta (Eq (Mul (va, vb))) k = Eq (Mul (va, vb))
  | a_beta (NEq (C va)) k = NEq (C va)
  | a_beta (NEq (Bound va)) k = NEq (Bound va)
  | a_beta (NEq (Neg va)) k = NEq (Neg va)
  | a_beta (NEq (Add (va, vb))) k = NEq (Add (va, vb))
  | a_beta (NEq (Sub (va, vb))) k = NEq (Sub (va, vb))
  | a_beta (NEq (Mul (va, vb))) k = NEq (Mul (va, vb))
  | a_beta (Dvd (v, C vb)) k = Dvd (v, C vb)
  | a_beta (Dvd (v, Bound vb)) k = Dvd (v, Bound vb)
  | a_beta (Dvd (v, Neg vb)) k = Dvd (v, Neg vb)
  | a_beta (Dvd (v, Add (vb, vc))) k = Dvd (v, Add (vb, vc))
  | a_beta (Dvd (v, Sub (vb, vc))) k = Dvd (v, Sub (vb, vc))
  | a_beta (Dvd (v, Mul (vb, vc))) k = Dvd (v, Mul (vb, vc))
  | a_beta (NDvd (v, C vb)) k = NDvd (v, C vb)
  | a_beta (NDvd (v, Bound vb)) k = NDvd (v, Bound vb)
  | a_beta (NDvd (v, Neg vb)) k = NDvd (v, Neg vb)
  | a_beta (NDvd (v, Add (vb, vc))) k = NDvd (v, Add (vb, vc))
  | a_beta (NDvd (v, Sub (vb, vc))) k = NDvd (v, Sub (vb, vc))
  | a_beta (NDvd (v, Mul (vb, vc))) k = NDvd (v, Mul (vb, vc))
  | a_beta (Not v) k = Not v
  | a_beta (Imp (v, va)) k = Imp (v, va)
  | a_beta (Iff (v, va)) k = Iff (v, va)
  | a_beta (E v) k = E v
  | a_beta (A v) k = A v
  | a_beta (Closed v) k = Closed v
  | a_beta (NClosed v) k = NClosed v
  | a_beta (Lt (CN (vd, c, e))) k =
    (if equal_nat vd zero_nat
      then Lt (CN (zero_nat, one_inta, Mul (divide_inta k c, e)))
      else Lt (CN (suc (minus_nat vd one_nat), c, e)))
  | a_beta (Le (CN (vd, c, e))) k =
    (if equal_nat vd zero_nat
      then Le (CN (zero_nat, one_inta, Mul (divide_inta k c, e)))
      else Le (CN (suc (minus_nat vd one_nat), c, e)))
  | a_beta (Gt (CN (vd, c, e))) k =
    (if equal_nat vd zero_nat
      then Gt (CN (zero_nat, one_inta, Mul (divide_inta k c, e)))
      else Gt (CN (suc (minus_nat vd one_nat), c, e)))
  | a_beta (Ge (CN (vd, c, e))) k =
    (if equal_nat vd zero_nat
      then Ge (CN (zero_nat, one_inta, Mul (divide_inta k c, e)))
      else Ge (CN (suc (minus_nat vd one_nat), c, e)))
  | a_beta (Eq (CN (vd, c, e))) k =
    (if equal_nat vd zero_nat
      then Eq (CN (zero_nat, one_inta, Mul (divide_inta k c, e)))
      else Eq (CN (suc (minus_nat vd one_nat), c, e)))
  | a_beta (NEq (CN (vd, c, e))) k =
    (if equal_nat vd zero_nat
      then NEq (CN (zero_nat, one_inta, Mul (divide_inta k c, e)))
      else NEq (CN (suc (minus_nat vd one_nat), c, e)))
  | a_beta (Dvd (i, CN (ve, c, e))) k =
    (if equal_nat ve zero_nat
      then Dvd (times_inta (divide_inta k c) i,
                 CN (zero_nat, one_inta, Mul (divide_inta k c, e)))
      else Dvd (i, CN (suc (minus_nat ve one_nat), c, e)))
  | a_beta (NDvd (i, CN (ve, c, e))) k =
    (if equal_nat ve zero_nat
      then NDvd (times_inta (divide_inta k c) i,
                  CN (zero_nat, one_inta, Mul (divide_inta k c, e)))
      else NDvd (i, CN (suc (minus_nat ve one_nat), c, e)));

fun gcd_integer k l =
  abs (if l = (0 : IntInf.int) then k
        else gcd_integer l (modulo_integer (abs k) (abs l)));

fun lcm_integer a b = divide_integer (abs a * abs b) (gcd_integer a b);

fun lcm_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (lcm_integer x y);

fun delta (And (p, q)) = lcm_int (delta p) (delta q)
  | delta (Or (p, q)) = lcm_int (delta p) (delta q)
  | delta T = one_inta
  | delta F = one_inta
  | delta (Lt v) = one_inta
  | delta (Le v) = one_inta
  | delta (Gt v) = one_inta
  | delta (Ge v) = one_inta
  | delta (Eq v) = one_inta
  | delta (NEq v) = one_inta
  | delta (Dvd (v, C vb)) = one_inta
  | delta (Dvd (v, Bound vb)) = one_inta
  | delta (Dvd (v, Neg vb)) = one_inta
  | delta (Dvd (v, Add (vb, vc))) = one_inta
  | delta (Dvd (v, Sub (vb, vc))) = one_inta
  | delta (Dvd (v, Mul (vb, vc))) = one_inta
  | delta (NDvd (v, C vb)) = one_inta
  | delta (NDvd (v, Bound vb)) = one_inta
  | delta (NDvd (v, Neg vb)) = one_inta
  | delta (NDvd (v, Add (vb, vc))) = one_inta
  | delta (NDvd (v, Sub (vb, vc))) = one_inta
  | delta (NDvd (v, Mul (vb, vc))) = one_inta
  | delta (Not v) = one_inta
  | delta (Imp (v, va)) = one_inta
  | delta (Iff (v, va)) = one_inta
  | delta (E v) = one_inta
  | delta (A v) = one_inta
  | delta (Closed v) = one_inta
  | delta (NClosed v) = one_inta
  | delta (Dvd (i, CN (ve, c, e))) =
    (if equal_nat ve zero_nat then i else one_inta)
  | delta (NDvd (i, CN (ve, c, e))) =
    (if equal_nat ve zero_nat then i else one_inta);

fun alpha (And (p, q)) = alpha p @ alpha q
  | alpha (Or (p, q)) = alpha p @ alpha q
  | alpha T = []
  | alpha F = []
  | alpha (Lt (C va)) = []
  | alpha (Lt (Bound va)) = []
  | alpha (Lt (Neg va)) = []
  | alpha (Lt (Add (va, vb))) = []
  | alpha (Lt (Sub (va, vb))) = []
  | alpha (Lt (Mul (va, vb))) = []
  | alpha (Le (C va)) = []
  | alpha (Le (Bound va)) = []
  | alpha (Le (Neg va)) = []
  | alpha (Le (Add (va, vb))) = []
  | alpha (Le (Sub (va, vb))) = []
  | alpha (Le (Mul (va, vb))) = []
  | alpha (Gt (C va)) = []
  | alpha (Gt (Bound va)) = []
  | alpha (Gt (Neg va)) = []
  | alpha (Gt (Add (va, vb))) = []
  | alpha (Gt (Sub (va, vb))) = []
  | alpha (Gt (Mul (va, vb))) = []
  | alpha (Ge (C va)) = []
  | alpha (Ge (Bound va)) = []
  | alpha (Ge (Neg va)) = []
  | alpha (Ge (Add (va, vb))) = []
  | alpha (Ge (Sub (va, vb))) = []
  | alpha (Ge (Mul (va, vb))) = []
  | alpha (Eq (C va)) = []
  | alpha (Eq (Bound va)) = []
  | alpha (Eq (Neg va)) = []
  | alpha (Eq (Add (va, vb))) = []
  | alpha (Eq (Sub (va, vb))) = []
  | alpha (Eq (Mul (va, vb))) = []
  | alpha (NEq (C va)) = []
  | alpha (NEq (Bound va)) = []
  | alpha (NEq (Neg va)) = []
  | alpha (NEq (Add (va, vb))) = []
  | alpha (NEq (Sub (va, vb))) = []
  | alpha (NEq (Mul (va, vb))) = []
  | alpha (Dvd (v, va)) = []
  | alpha (NDvd (v, va)) = []
  | alpha (Not v) = []
  | alpha (Imp (v, va)) = []
  | alpha (Iff (v, va)) = []
  | alpha (E v) = []
  | alpha (A v) = []
  | alpha (Closed v) = []
  | alpha (NClosed v) = []
  | alpha (Lt (CN (vd, c, e))) = (if equal_nat vd zero_nat then [e] else [])
  | alpha (Le (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then [Add (C (uminus_int one_inta), e)] else [])
  | alpha (Gt (CN (vd, c, e))) = (if equal_nat vd zero_nat then [] else [])
  | alpha (Ge (CN (vd, c, e))) = (if equal_nat vd zero_nat then [] else [])
  | alpha (Eq (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then [Add (C (uminus_int one_inta), e)] else [])
  | alpha (NEq (CN (vd, c, e))) = (if equal_nat vd zero_nat then [e] else []);

fun zeta (And (p, q)) = lcm_int (zeta p) (zeta q)
  | zeta (Or (p, q)) = lcm_int (zeta p) (zeta q)
  | zeta T = one_inta
  | zeta F = one_inta
  | zeta (Lt (C va)) = one_inta
  | zeta (Lt (Bound va)) = one_inta
  | zeta (Lt (Neg va)) = one_inta
  | zeta (Lt (Add (va, vb))) = one_inta
  | zeta (Lt (Sub (va, vb))) = one_inta
  | zeta (Lt (Mul (va, vb))) = one_inta
  | zeta (Le (C va)) = one_inta
  | zeta (Le (Bound va)) = one_inta
  | zeta (Le (Neg va)) = one_inta
  | zeta (Le (Add (va, vb))) = one_inta
  | zeta (Le (Sub (va, vb))) = one_inta
  | zeta (Le (Mul (va, vb))) = one_inta
  | zeta (Gt (C va)) = one_inta
  | zeta (Gt (Bound va)) = one_inta
  | zeta (Gt (Neg va)) = one_inta
  | zeta (Gt (Add (va, vb))) = one_inta
  | zeta (Gt (Sub (va, vb))) = one_inta
  | zeta (Gt (Mul (va, vb))) = one_inta
  | zeta (Ge (C va)) = one_inta
  | zeta (Ge (Bound va)) = one_inta
  | zeta (Ge (Neg va)) = one_inta
  | zeta (Ge (Add (va, vb))) = one_inta
  | zeta (Ge (Sub (va, vb))) = one_inta
  | zeta (Ge (Mul (va, vb))) = one_inta
  | zeta (Eq (C va)) = one_inta
  | zeta (Eq (Bound va)) = one_inta
  | zeta (Eq (Neg va)) = one_inta
  | zeta (Eq (Add (va, vb))) = one_inta
  | zeta (Eq (Sub (va, vb))) = one_inta
  | zeta (Eq (Mul (va, vb))) = one_inta
  | zeta (NEq (C va)) = one_inta
  | zeta (NEq (Bound va)) = one_inta
  | zeta (NEq (Neg va)) = one_inta
  | zeta (NEq (Add (va, vb))) = one_inta
  | zeta (NEq (Sub (va, vb))) = one_inta
  | zeta (NEq (Mul (va, vb))) = one_inta
  | zeta (Dvd (v, C vb)) = one_inta
  | zeta (Dvd (v, Bound vb)) = one_inta
  | zeta (Dvd (v, Neg vb)) = one_inta
  | zeta (Dvd (v, Add (vb, vc))) = one_inta
  | zeta (Dvd (v, Sub (vb, vc))) = one_inta
  | zeta (Dvd (v, Mul (vb, vc))) = one_inta
  | zeta (NDvd (v, C vb)) = one_inta
  | zeta (NDvd (v, Bound vb)) = one_inta
  | zeta (NDvd (v, Neg vb)) = one_inta
  | zeta (NDvd (v, Add (vb, vc))) = one_inta
  | zeta (NDvd (v, Sub (vb, vc))) = one_inta
  | zeta (NDvd (v, Mul (vb, vc))) = one_inta
  | zeta (Not v) = one_inta
  | zeta (Imp (v, va)) = one_inta
  | zeta (Iff (v, va)) = one_inta
  | zeta (E v) = one_inta
  | zeta (A v) = one_inta
  | zeta (Closed v) = one_inta
  | zeta (NClosed v) = one_inta
  | zeta (Lt (CN (vd, c, e))) = (if equal_nat vd zero_nat then c else one_inta)
  | zeta (Le (CN (vd, c, e))) = (if equal_nat vd zero_nat then c else one_inta)
  | zeta (Gt (CN (vd, c, e))) = (if equal_nat vd zero_nat then c else one_inta)
  | zeta (Ge (CN (vd, c, e))) = (if equal_nat vd zero_nat then c else one_inta)
  | zeta (Eq (CN (vd, c, e))) = (if equal_nat vd zero_nat then c else one_inta)
  | zeta (NEq (CN (vd, c, e))) = (if equal_nat vd zero_nat then c else one_inta)
  | zeta (Dvd (i, CN (ve, c, e))) =
    (if equal_nat ve zero_nat then c else one_inta)
  | zeta (NDvd (i, CN (ve, c, e))) =
    (if equal_nat ve zero_nat then c else one_inta);

fun beta (And (p, q)) = beta p @ beta q
  | beta (Or (p, q)) = beta p @ beta q
  | beta T = []
  | beta F = []
  | beta (Lt (C va)) = []
  | beta (Lt (Bound va)) = []
  | beta (Lt (Neg va)) = []
  | beta (Lt (Add (va, vb))) = []
  | beta (Lt (Sub (va, vb))) = []
  | beta (Lt (Mul (va, vb))) = []
  | beta (Le (C va)) = []
  | beta (Le (Bound va)) = []
  | beta (Le (Neg va)) = []
  | beta (Le (Add (va, vb))) = []
  | beta (Le (Sub (va, vb))) = []
  | beta (Le (Mul (va, vb))) = []
  | beta (Gt (C va)) = []
  | beta (Gt (Bound va)) = []
  | beta (Gt (Neg va)) = []
  | beta (Gt (Add (va, vb))) = []
  | beta (Gt (Sub (va, vb))) = []
  | beta (Gt (Mul (va, vb))) = []
  | beta (Ge (C va)) = []
  | beta (Ge (Bound va)) = []
  | beta (Ge (Neg va)) = []
  | beta (Ge (Add (va, vb))) = []
  | beta (Ge (Sub (va, vb))) = []
  | beta (Ge (Mul (va, vb))) = []
  | beta (Eq (C va)) = []
  | beta (Eq (Bound va)) = []
  | beta (Eq (Neg va)) = []
  | beta (Eq (Add (va, vb))) = []
  | beta (Eq (Sub (va, vb))) = []
  | beta (Eq (Mul (va, vb))) = []
  | beta (NEq (C va)) = []
  | beta (NEq (Bound va)) = []
  | beta (NEq (Neg va)) = []
  | beta (NEq (Add (va, vb))) = []
  | beta (NEq (Sub (va, vb))) = []
  | beta (NEq (Mul (va, vb))) = []
  | beta (Dvd (v, va)) = []
  | beta (NDvd (v, va)) = []
  | beta (Not v) = []
  | beta (Imp (v, va)) = []
  | beta (Iff (v, va)) = []
  | beta (E v) = []
  | beta (A v) = []
  | beta (Closed v) = []
  | beta (NClosed v) = []
  | beta (Lt (CN (vd, c, e))) = (if equal_nat vd zero_nat then [] else [])
  | beta (Le (CN (vd, c, e))) = (if equal_nat vd zero_nat then [] else [])
  | beta (Gt (CN (vd, c, e))) = (if equal_nat vd zero_nat then [Neg e] else [])
  | beta (Ge (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then [Sub (C (uminus_int one_inta), e)] else [])
  | beta (Eq (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then [Sub (C (uminus_int one_inta), e)] else [])
  | beta (NEq (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then [Neg e] else []);

fun mirror (And (p, q)) = And (mirror p, mirror q)
  | mirror (Or (p, q)) = Or (mirror p, mirror q)
  | mirror T = T
  | mirror F = F
  | mirror (Lt (C va)) = Lt (C va)
  | mirror (Lt (Bound va)) = Lt (Bound va)
  | mirror (Lt (Neg va)) = Lt (Neg va)
  | mirror (Lt (Add (va, vb))) = Lt (Add (va, vb))
  | mirror (Lt (Sub (va, vb))) = Lt (Sub (va, vb))
  | mirror (Lt (Mul (va, vb))) = Lt (Mul (va, vb))
  | mirror (Le (C va)) = Le (C va)
  | mirror (Le (Bound va)) = Le (Bound va)
  | mirror (Le (Neg va)) = Le (Neg va)
  | mirror (Le (Add (va, vb))) = Le (Add (va, vb))
  | mirror (Le (Sub (va, vb))) = Le (Sub (va, vb))
  | mirror (Le (Mul (va, vb))) = Le (Mul (va, vb))
  | mirror (Gt (C va)) = Gt (C va)
  | mirror (Gt (Bound va)) = Gt (Bound va)
  | mirror (Gt (Neg va)) = Gt (Neg va)
  | mirror (Gt (Add (va, vb))) = Gt (Add (va, vb))
  | mirror (Gt (Sub (va, vb))) = Gt (Sub (va, vb))
  | mirror (Gt (Mul (va, vb))) = Gt (Mul (va, vb))
  | mirror (Ge (C va)) = Ge (C va)
  | mirror (Ge (Bound va)) = Ge (Bound va)
  | mirror (Ge (Neg va)) = Ge (Neg va)
  | mirror (Ge (Add (va, vb))) = Ge (Add (va, vb))
  | mirror (Ge (Sub (va, vb))) = Ge (Sub (va, vb))
  | mirror (Ge (Mul (va, vb))) = Ge (Mul (va, vb))
  | mirror (Eq (C va)) = Eq (C va)
  | mirror (Eq (Bound va)) = Eq (Bound va)
  | mirror (Eq (Neg va)) = Eq (Neg va)
  | mirror (Eq (Add (va, vb))) = Eq (Add (va, vb))
  | mirror (Eq (Sub (va, vb))) = Eq (Sub (va, vb))
  | mirror (Eq (Mul (va, vb))) = Eq (Mul (va, vb))
  | mirror (NEq (C va)) = NEq (C va)
  | mirror (NEq (Bound va)) = NEq (Bound va)
  | mirror (NEq (Neg va)) = NEq (Neg va)
  | mirror (NEq (Add (va, vb))) = NEq (Add (va, vb))
  | mirror (NEq (Sub (va, vb))) = NEq (Sub (va, vb))
  | mirror (NEq (Mul (va, vb))) = NEq (Mul (va, vb))
  | mirror (Dvd (v, C vb)) = Dvd (v, C vb)
  | mirror (Dvd (v, Bound vb)) = Dvd (v, Bound vb)
  | mirror (Dvd (v, Neg vb)) = Dvd (v, Neg vb)
  | mirror (Dvd (v, Add (vb, vc))) = Dvd (v, Add (vb, vc))
  | mirror (Dvd (v, Sub (vb, vc))) = Dvd (v, Sub (vb, vc))
  | mirror (Dvd (v, Mul (vb, vc))) = Dvd (v, Mul (vb, vc))
  | mirror (NDvd (v, C vb)) = NDvd (v, C vb)
  | mirror (NDvd (v, Bound vb)) = NDvd (v, Bound vb)
  | mirror (NDvd (v, Neg vb)) = NDvd (v, Neg vb)
  | mirror (NDvd (v, Add (vb, vc))) = NDvd (v, Add (vb, vc))
  | mirror (NDvd (v, Sub (vb, vc))) = NDvd (v, Sub (vb, vc))
  | mirror (NDvd (v, Mul (vb, vc))) = NDvd (v, Mul (vb, vc))
  | mirror (Not v) = Not v
  | mirror (Imp (v, va)) = Imp (v, va)
  | mirror (Iff (v, va)) = Iff (v, va)
  | mirror (E v) = E v
  | mirror (A v) = A v
  | mirror (Closed v) = Closed v
  | mirror (NClosed v) = NClosed v
  | mirror (Lt (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then Gt (CN (zero_nat, c, Neg e))
      else Lt (CN (suc (minus_nat vd one_nat), c, e)))
  | mirror (Le (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then Ge (CN (zero_nat, c, Neg e))
      else Le (CN (suc (minus_nat vd one_nat), c, e)))
  | mirror (Gt (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then Lt (CN (zero_nat, c, Neg e))
      else Gt (CN (suc (minus_nat vd one_nat), c, e)))
  | mirror (Ge (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then Le (CN (zero_nat, c, Neg e))
      else Ge (CN (suc (minus_nat vd one_nat), c, e)))
  | mirror (Eq (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then Eq (CN (zero_nat, c, Neg e))
      else Eq (CN (suc (minus_nat vd one_nat), c, e)))
  | mirror (NEq (CN (vd, c, e))) =
    (if equal_nat vd zero_nat then NEq (CN (zero_nat, c, Neg e))
      else NEq (CN (suc (minus_nat vd one_nat), c, e)))
  | mirror (Dvd (i, CN (ve, c, e))) =
    (if equal_nat ve zero_nat then Dvd (i, CN (zero_nat, c, Neg e))
      else Dvd (i, CN (suc (minus_nat ve one_nat), c, e)))
  | mirror (NDvd (i, CN (ve, c, e))) =
    (if equal_nat ve zero_nat then NDvd (i, CN (zero_nat, c, Neg e))
      else NDvd (i, CN (suc (minus_nat ve one_nat), c, e)));

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun zsplit0 (C c) = (zero_inta, C c)
  | zsplit0 (Bound n) =
    (if equal_nat n zero_nat then (one_inta, C zero_inta)
      else (zero_inta, Bound n))
  | zsplit0 (CN (n, i, a)) =
    let
      val aa = zsplit0 a;
      val (ia, ab) = aa;
    in
      (if equal_nat n zero_nat then (plus_inta i ia, ab)
        else (ia, CN (n, i, ab)))
    end
  | zsplit0 (Neg a) = let
                        val aa = zsplit0 a;
                        val (i, ab) = aa;
                      in
                        (uminus_int i, Neg ab)
                      end
  | zsplit0 (Add (a, b)) = let
                             val aa = zsplit0 a;
                             val (ia, ab) = aa;
                             val ba = zsplit0 b;
                             val (ib, bb) = ba;
                           in
                             (plus_inta ia ib, Add (ab, bb))
                           end
  | zsplit0 (Sub (a, b)) = let
                             val aa = zsplit0 a;
                             val (ia, ab) = aa;
                             val ba = zsplit0 b;
                             val (ib, bb) = ba;
                           in
                             (minus_inta ia ib, Sub (ab, bb))
                           end
  | zsplit0 (Mul (i, a)) = let
                             val aa = zsplit0 a;
                             val (ia, ab) = aa;
                           in
                             (times_inta i ia, Mul (i, ab))
                           end;

fun zlfm (And (p, q)) = And (zlfm p, zlfm q)
  | zlfm (Or (p, q)) = Or (zlfm p, zlfm q)
  | zlfm (Imp (p, q)) = Or (zlfm (Not p), zlfm q)
  | zlfm (Iff (p, q)) =
    Or (And (zlfm p, zlfm q), And (zlfm (Not p), zlfm (Not q)))
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
  | zlfm (Not (And (p, q))) = Or (zlfm (Not p), zlfm (Not q))
  | zlfm (Not (Or (p, q))) = And (zlfm (Not p), zlfm (Not q))
  | zlfm (Not (Imp (p, q))) = And (zlfm p, zlfm (Not q))
  | zlfm (Not (Iff (p, q))) =
    Or (And (zlfm p, zlfm (Not q)), And (zlfm (Not p), zlfm q))
  | zlfm (Not (Not p)) = zlfm p
  | zlfm (Not T) = F
  | zlfm (Not F) = T
  | zlfm (Not (Lt a)) = zlfm (Ge a)
  | zlfm (Not (Le a)) = zlfm (Gt a)
  | zlfm (Not (Gt a)) = zlfm (Le a)
  | zlfm (Not (Ge a)) = zlfm (Lt a)
  | zlfm (Not (Eq a)) = zlfm (NEq a)
  | zlfm (Not (NEq a)) = zlfm (Eq a)
  | zlfm (Not (Dvd (i, a))) = zlfm (NDvd (i, a))
  | zlfm (Not (NDvd (i, a))) = zlfm (Dvd (i, a))
  | zlfm (Not (Closed p)) = NClosed p
  | zlfm (Not (NClosed p)) = Closed p
  | zlfm T = T
  | zlfm F = F
  | zlfm (Not (E va)) = Not (E va)
  | zlfm (Not (A va)) = Not (A va)
  | zlfm (E v) = E v
  | zlfm (A v) = A v
  | zlfm (Closed v) = Closed v
  | zlfm (NClosed v) = NClosed v;

fun unita p =
  let
    val pa = zlfm p;
    val l = zeta pa;
    val q = And (Dvd (l, CN (zero_nat, one_inta, C zero_inta)), a_beta pa l);
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
  | decr (Not p) = Not (decr p)
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
  (if less_int j i then js else upto_aux i (minus_inta j one_inta) (j :: js));

fun uptoa i j = upto_aux i j [];

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun cooper p =
  let
    val (q, (b, d)) = unita p;
    val js = uptoa one_inta d;
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
  | qelim (A p) = (fn qe => nota (qe (qelim (Not p) qe)))
  | qelim (Not p) = (fn qe => nota (qelim p qe))
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
  | prep (E (Imp (p, q))) = Or (prep (E (Not p)), prep (E q))
  | prep (E (Iff (p, q))) =
    Or (prep (E (And (p, q))), prep (E (And (Not p, Not q))))
  | prep (E (Not (And (p, q)))) = Or (prep (E (Not p)), prep (E (Not q)))
  | prep (E (Not (Imp (p, q)))) = prep (E (And (p, Not q)))
  | prep (E (Not (Iff (p, q)))) =
    Or (prep (E (And (p, Not q))), prep (E (And (Not p, q))))
  | prep (E (Lt v)) = E (prep (Lt v))
  | prep (E (Le v)) = E (prep (Le v))
  | prep (E (Gt v)) = E (prep (Gt v))
  | prep (E (Ge v)) = E (prep (Ge v))
  | prep (E (Eq v)) = E (prep (Eq v))
  | prep (E (NEq v)) = E (prep (NEq v))
  | prep (E (Dvd (v, va))) = E (prep (Dvd (v, va)))
  | prep (E (NDvd (v, va))) = E (prep (NDvd (v, va)))
  | prep (E (Not T)) = E (prep (Not T))
  | prep (E (Not F)) = E (prep (Not F))
  | prep (E (Not (Lt va))) = E (prep (Not (Lt va)))
  | prep (E (Not (Le va))) = E (prep (Not (Le va)))
  | prep (E (Not (Gt va))) = E (prep (Not (Gt va)))
  | prep (E (Not (Ge va))) = E (prep (Not (Ge va)))
  | prep (E (Not (Eq va))) = E (prep (Not (Eq va)))
  | prep (E (Not (NEq va))) = E (prep (Not (NEq va)))
  | prep (E (Not (Dvd (va, vb)))) = E (prep (Not (Dvd (va, vb))))
  | prep (E (Not (NDvd (va, vb)))) = E (prep (Not (NDvd (va, vb))))
  | prep (E (Not (Not va))) = E (prep (Not (Not va)))
  | prep (E (Not (Or (va, vb)))) = E (prep (Not (Or (va, vb))))
  | prep (E (Not (E va))) = E (prep (Not (E va)))
  | prep (E (Not (A va))) = E (prep (Not (A va)))
  | prep (E (Not (Closed va))) = E (prep (Not (Closed va)))
  | prep (E (Not (NClosed va))) = E (prep (Not (NClosed va)))
  | prep (E (And (v, va))) = E (prep (And (v, va)))
  | prep (E (E v)) = E (prep (E v))
  | prep (E (A v)) = E (prep (A v))
  | prep (E (Closed v)) = E (prep (Closed v))
  | prep (E (NClosed v)) = E (prep (NClosed v))
  | prep (A (And (p, q))) = And (prep (A p), prep (A q))
  | prep (A T) = prep (Not (E (Not T)))
  | prep (A F) = prep (Not (E (Not F)))
  | prep (A (Lt v)) = prep (Not (E (Not (Lt v))))
  | prep (A (Le v)) = prep (Not (E (Not (Le v))))
  | prep (A (Gt v)) = prep (Not (E (Not (Gt v))))
  | prep (A (Ge v)) = prep (Not (E (Not (Ge v))))
  | prep (A (Eq v)) = prep (Not (E (Not (Eq v))))
  | prep (A (NEq v)) = prep (Not (E (Not (NEq v))))
  | prep (A (Dvd (v, va))) = prep (Not (E (Not (Dvd (v, va)))))
  | prep (A (NDvd (v, va))) = prep (Not (E (Not (NDvd (v, va)))))
  | prep (A (Not v)) = prep (Not (E (Not (Not v))))
  | prep (A (Or (v, va))) = prep (Not (E (Not (Or (v, va)))))
  | prep (A (Imp (v, va))) = prep (Not (E (Not (Imp (v, va)))))
  | prep (A (Iff (v, va))) = prep (Not (E (Not (Iff (v, va)))))
  | prep (A (E v)) = prep (Not (E (Not (E v))))
  | prep (A (A v)) = prep (Not (E (Not (A v))))
  | prep (A (Closed v)) = prep (Not (E (Not (Closed v))))
  | prep (A (NClosed v)) = prep (Not (E (Not (NClosed v))))
  | prep (Not (Not p)) = prep p
  | prep (Not (And (p, q))) = Or (prep (Not p), prep (Not q))
  | prep (Not (A p)) = prep (E (Not p))
  | prep (Not (Or (p, q))) = And (prep (Not p), prep (Not q))
  | prep (Not (Imp (p, q))) = And (prep p, prep (Not q))
  | prep (Not (Iff (p, q))) = Or (prep (And (p, Not q)), prep (And (Not p, q)))
  | prep (Not T) = Not (prep T)
  | prep (Not F) = Not (prep F)
  | prep (Not (Lt v)) = Not (prep (Lt v))
  | prep (Not (Le v)) = Not (prep (Le v))
  | prep (Not (Gt v)) = Not (prep (Gt v))
  | prep (Not (Ge v)) = Not (prep (Ge v))
  | prep (Not (Eq v)) = Not (prep (Eq v))
  | prep (Not (NEq v)) = Not (prep (NEq v))
  | prep (Not (Dvd (v, va))) = Not (prep (Dvd (v, va)))
  | prep (Not (NDvd (v, va))) = Not (prep (NDvd (v, va)))
  | prep (Not (E v)) = Not (prep (E v))
  | prep (Not (Closed v)) = Not (prep (Closed v))
  | prep (Not (NClosed v)) = Not (prep (NClosed v))
  | prep (Or (p, q)) = Or (prep p, prep q)
  | prep (And (p, q)) = And (prep p, prep q)
  | prep (Imp (p, q)) = prep (Or (Not p, q))
  | prep (Iff (p, q)) = Or (prep (And (p, q)), prep (And (Not p, Not q)))
  | prep T = T
  | prep F = F
  | prep (Lt v) = Lt v
  | prep (Le v) = Le v
  | prep (Gt v) = Gt v
  | prep (Ge v) = Ge v
  | prep (Eq v) = Eq v
  | prep (NEq v) = NEq v
  | prep (Dvd (v, va)) = Dvd (v, va)
  | prep (NDvd (v, va)) = NDvd (v, va)
  | prep (Closed v) = Closed v
  | prep (NClosed v) = NClosed v;

fun pa p = qelim (prep p) cooper;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

end; (*struct Cooper_Procedure*)
