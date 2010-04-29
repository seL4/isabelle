(* Generated from Cooper.thy; DO NOT EDIT! *)

structure Generated_Cooper : sig
  type 'a eq
  val eq : 'a eq -> 'a -> 'a -> bool
  val eqa : 'a eq -> 'a -> 'a -> bool
  val leta : 'a -> ('a -> 'b) -> 'b
  val suc : IntInf.int -> IntInf.int
  datatype num = C of IntInf.int | Bound of IntInf.int |
    Cn of IntInf.int * IntInf.int * num | Neg of num | Add of num * num |
    Sub of num * num | Mul of IntInf.int * num
  datatype fm = T | F | Lt of num | Le of num | Gt of num | Ge of num |
    Eq of num | NEq of num | Dvd of IntInf.int * num | NDvd of IntInf.int * num
    | Not of fm | And of fm * fm | Or of fm * fm | Imp of fm * fm |
    Iff of fm * fm | E of fm | A of fm | Closed of IntInf.int |
    NClosed of IntInf.int
  val map : ('a -> 'b) -> 'a list -> 'b list
  val append : 'a list -> 'a list -> 'a list
  val disjuncts : fm -> fm list
  val fm_case :
    'a -> 'a -> (num -> 'a) ->
                  (num -> 'a) ->
                    (num -> 'a) ->
                      (num -> 'a) ->
                        (num -> 'a) ->
                          (num -> 'a) ->
                            (IntInf.int -> num -> 'a) ->
                              (IntInf.int -> num -> 'a) ->
                                (fm -> 'a) ->
                                  (fm -> fm -> 'a) ->
                                    (fm -> fm -> 'a) ->
                                      (fm -> fm -> 'a) ->
(fm -> fm -> 'a) ->
  (fm -> 'a) ->
    (fm -> 'a) -> (IntInf.int -> 'a) -> (IntInf.int -> 'a) -> fm -> 'a
  val eq_num : num -> num -> bool
  val eq_fm : fm -> fm -> bool
  val djf : ('a -> fm) -> 'a -> fm -> fm
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val evaldjf : ('a -> fm) -> 'a list -> fm
  val dj : (fm -> fm) -> fm -> fm
  val disj : fm -> fm -> fm
  val minus_nat : IntInf.int -> IntInf.int -> IntInf.int
  val decrnum : num -> num
  val decr : fm -> fm
  val concat_map : ('a -> 'b list) -> 'a list -> 'b list
  val numsubst0 : num -> num -> num
  val subst0 : num -> fm -> fm
  val minusinf : fm -> fm
  val eq_int : IntInf.int eq
  val zero_int : IntInf.int
  type 'a zero
  val zero : 'a zero -> 'a
  val zero_inta : IntInf.int zero
  type 'a times
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a no_zero_divisors
  val times_no_zero_divisors : 'a no_zero_divisors -> 'a times
  val zero_no_zero_divisors : 'a no_zero_divisors -> 'a zero
  val times_int : IntInf.int times
  val no_zero_divisors_int : IntInf.int no_zero_divisors
  type 'a one
  val one : 'a one -> 'a
  type 'a zero_neq_one
  val one_zero_neq_one : 'a zero_neq_one -> 'a one
  val zero_zero_neq_one : 'a zero_neq_one -> 'a zero
  type 'a semigroup_mult
  val times_semigroup_mult : 'a semigroup_mult -> 'a times
  type 'a plus
  val plus : 'a plus -> 'a -> 'a -> 'a
  type 'a semigroup_add
  val plus_semigroup_add : 'a semigroup_add -> 'a plus
  type 'a ab_semigroup_add
  val semigroup_add_ab_semigroup_add : 'a ab_semigroup_add -> 'a semigroup_add
  type 'a semiring
  val ab_semigroup_add_semiring : 'a semiring -> 'a ab_semigroup_add
  val semigroup_mult_semiring : 'a semiring -> 'a semigroup_mult
  type 'a mult_zero
  val times_mult_zero : 'a mult_zero -> 'a times
  val zero_mult_zero : 'a mult_zero -> 'a zero
  type 'a monoid_add
  val semigroup_add_monoid_add : 'a monoid_add -> 'a semigroup_add
  val zero_monoid_add : 'a monoid_add -> 'a zero
  type 'a comm_monoid_add
  val ab_semigroup_add_comm_monoid_add :
    'a comm_monoid_add -> 'a ab_semigroup_add
  val monoid_add_comm_monoid_add : 'a comm_monoid_add -> 'a monoid_add
  type 'a semiring_0
  val comm_monoid_add_semiring_0 : 'a semiring_0 -> 'a comm_monoid_add
  val mult_zero_semiring_0 : 'a semiring_0 -> 'a mult_zero
  val semiring_semiring_0 : 'a semiring_0 -> 'a semiring
  type 'a power
  val one_power : 'a power -> 'a one
  val times_power : 'a power -> 'a times
  type 'a monoid_mult
  val semigroup_mult_monoid_mult : 'a monoid_mult -> 'a semigroup_mult
  val power_monoid_mult : 'a monoid_mult -> 'a power
  type 'a semiring_1
  val monoid_mult_semiring_1 : 'a semiring_1 -> 'a monoid_mult
  val semiring_0_semiring_1 : 'a semiring_1 -> 'a semiring_0
  val zero_neq_one_semiring_1 : 'a semiring_1 -> 'a zero_neq_one
  type 'a cancel_semigroup_add
  val semigroup_add_cancel_semigroup_add :
    'a cancel_semigroup_add -> 'a semigroup_add
  type 'a cancel_ab_semigroup_add
  val ab_semigroup_add_cancel_ab_semigroup_add :
    'a cancel_ab_semigroup_add -> 'a ab_semigroup_add
  val cancel_semigroup_add_cancel_ab_semigroup_add :
    'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add
  type 'a cancel_comm_monoid_add
  val cancel_ab_semigroup_add_cancel_comm_monoid_add :
    'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add
  val comm_monoid_add_cancel_comm_monoid_add :
    'a cancel_comm_monoid_add -> 'a comm_monoid_add
  type 'a semiring_0_cancel
  val cancel_comm_monoid_add_semiring_0_cancel :
    'a semiring_0_cancel -> 'a cancel_comm_monoid_add
  val semiring_0_semiring_0_cancel : 'a semiring_0_cancel -> 'a semiring_0
  type 'a semiring_1_cancel
  val semiring_0_cancel_semiring_1_cancel :
    'a semiring_1_cancel -> 'a semiring_0_cancel
  val semiring_1_semiring_1_cancel : 'a semiring_1_cancel -> 'a semiring_1
  type 'a dvd
  val times_dvd : 'a dvd -> 'a times
  type 'a ab_semigroup_mult
  val semigroup_mult_ab_semigroup_mult :
    'a ab_semigroup_mult -> 'a semigroup_mult
  type 'a comm_semiring
  val ab_semigroup_mult_comm_semiring : 'a comm_semiring -> 'a ab_semigroup_mult
  val semiring_comm_semiring : 'a comm_semiring -> 'a semiring
  type 'a comm_semiring_0
  val comm_semiring_comm_semiring_0 : 'a comm_semiring_0 -> 'a comm_semiring
  val semiring_0_comm_semiring_0 : 'a comm_semiring_0 -> 'a semiring_0
  type 'a comm_monoid_mult
  val ab_semigroup_mult_comm_monoid_mult :
    'a comm_monoid_mult -> 'a ab_semigroup_mult
  val monoid_mult_comm_monoid_mult : 'a comm_monoid_mult -> 'a monoid_mult
  type 'a comm_semiring_1
  val comm_monoid_mult_comm_semiring_1 :
    'a comm_semiring_1 -> 'a comm_monoid_mult
  val comm_semiring_0_comm_semiring_1 : 'a comm_semiring_1 -> 'a comm_semiring_0
  val dvd_comm_semiring_1 : 'a comm_semiring_1 -> 'a dvd
  val semiring_1_comm_semiring_1 : 'a comm_semiring_1 -> 'a semiring_1
  type 'a comm_semiring_0_cancel
  val comm_semiring_0_comm_semiring_0_cancel :
    'a comm_semiring_0_cancel -> 'a comm_semiring_0
  val semiring_0_cancel_comm_semiring_0_cancel :
    'a comm_semiring_0_cancel -> 'a semiring_0_cancel
  type 'a comm_semiring_1_cancel
  val comm_semiring_0_cancel_comm_semiring_1_cancel :
    'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel
  val comm_semiring_1_comm_semiring_1_cancel :
    'a comm_semiring_1_cancel -> 'a comm_semiring_1
  val semiring_1_cancel_comm_semiring_1_cancel :
    'a comm_semiring_1_cancel -> 'a semiring_1_cancel
  type 'a diva
  val dvd_div : 'a diva -> 'a dvd
  val diva : 'a diva -> 'a -> 'a -> 'a
  val moda : 'a diva -> 'a -> 'a -> 'a
  type 'a semiring_div
  val div_semiring_div : 'a semiring_div -> 'a diva
  val comm_semiring_1_cancel_semiring_div :
    'a semiring_div -> 'a comm_semiring_1_cancel
  val no_zero_divisors_semiring_div : 'a semiring_div -> 'a no_zero_divisors
  val one_int : IntInf.int
  val one_inta : IntInf.int one
  val zero_neq_one_int : IntInf.int zero_neq_one
  val semigroup_mult_int : IntInf.int semigroup_mult
  val plus_int : IntInf.int plus
  val semigroup_add_int : IntInf.int semigroup_add
  val ab_semigroup_add_int : IntInf.int ab_semigroup_add
  val semiring_int : IntInf.int semiring
  val mult_zero_int : IntInf.int mult_zero
  val monoid_add_int : IntInf.int monoid_add
  val comm_monoid_add_int : IntInf.int comm_monoid_add
  val semiring_0_int : IntInf.int semiring_0
  val power_int : IntInf.int power
  val monoid_mult_int : IntInf.int monoid_mult
  val semiring_1_int : IntInf.int semiring_1
  val cancel_semigroup_add_int : IntInf.int cancel_semigroup_add
  val cancel_ab_semigroup_add_int : IntInf.int cancel_ab_semigroup_add
  val cancel_comm_monoid_add_int : IntInf.int cancel_comm_monoid_add
  val semiring_0_cancel_int : IntInf.int semiring_0_cancel
  val semiring_1_cancel_int : IntInf.int semiring_1_cancel
  val dvd_int : IntInf.int dvd
  val ab_semigroup_mult_int : IntInf.int ab_semigroup_mult
  val comm_semiring_int : IntInf.int comm_semiring
  val comm_semiring_0_int : IntInf.int comm_semiring_0
  val comm_monoid_mult_int : IntInf.int comm_monoid_mult
  val comm_semiring_1_int : IntInf.int comm_semiring_1
  val comm_semiring_0_cancel_int : IntInf.int comm_semiring_0_cancel
  val comm_semiring_1_cancel_int : IntInf.int comm_semiring_1_cancel
  val abs_int : IntInf.int -> IntInf.int
  val split : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val sgn_int : IntInf.int -> IntInf.int
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val divmod_int : IntInf.int -> IntInf.int -> IntInf.int * IntInf.int
  val snd : 'a * 'b -> 'b
  val mod_int : IntInf.int -> IntInf.int -> IntInf.int
  val fst : 'a * 'b -> 'a
  val div_int : IntInf.int -> IntInf.int -> IntInf.int
  val div_inta : IntInf.int diva
  val semiring_div_int : IntInf.int semiring_div
  val dvd : 'a semiring_div * 'a eq -> 'a -> 'a -> bool
  val num_case :
    (IntInf.int -> 'a) ->
      (IntInf.int -> 'a) ->
        (IntInf.int -> IntInf.int -> num -> 'a) ->
          (num -> 'a) ->
            (num -> num -> 'a) ->
              (num -> num -> 'a) -> (IntInf.int -> num -> 'a) -> num -> 'a
  val nummul : IntInf.int -> num -> num
  val numneg : num -> num
  val numadd : num * num -> num
  val numsub : num -> num -> num
  val simpnum : num -> num
  val nota : fm -> fm
  val iffa : fm -> fm -> fm
  val impa : fm -> fm -> fm
  val conj : fm -> fm -> fm
  val simpfm : fm -> fm
  val iupt : IntInf.int -> IntInf.int -> IntInf.int list
  val mirror : fm -> fm
  val size_list : 'a list -> IntInf.int
  val alpha : fm -> num list
  val beta : fm -> num list
  val eq_numa : num eq
  val member : 'a eq -> 'a -> 'a list -> bool
  val remdups : 'a eq -> 'a list -> 'a list
  val gcd_int : IntInf.int -> IntInf.int -> IntInf.int
  val lcm_int : IntInf.int -> IntInf.int -> IntInf.int
  val delta : fm -> IntInf.int
  val a_beta : fm -> IntInf.int -> fm
  val zeta : fm -> IntInf.int
  val zsplit0 : num -> IntInf.int * num
  val zlfm : fm -> fm
  val unita : fm -> fm * (num list * IntInf.int)
  val cooper : fm -> fm
  val prep : fm -> fm
  val qelim : fm -> (fm -> fm) -> fm
  val pa : fm -> fm
end = struct

type 'a eq = {eq : 'a -> 'a -> bool};
val eq = #eq : 'a eq -> 'a -> 'a -> bool;

fun eqa A_ a b = eq A_ a b;

fun leta s f = f s;

fun suc n = IntInf.+ (n, (1 : IntInf.int));

datatype num = C of IntInf.int | Bound of IntInf.int |
  Cn of IntInf.int * IntInf.int * num | Neg of num | Add of num * num |
  Sub of num * num | Mul of IntInf.int * num;

datatype fm = T | F | Lt of num | Le of num | Gt of num | Ge of num | Eq of num
  | NEq of num | Dvd of IntInf.int * num | NDvd of IntInf.int * num | Not of fm
  | And of fm * fm | Or of fm * fm | Imp of fm * fm | Iff of fm * fm | E of fm |
  A of fm | Closed of IntInf.int | NClosed of IntInf.int;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs;

fun append [] ys = ys
  | append (x :: xs) ys = x :: append xs ys;

fun disjuncts (Or (p, q)) = append (disjuncts p) (disjuncts q)
  | disjuncts F = []
  | disjuncts T = [T]
  | disjuncts (Lt u) = [Lt u]
  | disjuncts (Le v) = [Le v]
  | disjuncts (Gt w) = [Gt w]
  | disjuncts (Ge x) = [Ge x]
  | disjuncts (Eq y) = [Eq y]
  | disjuncts (NEq z) = [NEq z]
  | disjuncts (Dvd (aa, ab)) = [Dvd (aa, ab)]
  | disjuncts (NDvd (ac, ad)) = [NDvd (ac, ad)]
  | disjuncts (Not ae) = [Not ae]
  | disjuncts (And (af, ag)) = [And (af, ag)]
  | disjuncts (Imp (aj, ak)) = [Imp (aj, ak)]
  | disjuncts (Iff (al, am)) = [Iff (al, am)]
  | disjuncts (E an) = [E an]
  | disjuncts (A ao) = [A ao]
  | disjuncts (Closed ap) = [Closed ap]
  | disjuncts (NClosed aq) = [NClosed aq];

fun fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
  (NClosed nat) = f19 nat
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Closed nat) = f18 nat
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (A fm) = f17 fm
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (E fm) = f16 fm
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Iff (fm1, fm2)) = f15 fm1 fm2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Imp (fm1, fm2)) = f14 fm1 fm2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Or (fm1, fm2)) = f13 fm1 fm2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (And (fm1, fm2)) = f12 fm1 fm2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Not fm) = f11 fm
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (NDvd (inta, num)) = f10 inta num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Dvd (inta, num)) = f9 inta num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (NEq num) = f8 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Eq num) = f7 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Ge num) = f6 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Gt num) = f5 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Le num) = f4 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    (Lt num) = f3 num
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 F
    = f2
  | fm_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 T
    = f1;

fun eq_num (C intaa) (C inta) = ((intaa : IntInf.int) = inta)
  | eq_num (Bound nata) (Bound nat) = ((nata : IntInf.int) = nat)
  | eq_num (Cn (nata, intaa, numa)) (Cn (nat, inta, num)) =
    ((nata : IntInf.int) = nat) andalso
      (((intaa : IntInf.int) = inta) andalso eq_num numa num)
  | eq_num (Neg numa) (Neg num) = eq_num numa num
  | eq_num (Add (num1a, num2a)) (Add (num1, num2)) =
    eq_num num1a num1 andalso eq_num num2a num2
  | eq_num (Sub (num1a, num2a)) (Sub (num1, num2)) =
    eq_num num1a num1 andalso eq_num num2a num2
  | eq_num (Mul (intaa, numa)) (Mul (inta, num)) =
    ((intaa : IntInf.int) = inta) andalso eq_num numa num
  | eq_num (C inta) (Bound nat) = false
  | eq_num (Bound nat) (C inta) = false
  | eq_num (C intaa) (Cn (nat, inta, num)) = false
  | eq_num (Cn (nat, intaa, num)) (C inta) = false
  | eq_num (C inta) (Neg num) = false
  | eq_num (Neg num) (C inta) = false
  | eq_num (C inta) (Add (num1, num2)) = false
  | eq_num (Add (num1, num2)) (C inta) = false
  | eq_num (C inta) (Sub (num1, num2)) = false
  | eq_num (Sub (num1, num2)) (C inta) = false
  | eq_num (C intaa) (Mul (inta, num)) = false
  | eq_num (Mul (intaa, num)) (C inta) = false
  | eq_num (Bound nata) (Cn (nat, inta, num)) = false
  | eq_num (Cn (nata, inta, num)) (Bound nat) = false
  | eq_num (Bound nat) (Neg num) = false
  | eq_num (Neg num) (Bound nat) = false
  | eq_num (Bound nat) (Add (num1, num2)) = false
  | eq_num (Add (num1, num2)) (Bound nat) = false
  | eq_num (Bound nat) (Sub (num1, num2)) = false
  | eq_num (Sub (num1, num2)) (Bound nat) = false
  | eq_num (Bound nat) (Mul (inta, num)) = false
  | eq_num (Mul (inta, num)) (Bound nat) = false
  | eq_num (Cn (nat, inta, numa)) (Neg num) = false
  | eq_num (Neg numa) (Cn (nat, inta, num)) = false
  | eq_num (Cn (nat, inta, num)) (Add (num1, num2)) = false
  | eq_num (Add (num1, num2)) (Cn (nat, inta, num)) = false
  | eq_num (Cn (nat, inta, num)) (Sub (num1, num2)) = false
  | eq_num (Sub (num1, num2)) (Cn (nat, inta, num)) = false
  | eq_num (Cn (nat, intaa, numa)) (Mul (inta, num)) = false
  | eq_num (Mul (intaa, numa)) (Cn (nat, inta, num)) = false
  | eq_num (Neg num) (Add (num1, num2)) = false
  | eq_num (Add (num1, num2)) (Neg num) = false
  | eq_num (Neg num) (Sub (num1, num2)) = false
  | eq_num (Sub (num1, num2)) (Neg num) = false
  | eq_num (Neg numa) (Mul (inta, num)) = false
  | eq_num (Mul (inta, numa)) (Neg num) = false
  | eq_num (Add (num1a, num2a)) (Sub (num1, num2)) = false
  | eq_num (Sub (num1a, num2a)) (Add (num1, num2)) = false
  | eq_num (Add (num1, num2)) (Mul (inta, num)) = false
  | eq_num (Mul (inta, num)) (Add (num1, num2)) = false
  | eq_num (Sub (num1, num2)) (Mul (inta, num)) = false
  | eq_num (Mul (inta, num)) (Sub (num1, num2)) = false;

fun eq_fm T T = true
  | eq_fm F F = true
  | eq_fm (Lt numa) (Lt num) = eq_num numa num
  | eq_fm (Le numa) (Le num) = eq_num numa num
  | eq_fm (Gt numa) (Gt num) = eq_num numa num
  | eq_fm (Ge numa) (Ge num) = eq_num numa num
  | eq_fm (Eq numa) (Eq num) = eq_num numa num
  | eq_fm (NEq numa) (NEq num) = eq_num numa num
  | eq_fm (Dvd (intaa, numa)) (Dvd (inta, num)) =
    ((intaa : IntInf.int) = inta) andalso eq_num numa num
  | eq_fm (NDvd (intaa, numa)) (NDvd (inta, num)) =
    ((intaa : IntInf.int) = inta) andalso eq_num numa num
  | eq_fm (Not fma) (Not fm) = eq_fm fma fm
  | eq_fm (And (fm1a, fm2a)) (And (fm1, fm2)) =
    eq_fm fm1a fm1 andalso eq_fm fm2a fm2
  | eq_fm (Or (fm1a, fm2a)) (Or (fm1, fm2)) =
    eq_fm fm1a fm1 andalso eq_fm fm2a fm2
  | eq_fm (Imp (fm1a, fm2a)) (Imp (fm1, fm2)) =
    eq_fm fm1a fm1 andalso eq_fm fm2a fm2
  | eq_fm (Iff (fm1a, fm2a)) (Iff (fm1, fm2)) =
    eq_fm fm1a fm1 andalso eq_fm fm2a fm2
  | eq_fm (E fma) (E fm) = eq_fm fma fm
  | eq_fm (A fma) (A fm) = eq_fm fma fm
  | eq_fm (Closed nata) (Closed nat) = ((nata : IntInf.int) = nat)
  | eq_fm (NClosed nata) (NClosed nat) = ((nata : IntInf.int) = nat)
  | eq_fm T F = false
  | eq_fm F T = false
  | eq_fm T (Lt num) = false
  | eq_fm (Lt num) T = false
  | eq_fm T (Le num) = false
  | eq_fm (Le num) T = false
  | eq_fm T (Gt num) = false
  | eq_fm (Gt num) T = false
  | eq_fm T (Ge num) = false
  | eq_fm (Ge num) T = false
  | eq_fm T (Eq num) = false
  | eq_fm (Eq num) T = false
  | eq_fm T (NEq num) = false
  | eq_fm (NEq num) T = false
  | eq_fm T (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) T = false
  | eq_fm T (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) T = false
  | eq_fm T (Not fm) = false
  | eq_fm (Not fm) T = false
  | eq_fm T (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) T = false
  | eq_fm T (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) T = false
  | eq_fm T (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) T = false
  | eq_fm T (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) T = false
  | eq_fm T (E fm) = false
  | eq_fm (E fm) T = false
  | eq_fm T (A fm) = false
  | eq_fm (A fm) T = false
  | eq_fm T (Closed nat) = false
  | eq_fm (Closed nat) T = false
  | eq_fm T (NClosed nat) = false
  | eq_fm (NClosed nat) T = false
  | eq_fm F (Lt num) = false
  | eq_fm (Lt num) F = false
  | eq_fm F (Le num) = false
  | eq_fm (Le num) F = false
  | eq_fm F (Gt num) = false
  | eq_fm (Gt num) F = false
  | eq_fm F (Ge num) = false
  | eq_fm (Ge num) F = false
  | eq_fm F (Eq num) = false
  | eq_fm (Eq num) F = false
  | eq_fm F (NEq num) = false
  | eq_fm (NEq num) F = false
  | eq_fm F (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) F = false
  | eq_fm F (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) F = false
  | eq_fm F (Not fm) = false
  | eq_fm (Not fm) F = false
  | eq_fm F (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) F = false
  | eq_fm F (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) F = false
  | eq_fm F (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) F = false
  | eq_fm F (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) F = false
  | eq_fm F (E fm) = false
  | eq_fm (E fm) F = false
  | eq_fm F (A fm) = false
  | eq_fm (A fm) F = false
  | eq_fm F (Closed nat) = false
  | eq_fm (Closed nat) F = false
  | eq_fm F (NClosed nat) = false
  | eq_fm (NClosed nat) F = false
  | eq_fm (Lt numa) (Le num) = false
  | eq_fm (Le numa) (Lt num) = false
  | eq_fm (Lt numa) (Gt num) = false
  | eq_fm (Gt numa) (Lt num) = false
  | eq_fm (Lt numa) (Ge num) = false
  | eq_fm (Ge numa) (Lt num) = false
  | eq_fm (Lt numa) (Eq num) = false
  | eq_fm (Eq numa) (Lt num) = false
  | eq_fm (Lt numa) (NEq num) = false
  | eq_fm (NEq numa) (Lt num) = false
  | eq_fm (Lt numa) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, numa)) (Lt num) = false
  | eq_fm (Lt numa) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, numa)) (Lt num) = false
  | eq_fm (Lt num) (Not fm) = false
  | eq_fm (Not fm) (Lt num) = false
  | eq_fm (Lt num) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (Lt num) = false
  | eq_fm (Lt num) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (Lt num) = false
  | eq_fm (Lt num) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (Lt num) = false
  | eq_fm (Lt num) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (Lt num) = false
  | eq_fm (Lt num) (E fm) = false
  | eq_fm (E fm) (Lt num) = false
  | eq_fm (Lt num) (A fm) = false
  | eq_fm (A fm) (Lt num) = false
  | eq_fm (Lt num) (Closed nat) = false
  | eq_fm (Closed nat) (Lt num) = false
  | eq_fm (Lt num) (NClosed nat) = false
  | eq_fm (NClosed nat) (Lt num) = false
  | eq_fm (Le numa) (Gt num) = false
  | eq_fm (Gt numa) (Le num) = false
  | eq_fm (Le numa) (Ge num) = false
  | eq_fm (Ge numa) (Le num) = false
  | eq_fm (Le numa) (Eq num) = false
  | eq_fm (Eq numa) (Le num) = false
  | eq_fm (Le numa) (NEq num) = false
  | eq_fm (NEq numa) (Le num) = false
  | eq_fm (Le numa) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, numa)) (Le num) = false
  | eq_fm (Le numa) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, numa)) (Le num) = false
  | eq_fm (Le num) (Not fm) = false
  | eq_fm (Not fm) (Le num) = false
  | eq_fm (Le num) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (Le num) = false
  | eq_fm (Le num) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (Le num) = false
  | eq_fm (Le num) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (Le num) = false
  | eq_fm (Le num) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (Le num) = false
  | eq_fm (Le num) (E fm) = false
  | eq_fm (E fm) (Le num) = false
  | eq_fm (Le num) (A fm) = false
  | eq_fm (A fm) (Le num) = false
  | eq_fm (Le num) (Closed nat) = false
  | eq_fm (Closed nat) (Le num) = false
  | eq_fm (Le num) (NClosed nat) = false
  | eq_fm (NClosed nat) (Le num) = false
  | eq_fm (Gt numa) (Ge num) = false
  | eq_fm (Ge numa) (Gt num) = false
  | eq_fm (Gt numa) (Eq num) = false
  | eq_fm (Eq numa) (Gt num) = false
  | eq_fm (Gt numa) (NEq num) = false
  | eq_fm (NEq numa) (Gt num) = false
  | eq_fm (Gt numa) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, numa)) (Gt num) = false
  | eq_fm (Gt numa) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, numa)) (Gt num) = false
  | eq_fm (Gt num) (Not fm) = false
  | eq_fm (Not fm) (Gt num) = false
  | eq_fm (Gt num) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (Gt num) = false
  | eq_fm (Gt num) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (Gt num) = false
  | eq_fm (Gt num) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (Gt num) = false
  | eq_fm (Gt num) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (Gt num) = false
  | eq_fm (Gt num) (E fm) = false
  | eq_fm (E fm) (Gt num) = false
  | eq_fm (Gt num) (A fm) = false
  | eq_fm (A fm) (Gt num) = false
  | eq_fm (Gt num) (Closed nat) = false
  | eq_fm (Closed nat) (Gt num) = false
  | eq_fm (Gt num) (NClosed nat) = false
  | eq_fm (NClosed nat) (Gt num) = false
  | eq_fm (Ge numa) (Eq num) = false
  | eq_fm (Eq numa) (Ge num) = false
  | eq_fm (Ge numa) (NEq num) = false
  | eq_fm (NEq numa) (Ge num) = false
  | eq_fm (Ge numa) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, numa)) (Ge num) = false
  | eq_fm (Ge numa) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, numa)) (Ge num) = false
  | eq_fm (Ge num) (Not fm) = false
  | eq_fm (Not fm) (Ge num) = false
  | eq_fm (Ge num) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (Ge num) = false
  | eq_fm (Ge num) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (Ge num) = false
  | eq_fm (Ge num) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (Ge num) = false
  | eq_fm (Ge num) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (Ge num) = false
  | eq_fm (Ge num) (E fm) = false
  | eq_fm (E fm) (Ge num) = false
  | eq_fm (Ge num) (A fm) = false
  | eq_fm (A fm) (Ge num) = false
  | eq_fm (Ge num) (Closed nat) = false
  | eq_fm (Closed nat) (Ge num) = false
  | eq_fm (Ge num) (NClosed nat) = false
  | eq_fm (NClosed nat) (Ge num) = false
  | eq_fm (Eq numa) (NEq num) = false
  | eq_fm (NEq numa) (Eq num) = false
  | eq_fm (Eq numa) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, numa)) (Eq num) = false
  | eq_fm (Eq numa) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, numa)) (Eq num) = false
  | eq_fm (Eq num) (Not fm) = false
  | eq_fm (Not fm) (Eq num) = false
  | eq_fm (Eq num) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (Eq num) = false
  | eq_fm (Eq num) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (Eq num) = false
  | eq_fm (Eq num) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (Eq num) = false
  | eq_fm (Eq num) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (Eq num) = false
  | eq_fm (Eq num) (E fm) = false
  | eq_fm (E fm) (Eq num) = false
  | eq_fm (Eq num) (A fm) = false
  | eq_fm (A fm) (Eq num) = false
  | eq_fm (Eq num) (Closed nat) = false
  | eq_fm (Closed nat) (Eq num) = false
  | eq_fm (Eq num) (NClosed nat) = false
  | eq_fm (NClosed nat) (Eq num) = false
  | eq_fm (NEq numa) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, numa)) (NEq num) = false
  | eq_fm (NEq numa) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, numa)) (NEq num) = false
  | eq_fm (NEq num) (Not fm) = false
  | eq_fm (Not fm) (NEq num) = false
  | eq_fm (NEq num) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (NEq num) = false
  | eq_fm (NEq num) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (NEq num) = false
  | eq_fm (NEq num) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (NEq num) = false
  | eq_fm (NEq num) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (NEq num) = false
  | eq_fm (NEq num) (E fm) = false
  | eq_fm (E fm) (NEq num) = false
  | eq_fm (NEq num) (A fm) = false
  | eq_fm (A fm) (NEq num) = false
  | eq_fm (NEq num) (Closed nat) = false
  | eq_fm (Closed nat) (NEq num) = false
  | eq_fm (NEq num) (NClosed nat) = false
  | eq_fm (NClosed nat) (NEq num) = false
  | eq_fm (Dvd (intaa, numa)) (NDvd (inta, num)) = false
  | eq_fm (NDvd (intaa, numa)) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (Not fm) = false
  | eq_fm (Not fm) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (E fm) = false
  | eq_fm (E fm) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (A fm) = false
  | eq_fm (A fm) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (Closed nat) = false
  | eq_fm (Closed nat) (Dvd (inta, num)) = false
  | eq_fm (Dvd (inta, num)) (NClosed nat) = false
  | eq_fm (NClosed nat) (Dvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (Not fm) = false
  | eq_fm (Not fm) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (E fm) = false
  | eq_fm (E fm) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (A fm) = false
  | eq_fm (A fm) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (Closed nat) = false
  | eq_fm (Closed nat) (NDvd (inta, num)) = false
  | eq_fm (NDvd (inta, num)) (NClosed nat) = false
  | eq_fm (NClosed nat) (NDvd (inta, num)) = false
  | eq_fm (Not fm) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (Not fm) = false
  | eq_fm (Not fm) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (Not fm) = false
  | eq_fm (Not fm) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (Not fm) = false
  | eq_fm (Not fm) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (Not fm) = false
  | eq_fm (Not fma) (E fm) = false
  | eq_fm (E fma) (Not fm) = false
  | eq_fm (Not fma) (A fm) = false
  | eq_fm (A fma) (Not fm) = false
  | eq_fm (Not fm) (Closed nat) = false
  | eq_fm (Closed nat) (Not fm) = false
  | eq_fm (Not fm) (NClosed nat) = false
  | eq_fm (NClosed nat) (Not fm) = false
  | eq_fm (And (fm1a, fm2a)) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1a, fm2a)) (And (fm1, fm2)) = false
  | eq_fm (And (fm1a, fm2a)) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1a, fm2a)) (And (fm1, fm2)) = false
  | eq_fm (And (fm1a, fm2a)) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1a, fm2a)) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (E fm) = false
  | eq_fm (E fm) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (A fm) = false
  | eq_fm (A fm) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (Closed nat) = false
  | eq_fm (Closed nat) (And (fm1, fm2)) = false
  | eq_fm (And (fm1, fm2)) (NClosed nat) = false
  | eq_fm (NClosed nat) (And (fm1, fm2)) = false
  | eq_fm (Or (fm1a, fm2a)) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1a, fm2a)) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1a, fm2a)) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1a, fm2a)) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (E fm) = false
  | eq_fm (E fm) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (A fm) = false
  | eq_fm (A fm) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (Closed nat) = false
  | eq_fm (Closed nat) (Or (fm1, fm2)) = false
  | eq_fm (Or (fm1, fm2)) (NClosed nat) = false
  | eq_fm (NClosed nat) (Or (fm1, fm2)) = false
  | eq_fm (Imp (fm1a, fm2a)) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1a, fm2a)) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (E fm) = false
  | eq_fm (E fm) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (A fm) = false
  | eq_fm (A fm) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (Closed nat) = false
  | eq_fm (Closed nat) (Imp (fm1, fm2)) = false
  | eq_fm (Imp (fm1, fm2)) (NClosed nat) = false
  | eq_fm (NClosed nat) (Imp (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (E fm) = false
  | eq_fm (E fm) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (A fm) = false
  | eq_fm (A fm) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (Closed nat) = false
  | eq_fm (Closed nat) (Iff (fm1, fm2)) = false
  | eq_fm (Iff (fm1, fm2)) (NClosed nat) = false
  | eq_fm (NClosed nat) (Iff (fm1, fm2)) = false
  | eq_fm (E fma) (A fm) = false
  | eq_fm (A fma) (E fm) = false
  | eq_fm (E fm) (Closed nat) = false
  | eq_fm (Closed nat) (E fm) = false
  | eq_fm (E fm) (NClosed nat) = false
  | eq_fm (NClosed nat) (E fm) = false
  | eq_fm (A fm) (Closed nat) = false
  | eq_fm (Closed nat) (A fm) = false
  | eq_fm (A fm) (NClosed nat) = false
  | eq_fm (NClosed nat) (A fm) = false
  | eq_fm (Closed nata) (NClosed nat) = false
  | eq_fm (NClosed nata) (Closed nat) = false;

fun djf f p q =
  (if eq_fm q T then T
    else (if eq_fm q F then f p
           else (case f p of T => T | F => q | Lt _ => Or (f p, q)
                  | Le _ => Or (f p, q) | Gt _ => Or (f p, q)
                  | Ge _ => Or (f p, q) | Eq _ => Or (f p, q)
                  | NEq _ => Or (f p, q) | Dvd (_, _) => Or (f p, q)
                  | NDvd (_, _) => Or (f p, q) | Not _ => Or (f p, q)
                  | And (_, _) => Or (f p, q) | Or (_, _) => Or (f p, q)
                  | Imp (_, _) => Or (f p, q) | Iff (_, _) => Or (f p, q)
                  | E _ => Or (f p, q) | A _ => Or (f p, q)
                  | Closed _ => Or (f p, q) | NClosed _ => Or (f p, q))));

fun foldr f [] a = a
  | foldr f (x :: xs) a = f x (foldr f xs a);

fun evaldjf f ps = foldr (djf f) ps F;

fun dj f p = evaldjf f (disjuncts p);

fun disj p q =
  (if eq_fm p T orelse eq_fm q T then T
    else (if eq_fm p F then q else (if eq_fm q F then p else Or (p, q))));

fun minus_nat n m = IntInf.max (0, (IntInf.- (n, m)));

fun decrnum (Bound n) = Bound (minus_nat n (1 : IntInf.int))
  | decrnum (Neg a) = Neg (decrnum a)
  | decrnum (Add (a, b)) = Add (decrnum a, decrnum b)
  | decrnum (Sub (a, b)) = Sub (decrnum a, decrnum b)
  | decrnum (Mul (c, a)) = Mul (c, decrnum a)
  | decrnum (Cn (n, i, a)) = Cn (minus_nat n (1 : IntInf.int), i, decrnum a)
  | decrnum (C u) = C u;

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
  | decr (E ao) = E ao
  | decr (A ap) = A ap
  | decr (Closed aq) = Closed aq
  | decr (NClosed ar) = NClosed ar;

fun concat_map f [] = []
  | concat_map f (x :: xs) = append (f x) (concat_map f xs);

fun numsubst0 t (C c) = C c
  | numsubst0 t (Bound n) =
    (if ((n : IntInf.int) = (0 : IntInf.int)) then t else Bound n)
  | numsubst0 t (Neg a) = Neg (numsubst0 t a)
  | numsubst0 t (Add (a, b)) = Add (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Sub (a, b)) = Sub (numsubst0 t a, numsubst0 t b)
  | numsubst0 t (Mul (i, a)) = Mul (i, numsubst0 t a)
  | numsubst0 t (Cn (v, i, a)) =
    (if ((v : IntInf.int) = (0 : IntInf.int))
      then Add (Mul (i, t), numsubst0 t a)
      else Cn (suc (minus_nat v (1 : IntInf.int)), i, numsubst0 t a));

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
  | minusinf (Not ae) = Not ae
  | minusinf (Imp (aj, ak)) = Imp (aj, ak)
  | minusinf (Iff (al, am)) = Iff (al, am)
  | minusinf (E an) = E an
  | minusinf (A ao) = A ao
  | minusinf (Closed ap) = Closed ap
  | minusinf (NClosed aq) = NClosed aq
  | minusinf (Lt (Cn (cm, c, e))) =
    (if ((cm : IntInf.int) = (0 : IntInf.int)) then T
      else Lt (Cn (suc (minus_nat cm (1 : IntInf.int)), c, e)))
  | minusinf (Le (Cn (dm, c, e))) =
    (if ((dm : IntInf.int) = (0 : IntInf.int)) then T
      else Le (Cn (suc (minus_nat dm (1 : IntInf.int)), c, e)))
  | minusinf (Gt (Cn (em, c, e))) =
    (if ((em : IntInf.int) = (0 : IntInf.int)) then F
      else Gt (Cn (suc (minus_nat em (1 : IntInf.int)), c, e)))
  | minusinf (Ge (Cn (fm, c, e))) =
    (if ((fm : IntInf.int) = (0 : IntInf.int)) then F
      else Ge (Cn (suc (minus_nat fm (1 : IntInf.int)), c, e)))
  | minusinf (Eq (Cn (gm, c, e))) =
    (if ((gm : IntInf.int) = (0 : IntInf.int)) then F
      else Eq (Cn (suc (minus_nat gm (1 : IntInf.int)), c, e)))
  | minusinf (NEq (Cn (hm, c, e))) =
    (if ((hm : IntInf.int) = (0 : IntInf.int)) then T
      else NEq (Cn (suc (minus_nat hm (1 : IntInf.int)), c, e)));

val eq_int = {eq = (fn a => fn b => ((a : IntInf.int) = b))} : IntInf.int eq;

val zero_int : IntInf.int = (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_inta = {zero = zero_int} : IntInf.int zero;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a no_zero_divisors =
  {times_no_zero_divisors : 'a times, zero_no_zero_divisors : 'a zero};
val times_no_zero_divisors = #times_no_zero_divisors :
  'a no_zero_divisors -> 'a times;
val zero_no_zero_divisors = #zero_no_zero_divisors :
  'a no_zero_divisors -> 'a zero;

val times_int = {times = (fn a => fn b => IntInf.* (a, b))} : IntInf.int times;

val no_zero_divisors_int =
  {times_no_zero_divisors = times_int, zero_no_zero_divisors = zero_inta} :
  IntInf.int no_zero_divisors;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

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

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_1 =
  {monoid_mult_semiring_1 : 'a monoid_mult,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val monoid_mult_semiring_1 = #monoid_mult_semiring_1 :
  'a semiring_1 -> 'a monoid_mult;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;

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

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

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

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    dvd_comm_semiring_1 : 'a dvd, semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val dvd_comm_semiring_1 = #dvd_comm_semiring_1 : 'a comm_semiring_1 -> 'a dvd;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

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

type 'a diva = {dvd_div : 'a dvd, diva : 'a -> 'a -> 'a, moda : 'a -> 'a -> 'a};
val dvd_div = #dvd_div : 'a diva -> 'a dvd;
val diva = #diva : 'a diva -> 'a -> 'a -> 'a;
val moda = #moda : 'a diva -> 'a -> 'a -> 'a;

type 'a semiring_div =
  {div_semiring_div : 'a diva,
    comm_semiring_1_cancel_semiring_div : 'a comm_semiring_1_cancel,
    no_zero_divisors_semiring_div : 'a no_zero_divisors};
val div_semiring_div = #div_semiring_div : 'a semiring_div -> 'a diva;
val comm_semiring_1_cancel_semiring_div = #comm_semiring_1_cancel_semiring_div :
  'a semiring_div -> 'a comm_semiring_1_cancel;
val no_zero_divisors_semiring_div = #no_zero_divisors_semiring_div :
  'a semiring_div -> 'a no_zero_divisors;

val one_int : IntInf.int = (1 : IntInf.int);

val one_inta = {one = one_int} : IntInf.int one;

val zero_neq_one_int =
  {one_zero_neq_one = one_inta, zero_zero_neq_one = zero_inta} :
  IntInf.int zero_neq_one;

val semigroup_mult_int = {times_semigroup_mult = times_int} :
  IntInf.int semigroup_mult;

val plus_int = {plus = (fn a => fn b => IntInf.+ (a, b))} : IntInf.int plus;

val semigroup_add_int = {plus_semigroup_add = plus_int} :
  IntInf.int semigroup_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : IntInf.int ab_semigroup_add;

val semiring_int =
  {ab_semigroup_add_semiring = ab_semigroup_add_int,
    semigroup_mult_semiring = semigroup_mult_int}
  : IntInf.int semiring;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_inta} :
  IntInf.int mult_zero;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_inta} :
  IntInf.int monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : IntInf.int comm_monoid_add;

val semiring_0_int =
  {comm_monoid_add_semiring_0 = comm_monoid_add_int,
    mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int}
  : IntInf.int semiring_0;

val power_int = {one_power = one_inta, times_power = times_int} :
  IntInf.int power;

val monoid_mult_int =
  {semigroup_mult_monoid_mult = semigroup_mult_int,
    power_monoid_mult = power_int}
  : IntInf.int monoid_mult;

val semiring_1_int =
  {monoid_mult_semiring_1 = monoid_mult_int,
    semiring_0_semiring_1 = semiring_0_int,
    zero_neq_one_semiring_1 = zero_neq_one_int}
  : IntInf.int semiring_1;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  IntInf.int cancel_semigroup_add;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int}
  : IntInf.int cancel_ab_semigroup_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : IntInf.int cancel_comm_monoid_add;

val semiring_0_cancel_int =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int,
    semiring_0_semiring_0_cancel = semiring_0_int}
  : IntInf.int semiring_0_cancel;

val semiring_1_cancel_int =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int,
    semiring_1_semiring_1_cancel = semiring_1_int}
  : IntInf.int semiring_1_cancel;

val dvd_int = {times_dvd = times_int} : IntInf.int dvd;

val ab_semigroup_mult_int =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
  IntInf.int ab_semigroup_mult;

val comm_semiring_int =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int,
    semiring_comm_semiring = semiring_int}
  : IntInf.int comm_semiring;

val comm_semiring_0_int =
  {comm_semiring_comm_semiring_0 = comm_semiring_int,
    semiring_0_comm_semiring_0 = semiring_0_int}
  : IntInf.int comm_semiring_0;

val comm_monoid_mult_int =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int,
    monoid_mult_comm_monoid_mult = monoid_mult_int}
  : IntInf.int comm_monoid_mult;

val comm_semiring_1_int =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_int,
    dvd_comm_semiring_1 = dvd_int, semiring_1_comm_semiring_1 = semiring_1_int}
  : IntInf.int comm_semiring_1;

val comm_semiring_0_cancel_int =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
  : IntInf.int comm_semiring_0_cancel;

val comm_semiring_1_cancel_int =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
  : IntInf.int comm_semiring_1_cancel;

fun abs_int i = (if IntInf.< (i, (0 : IntInf.int)) then IntInf.~ i else i);

fun split f (a, b) = f a b;

fun sgn_int i =
  (if ((i : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< ((0 : IntInf.int), i) then (1 : IntInf.int)
           else IntInf.~ (1 : IntInf.int)));

fun apsnd f (x, y) = (x, f y);

fun divmod_int k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else apsnd (fn a => IntInf.* (sgn_int l, a))
                  (if (((sgn_int k) : IntInf.int) = (sgn_int l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (abs_int l, s)))
                         end)));

fun snd (a, b) = b;

fun mod_int a b = snd (divmod_int a b);

fun fst (a, b) = a;

fun div_int a b = fst (divmod_int a b);

val div_inta = {dvd_div = dvd_int, diva = div_int, moda = mod_int} :
  IntInf.int diva;

val semiring_div_int =
  {div_semiring_div = div_inta,
    comm_semiring_1_cancel_semiring_div = comm_semiring_1_cancel_int,
    no_zero_divisors_semiring_div = no_zero_divisors_int}
  : IntInf.int semiring_div;

fun dvd (A1_, A2_) a b =
  eqa A2_ (moda (div_semiring_div A1_) b a)
    (zero ((zero_no_zero_divisors o no_zero_divisors_semiring_div) A1_));

fun num_case f1 f2 f3 f4 f5 f6 f7 (Mul (inta, num)) = f7 inta num
  | num_case f1 f2 f3 f4 f5 f6 f7 (Sub (num1, num2)) = f6 num1 num2
  | num_case f1 f2 f3 f4 f5 f6 f7 (Add (num1, num2)) = f5 num1 num2
  | num_case f1 f2 f3 f4 f5 f6 f7 (Neg num) = f4 num
  | num_case f1 f2 f3 f4 f5 f6 f7 (Cn (nat, inta, num)) = f3 nat inta num
  | num_case f1 f2 f3 f4 f5 f6 f7 (Bound nat) = f2 nat
  | num_case f1 f2 f3 f4 f5 f6 f7 (C inta) = f1 inta;

fun nummul i (C j) = C (IntInf.* (i, j))
  | nummul i (Cn (n, c, t)) = Cn (n, IntInf.* (c, i), nummul i t)
  | nummul i (Bound v) = Mul (i, Bound v)
  | nummul i (Neg v) = Mul (i, Neg v)
  | nummul i (Add (v, va)) = Mul (i, Add (v, va))
  | nummul i (Sub (v, va)) = Mul (i, Sub (v, va))
  | nummul i (Mul (v, va)) = Mul (i, Mul (v, va));

fun numneg t = nummul (IntInf.~ (1 : IntInf.int)) t;

fun numadd (Cn (n1, c1, r1), Cn (n2, c2, r2)) =
  (if ((n1 : IntInf.int) = n2)
    then let
           val c = IntInf.+ (c1, c2);
         in
           (if ((c : IntInf.int) = (0 : IntInf.int)) then numadd (r1, r2)
             else Cn (n1, c, numadd (r1, r2)))
         end
    else (if IntInf.<= (n1, n2)
           then Cn (n1, c1, numadd (r1, Add (Mul (c2, Bound n2), r2)))
           else Cn (n2, c2, numadd (Add (Mul (c1, Bound n1), r1), r2))))
  | numadd (Cn (n1, c1, r1), C dd) = Cn (n1, c1, numadd (r1, C dd))
  | numadd (Cn (n1, c1, r1), Bound de) = Cn (n1, c1, numadd (r1, Bound de))
  | numadd (Cn (n1, c1, r1), Neg di) = Cn (n1, c1, numadd (r1, Neg di))
  | numadd (Cn (n1, c1, r1), Add (dj, dk)) =
    Cn (n1, c1, numadd (r1, Add (dj, dk)))
  | numadd (Cn (n1, c1, r1), Sub (dl, dm)) =
    Cn (n1, c1, numadd (r1, Sub (dl, dm)))
  | numadd (Cn (n1, c1, r1), Mul (dn, doa)) =
    Cn (n1, c1, numadd (r1, Mul (dn, doa)))
  | numadd (C w, Cn (n2, c2, r2)) = Cn (n2, c2, numadd (C w, r2))
  | numadd (Bound x, Cn (n2, c2, r2)) = Cn (n2, c2, numadd (Bound x, r2))
  | numadd (Neg ac, Cn (n2, c2, r2)) = Cn (n2, c2, numadd (Neg ac, r2))
  | numadd (Add (ad, ae), Cn (n2, c2, r2)) =
    Cn (n2, c2, numadd (Add (ad, ae), r2))
  | numadd (Sub (af, ag), Cn (n2, c2, r2)) =
    Cn (n2, c2, numadd (Sub (af, ag), r2))
  | numadd (Mul (ah, ai), Cn (n2, c2, r2)) =
    Cn (n2, c2, numadd (Mul (ah, ai), r2))
  | numadd (C b1, C b2) = C (IntInf.+ (b1, b2))
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
  | numadd (Neg ao, Neg es) = Add (Neg ao, Neg es)
  | numadd (Neg ao, Add (et, eu)) = Add (Neg ao, Add (et, eu))
  | numadd (Neg ao, Sub (ev, ew)) = Add (Neg ao, Sub (ev, ew))
  | numadd (Neg ao, Mul (ex, ey)) = Add (Neg ao, Mul (ex, ey))
  | numadd (Add (ap, aq), C fl) = Add (Add (ap, aq), C fl)
  | numadd (Add (ap, aq), Bound fm) = Add (Add (ap, aq), Bound fm)
  | numadd (Add (ap, aq), Neg fq) = Add (Add (ap, aq), Neg fq)
  | numadd (Add (ap, aq), Add (fr, fs)) = Add (Add (ap, aq), Add (fr, fs))
  | numadd (Add (ap, aq), Sub (ft, fu)) = Add (Add (ap, aq), Sub (ft, fu))
  | numadd (Add (ap, aq), Mul (fv, fw)) = Add (Add (ap, aq), Mul (fv, fw))
  | numadd (Sub (ar, asa), C gj) = Add (Sub (ar, asa), C gj)
  | numadd (Sub (ar, asa), Bound gk) = Add (Sub (ar, asa), Bound gk)
  | numadd (Sub (ar, asa), Neg go) = Add (Sub (ar, asa), Neg go)
  | numadd (Sub (ar, asa), Add (gp, gq)) = Add (Sub (ar, asa), Add (gp, gq))
  | numadd (Sub (ar, asa), Sub (gr, gs)) = Add (Sub (ar, asa), Sub (gr, gs))
  | numadd (Sub (ar, asa), Mul (gt, gu)) = Add (Sub (ar, asa), Mul (gt, gu))
  | numadd (Mul (at, au), C hh) = Add (Mul (at, au), C hh)
  | numadd (Mul (at, au), Bound hi) = Add (Mul (at, au), Bound hi)
  | numadd (Mul (at, au), Neg hm) = Add (Mul (at, au), Neg hm)
  | numadd (Mul (at, au), Add (hn, ho)) = Add (Mul (at, au), Add (hn, ho))
  | numadd (Mul (at, au), Sub (hp, hq)) = Add (Mul (at, au), Sub (hp, hq))
  | numadd (Mul (at, au), Mul (hr, hs)) = Add (Mul (at, au), Mul (hr, hs));

fun numsub s t =
  (if eq_num s t then C (0 : IntInf.int) else numadd (s, numneg t));

fun simpnum (C j) = C j
  | simpnum (Bound n) = Cn (n, (1 : IntInf.int), C (0 : IntInf.int))
  | simpnum (Neg t) = numneg (simpnum t)
  | simpnum (Add (t, s)) = numadd (simpnum t, simpnum s)
  | simpnum (Sub (t, s)) = numsub (simpnum t) (simpnum s)
  | simpnum (Mul (i, t)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then C (0 : IntInf.int)
      else nummul i (simpnum t))
  | simpnum (Cn (v, va, vb)) = Cn (v, va, vb);

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

fun iffa p q =
  (if eq_fm p q then T
    else (if eq_fm p (nota q) orelse eq_fm (nota p) q then F
           else (if eq_fm p F then nota q
                  else (if eq_fm q F then nota p
                         else (if eq_fm p T then q
                                else (if eq_fm q T then p else Iff (p, q)))))));

fun impa p q =
  (if eq_fm p F orelse eq_fm q T then T
    else (if eq_fm p T then q else (if eq_fm q F then nota p else Imp (p, q))));

fun conj p q =
  (if eq_fm p F orelse eq_fm q F then F
    else (if eq_fm p T then q else (if eq_fm q T then p else And (p, q))));

fun simpfm (And (p, q)) = conj (simpfm p) (simpfm q)
  | simpfm (Or (p, q)) = disj (simpfm p) (simpfm q)
  | simpfm (Imp (p, q)) = impa (simpfm p) (simpfm q)
  | simpfm (Iff (p, q)) = iffa (simpfm p) (simpfm q)
  | simpfm (Not p) = nota (simpfm p)
  | simpfm (Lt a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if IntInf.< (v, (0 : IntInf.int)) then T else F)
        | Bound _ => Lt aa | Cn (_, _, _) => Lt aa | Neg _ => Lt aa
        | Add (_, _) => Lt aa | Sub (_, _) => Lt aa | Mul (_, _) => Lt aa)
    end
  | simpfm (Le a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if IntInf.<= (v, (0 : IntInf.int)) then T else F)
        | Bound _ => Le aa | Cn (_, _, _) => Le aa | Neg _ => Le aa
        | Add (_, _) => Le aa | Sub (_, _) => Le aa | Mul (_, _) => Le aa)
    end
  | simpfm (Gt a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if IntInf.< ((0 : IntInf.int), v) then T else F)
        | Bound _ => Gt aa | Cn (_, _, _) => Gt aa | Neg _ => Gt aa
        | Add (_, _) => Gt aa | Sub (_, _) => Gt aa | Mul (_, _) => Gt aa)
    end
  | simpfm (Ge a) =
    let
      val aa = simpnum a;
    in
      (case aa of C v => (if IntInf.<= ((0 : IntInf.int), v) then T else F)
        | Bound _ => Ge aa | Cn (_, _, _) => Ge aa | Neg _ => Ge aa
        | Add (_, _) => Ge aa | Sub (_, _) => Ge aa | Mul (_, _) => Ge aa)
    end
  | simpfm (Eq a) =
    let
      val aa = simpnum a;
    in
      (case aa
        of C v => (if ((v : IntInf.int) = (0 : IntInf.int)) then T else F)
        | Bound _ => Eq aa | Cn (_, _, _) => Eq aa | Neg _ => Eq aa
        | Add (_, _) => Eq aa | Sub (_, _) => Eq aa | Mul (_, _) => Eq aa)
    end
  | simpfm (NEq a) =
    let
      val aa = simpnum a;
    in
      (case aa
        of C v => (if not ((v : IntInf.int) = (0 : IntInf.int)) then T else F)
        | Bound _ => NEq aa | Cn (_, _, _) => NEq aa | Neg _ => NEq aa
        | Add (_, _) => NEq aa | Sub (_, _) => NEq aa | Mul (_, _) => NEq aa)
    end
  | simpfm (Dvd (i, a)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then simpfm (Eq a)
      else (if (((abs_int i) : IntInf.int) = (1 : IntInf.int)) then T
             else let
                    val aa = simpnum a;
                  in
                    (case aa
                      of C v =>
                        (if dvd (semiring_div_int, eq_int) i v then T else F)
                      | Bound _ => Dvd (i, aa) | Cn (_, _, _) => Dvd (i, aa)
                      | Neg _ => Dvd (i, aa) | Add (_, _) => Dvd (i, aa)
                      | Sub (_, _) => Dvd (i, aa) | Mul (_, _) => Dvd (i, aa))
                  end))
  | simpfm (NDvd (i, a)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then simpfm (NEq a)
      else (if (((abs_int i) : IntInf.int) = (1 : IntInf.int)) then F
             else let
                    val aa = simpnum a;
                  in
                    (case aa
                      of C v =>
                        (if not (dvd (semiring_div_int, eq_int) i v) then T
                          else F)
                      | Bound _ => NDvd (i, aa) | Cn (_, _, _) => NDvd (i, aa)
                      | Neg _ => NDvd (i, aa) | Add (_, _) => NDvd (i, aa)
                      | Sub (_, _) => NDvd (i, aa) | Mul (_, _) => NDvd (i, aa))
                  end))
  | simpfm T = T
  | simpfm F = F
  | simpfm (E v) = E v
  | simpfm (A v) = A v
  | simpfm (Closed v) = Closed v
  | simpfm (NClosed v) = NClosed v;

fun iupt i j =
  (if IntInf.< (j, i) then []
    else i :: iupt (IntInf.+ (i, (1 : IntInf.int))) j);

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
  | mirror (Not ae) = Not ae
  | mirror (Imp (aj, ak)) = Imp (aj, ak)
  | mirror (Iff (al, am)) = Iff (al, am)
  | mirror (E an) = E an
  | mirror (A ao) = A ao
  | mirror (Closed ap) = Closed ap
  | mirror (NClosed aq) = NClosed aq
  | mirror (Lt (Cn (cm, c, e))) =
    (if ((cm : IntInf.int) = (0 : IntInf.int))
      then Gt (Cn ((0 : IntInf.int), c, Neg e))
      else Lt (Cn (suc (minus_nat cm (1 : IntInf.int)), c, e)))
  | mirror (Le (Cn (dm, c, e))) =
    (if ((dm : IntInf.int) = (0 : IntInf.int))
      then Ge (Cn ((0 : IntInf.int), c, Neg e))
      else Le (Cn (suc (minus_nat dm (1 : IntInf.int)), c, e)))
  | mirror (Gt (Cn (em, c, e))) =
    (if ((em : IntInf.int) = (0 : IntInf.int))
      then Lt (Cn ((0 : IntInf.int), c, Neg e))
      else Gt (Cn (suc (minus_nat em (1 : IntInf.int)), c, e)))
  | mirror (Ge (Cn (fm, c, e))) =
    (if ((fm : IntInf.int) = (0 : IntInf.int))
      then Le (Cn ((0 : IntInf.int), c, Neg e))
      else Ge (Cn (suc (minus_nat fm (1 : IntInf.int)), c, e)))
  | mirror (Eq (Cn (gm, c, e))) =
    (if ((gm : IntInf.int) = (0 : IntInf.int))
      then Eq (Cn ((0 : IntInf.int), c, Neg e))
      else Eq (Cn (suc (minus_nat gm (1 : IntInf.int)), c, e)))
  | mirror (NEq (Cn (hm, c, e))) =
    (if ((hm : IntInf.int) = (0 : IntInf.int))
      then NEq (Cn ((0 : IntInf.int), c, Neg e))
      else NEq (Cn (suc (minus_nat hm (1 : IntInf.int)), c, e)))
  | mirror (Dvd (i, Cn (im, c, e))) =
    (if ((im : IntInf.int) = (0 : IntInf.int))
      then Dvd (i, Cn ((0 : IntInf.int), c, Neg e))
      else Dvd (i, Cn (suc (minus_nat im (1 : IntInf.int)), c, e)))
  | mirror (NDvd (i, Cn (jm, c, e))) =
    (if ((jm : IntInf.int) = (0 : IntInf.int))
      then NDvd (i, Cn ((0 : IntInf.int), c, Neg e))
      else NDvd (i, Cn (suc (minus_nat jm (1 : IntInf.int)), c, e)));

fun size_list [] = (0 : IntInf.int)
  | size_list (a :: lista) = IntInf.+ (size_list lista, suc (0 : IntInf.int));

fun alpha (And (p, q)) = append (alpha p) (alpha q)
  | alpha (Or (p, q)) = append (alpha p) (alpha q)
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
  | alpha (Not ae) = []
  | alpha (Imp (aj, ak)) = []
  | alpha (Iff (al, am)) = []
  | alpha (E an) = []
  | alpha (A ao) = []
  | alpha (Closed ap) = []
  | alpha (NClosed aq) = []
  | alpha (Lt (Cn (cm, c, e))) =
    (if ((cm : IntInf.int) = (0 : IntInf.int)) then [e] else [])
  | alpha (Le (Cn (dm, c, e))) =
    (if ((dm : IntInf.int) = (0 : IntInf.int))
      then [Add (C (~1 : IntInf.int), e)] else [])
  | alpha (Gt (Cn (em, c, e))) =
    (if ((em : IntInf.int) = (0 : IntInf.int)) then [] else [])
  | alpha (Ge (Cn (fm, c, e))) =
    (if ((fm : IntInf.int) = (0 : IntInf.int)) then [] else [])
  | alpha (Eq (Cn (gm, c, e))) =
    (if ((gm : IntInf.int) = (0 : IntInf.int))
      then [Add (C (~1 : IntInf.int), e)] else [])
  | alpha (NEq (Cn (hm, c, e))) =
    (if ((hm : IntInf.int) = (0 : IntInf.int)) then [e] else []);

fun beta (And (p, q)) = append (beta p) (beta q)
  | beta (Or (p, q)) = append (beta p) (beta q)
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
  | beta (Not ae) = []
  | beta (Imp (aj, ak)) = []
  | beta (Iff (al, am)) = []
  | beta (E an) = []
  | beta (A ao) = []
  | beta (Closed ap) = []
  | beta (NClosed aq) = []
  | beta (Lt (Cn (cm, c, e))) =
    (if ((cm : IntInf.int) = (0 : IntInf.int)) then [] else [])
  | beta (Le (Cn (dm, c, e))) =
    (if ((dm : IntInf.int) = (0 : IntInf.int)) then [] else [])
  | beta (Gt (Cn (em, c, e))) =
    (if ((em : IntInf.int) = (0 : IntInf.int)) then [Neg e] else [])
  | beta (Ge (Cn (fm, c, e))) =
    (if ((fm : IntInf.int) = (0 : IntInf.int))
      then [Sub (C (~1 : IntInf.int), e)] else [])
  | beta (Eq (Cn (gm, c, e))) =
    (if ((gm : IntInf.int) = (0 : IntInf.int))
      then [Sub (C (~1 : IntInf.int), e)] else [])
  | beta (NEq (Cn (hm, c, e))) =
    (if ((hm : IntInf.int) = (0 : IntInf.int)) then [Neg e] else []);

val eq_numa = {eq = eq_num} : num eq;

fun member A_ x [] = false
  | member A_ x (y :: ys) = eqa A_ x y orelse member A_ x ys;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ x xs then remdups A_ xs else x :: remdups A_ xs);

fun gcd_int k l =
  abs_int
    (if ((l : IntInf.int) = (0 : IntInf.int)) then k
      else gcd_int l (mod_int (abs_int k) (abs_int l)));

fun lcm_int a b = div_int (IntInf.* (abs_int a, abs_int b)) (gcd_int a b);

fun delta (And (p, q)) = lcm_int (delta p) (delta q)
  | delta (Or (p, q)) = lcm_int (delta p) (delta q)
  | delta T = (1 : IntInf.int)
  | delta F = (1 : IntInf.int)
  | delta (Lt u) = (1 : IntInf.int)
  | delta (Le v) = (1 : IntInf.int)
  | delta (Gt w) = (1 : IntInf.int)
  | delta (Ge x) = (1 : IntInf.int)
  | delta (Eq y) = (1 : IntInf.int)
  | delta (NEq z) = (1 : IntInf.int)
  | delta (Dvd (aa, C bo)) = (1 : IntInf.int)
  | delta (Dvd (aa, Bound bp)) = (1 : IntInf.int)
  | delta (Dvd (aa, Neg bt)) = (1 : IntInf.int)
  | delta (Dvd (aa, Add (bu, bv))) = (1 : IntInf.int)
  | delta (Dvd (aa, Sub (bw, bx))) = (1 : IntInf.int)
  | delta (Dvd (aa, Mul (by, bz))) = (1 : IntInf.int)
  | delta (NDvd (ac, C co)) = (1 : IntInf.int)
  | delta (NDvd (ac, Bound cp)) = (1 : IntInf.int)
  | delta (NDvd (ac, Neg ct)) = (1 : IntInf.int)
  | delta (NDvd (ac, Add (cu, cv))) = (1 : IntInf.int)
  | delta (NDvd (ac, Sub (cw, cx))) = (1 : IntInf.int)
  | delta (NDvd (ac, Mul (cy, cz))) = (1 : IntInf.int)
  | delta (Not ae) = (1 : IntInf.int)
  | delta (Imp (aj, ak)) = (1 : IntInf.int)
  | delta (Iff (al, am)) = (1 : IntInf.int)
  | delta (E an) = (1 : IntInf.int)
  | delta (A ao) = (1 : IntInf.int)
  | delta (Closed ap) = (1 : IntInf.int)
  | delta (NClosed aq) = (1 : IntInf.int)
  | delta (Dvd (i, Cn (cm, c, e))) =
    (if ((cm : IntInf.int) = (0 : IntInf.int)) then i else (1 : IntInf.int))
  | delta (NDvd (i, Cn (dm, c, e))) =
    (if ((dm : IntInf.int) = (0 : IntInf.int)) then i else (1 : IntInf.int));

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
  | a_beta (Not ae) = (fn _ => Not ae)
  | a_beta (Imp (aj, ak)) = (fn _ => Imp (aj, ak))
  | a_beta (Iff (al, am)) = (fn _ => Iff (al, am))
  | a_beta (E an) = (fn _ => E an)
  | a_beta (A ao) = (fn _ => A ao)
  | a_beta (Closed ap) = (fn _ => Closed ap)
  | a_beta (NClosed aq) = (fn _ => NClosed aq)
  | a_beta (Lt (Cn (cm, c, e))) =
    (if ((cm : IntInf.int) = (0 : IntInf.int))
      then (fn k =>
             Lt (Cn ((0 : IntInf.int), (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn _ => Lt (Cn (suc (minus_nat cm (1 : IntInf.int)), c, e))))
  | a_beta (Le (Cn (dm, c, e))) =
    (if ((dm : IntInf.int) = (0 : IntInf.int))
      then (fn k =>
             Le (Cn ((0 : IntInf.int), (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn _ => Le (Cn (suc (minus_nat dm (1 : IntInf.int)), c, e))))
  | a_beta (Gt (Cn (em, c, e))) =
    (if ((em : IntInf.int) = (0 : IntInf.int))
      then (fn k =>
             Gt (Cn ((0 : IntInf.int), (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn _ => Gt (Cn (suc (minus_nat em (1 : IntInf.int)), c, e))))
  | a_beta (Ge (Cn (fm, c, e))) =
    (if ((fm : IntInf.int) = (0 : IntInf.int))
      then (fn k =>
             Ge (Cn ((0 : IntInf.int), (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn _ => Ge (Cn (suc (minus_nat fm (1 : IntInf.int)), c, e))))
  | a_beta (Eq (Cn (gm, c, e))) =
    (if ((gm : IntInf.int) = (0 : IntInf.int))
      then (fn k =>
             Eq (Cn ((0 : IntInf.int), (1 : IntInf.int), Mul (div_int k c, e))))
      else (fn _ => Eq (Cn (suc (minus_nat gm (1 : IntInf.int)), c, e))))
  | a_beta (NEq (Cn (hm, c, e))) =
    (if ((hm : IntInf.int) = (0 : IntInf.int))
      then (fn k =>
             NEq (Cn ((0 : IntInf.int), (1 : IntInf.int),
                       Mul (div_int k c, e))))
      else (fn _ => NEq (Cn (suc (minus_nat hm (1 : IntInf.int)), c, e))))
  | a_beta (Dvd (i, Cn (im, c, e))) =
    (if ((im : IntInf.int) = (0 : IntInf.int))
      then (fn k =>
             Dvd (IntInf.* (div_int k c, i),
                   Cn ((0 : IntInf.int), (1 : IntInf.int),
                        Mul (div_int k c, e))))
      else (fn _ => Dvd (i, Cn (suc (minus_nat im (1 : IntInf.int)), c, e))))
  | a_beta (NDvd (i, Cn (jm, c, e))) =
    (if ((jm : IntInf.int) = (0 : IntInf.int))
      then (fn k =>
             NDvd (IntInf.* (div_int k c, i),
                    Cn ((0 : IntInf.int), (1 : IntInf.int),
                         Mul (div_int k c, e))))
      else (fn _ => NDvd (i, Cn (suc (minus_nat jm (1 : IntInf.int)), c, e))));

fun zeta (And (p, q)) = lcm_int (zeta p) (zeta q)
  | zeta (Or (p, q)) = lcm_int (zeta p) (zeta q)
  | zeta T = (1 : IntInf.int)
  | zeta F = (1 : IntInf.int)
  | zeta (Lt (C bo)) = (1 : IntInf.int)
  | zeta (Lt (Bound bp)) = (1 : IntInf.int)
  | zeta (Lt (Neg bt)) = (1 : IntInf.int)
  | zeta (Lt (Add (bu, bv))) = (1 : IntInf.int)
  | zeta (Lt (Sub (bw, bx))) = (1 : IntInf.int)
  | zeta (Lt (Mul (by, bz))) = (1 : IntInf.int)
  | zeta (Le (C co)) = (1 : IntInf.int)
  | zeta (Le (Bound cp)) = (1 : IntInf.int)
  | zeta (Le (Neg ct)) = (1 : IntInf.int)
  | zeta (Le (Add (cu, cv))) = (1 : IntInf.int)
  | zeta (Le (Sub (cw, cx))) = (1 : IntInf.int)
  | zeta (Le (Mul (cy, cz))) = (1 : IntInf.int)
  | zeta (Gt (C doa)) = (1 : IntInf.int)
  | zeta (Gt (Bound dp)) = (1 : IntInf.int)
  | zeta (Gt (Neg dt)) = (1 : IntInf.int)
  | zeta (Gt (Add (du, dv))) = (1 : IntInf.int)
  | zeta (Gt (Sub (dw, dx))) = (1 : IntInf.int)
  | zeta (Gt (Mul (dy, dz))) = (1 : IntInf.int)
  | zeta (Ge (C eo)) = (1 : IntInf.int)
  | zeta (Ge (Bound ep)) = (1 : IntInf.int)
  | zeta (Ge (Neg et)) = (1 : IntInf.int)
  | zeta (Ge (Add (eu, ev))) = (1 : IntInf.int)
  | zeta (Ge (Sub (ew, ex))) = (1 : IntInf.int)
  | zeta (Ge (Mul (ey, ez))) = (1 : IntInf.int)
  | zeta (Eq (C fo)) = (1 : IntInf.int)
  | zeta (Eq (Bound fp)) = (1 : IntInf.int)
  | zeta (Eq (Neg ft)) = (1 : IntInf.int)
  | zeta (Eq (Add (fu, fv))) = (1 : IntInf.int)
  | zeta (Eq (Sub (fw, fx))) = (1 : IntInf.int)
  | zeta (Eq (Mul (fy, fz))) = (1 : IntInf.int)
  | zeta (NEq (C go)) = (1 : IntInf.int)
  | zeta (NEq (Bound gp)) = (1 : IntInf.int)
  | zeta (NEq (Neg gt)) = (1 : IntInf.int)
  | zeta (NEq (Add (gu, gv))) = (1 : IntInf.int)
  | zeta (NEq (Sub (gw, gx))) = (1 : IntInf.int)
  | zeta (NEq (Mul (gy, gz))) = (1 : IntInf.int)
  | zeta (Dvd (aa, C ho)) = (1 : IntInf.int)
  | zeta (Dvd (aa, Bound hp)) = (1 : IntInf.int)
  | zeta (Dvd (aa, Neg ht)) = (1 : IntInf.int)
  | zeta (Dvd (aa, Add (hu, hv))) = (1 : IntInf.int)
  | zeta (Dvd (aa, Sub (hw, hx))) = (1 : IntInf.int)
  | zeta (Dvd (aa, Mul (hy, hz))) = (1 : IntInf.int)
  | zeta (NDvd (ac, C io)) = (1 : IntInf.int)
  | zeta (NDvd (ac, Bound ip)) = (1 : IntInf.int)
  | zeta (NDvd (ac, Neg it)) = (1 : IntInf.int)
  | zeta (NDvd (ac, Add (iu, iv))) = (1 : IntInf.int)
  | zeta (NDvd (ac, Sub (iw, ix))) = (1 : IntInf.int)
  | zeta (NDvd (ac, Mul (iy, iz))) = (1 : IntInf.int)
  | zeta (Not ae) = (1 : IntInf.int)
  | zeta (Imp (aj, ak)) = (1 : IntInf.int)
  | zeta (Iff (al, am)) = (1 : IntInf.int)
  | zeta (E an) = (1 : IntInf.int)
  | zeta (A ao) = (1 : IntInf.int)
  | zeta (Closed ap) = (1 : IntInf.int)
  | zeta (NClosed aq) = (1 : IntInf.int)
  | zeta (Lt (Cn (cm, c, e))) =
    (if ((cm : IntInf.int) = (0 : IntInf.int)) then c else (1 : IntInf.int))
  | zeta (Le (Cn (dm, c, e))) =
    (if ((dm : IntInf.int) = (0 : IntInf.int)) then c else (1 : IntInf.int))
  | zeta (Gt (Cn (em, c, e))) =
    (if ((em : IntInf.int) = (0 : IntInf.int)) then c else (1 : IntInf.int))
  | zeta (Ge (Cn (fm, c, e))) =
    (if ((fm : IntInf.int) = (0 : IntInf.int)) then c else (1 : IntInf.int))
  | zeta (Eq (Cn (gm, c, e))) =
    (if ((gm : IntInf.int) = (0 : IntInf.int)) then c else (1 : IntInf.int))
  | zeta (NEq (Cn (hm, c, e))) =
    (if ((hm : IntInf.int) = (0 : IntInf.int)) then c else (1 : IntInf.int))
  | zeta (Dvd (i, Cn (im, c, e))) =
    (if ((im : IntInf.int) = (0 : IntInf.int)) then c else (1 : IntInf.int))
  | zeta (NDvd (i, Cn (jm, c, e))) =
    (if ((jm : IntInf.int) = (0 : IntInf.int)) then c else (1 : IntInf.int));

fun zsplit0 (C c) = ((0 : IntInf.int), C c)
  | zsplit0 (Bound n) =
    (if ((n : IntInf.int) = (0 : IntInf.int))
      then ((1 : IntInf.int), C (0 : IntInf.int))
      else ((0 : IntInf.int), Bound n))
  | zsplit0 (Cn (n, i, a)) =
    let
      val (ia, aa) = zsplit0 a;
    in
      (if ((n : IntInf.int) = (0 : IntInf.int)) then (IntInf.+ (i, ia), aa)
        else (ia, Cn (n, i, aa)))
    end
  | zsplit0 (Neg a) =
    let
      val (i, aa) = zsplit0 a;
    in
      (IntInf.~ i, Neg aa)
    end
  | zsplit0 (Add (a, b)) =
    let
      val (ia, aa) = zsplit0 a;
      val (ib, ba) = zsplit0 b;
    in
      (IntInf.+ (ia, ib), Add (aa, ba))
    end
  | zsplit0 (Sub (a, b)) =
    let
      val (ia, aa) = zsplit0 a;
      val (ib, ba) = zsplit0 b;
    in
      (IntInf.- (ia, ib), Sub (aa, ba))
    end
  | zsplit0 (Mul (i, a)) =
    let
      val (ia, aa) = zsplit0 a;
    in
      (IntInf.* (i, ia), Mul (i, aa))
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
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Lt r
        else (if IntInf.< ((0 : IntInf.int), c)
               then Lt (Cn ((0 : IntInf.int), c, r))
               else Gt (Cn ((0 : IntInf.int), IntInf.~ c, Neg r))))
    end
  | zlfm (Le a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Le r
        else (if IntInf.< ((0 : IntInf.int), c)
               then Le (Cn ((0 : IntInf.int), c, r))
               else Ge (Cn ((0 : IntInf.int), IntInf.~ c, Neg r))))
    end
  | zlfm (Gt a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Gt r
        else (if IntInf.< ((0 : IntInf.int), c)
               then Gt (Cn ((0 : IntInf.int), c, r))
               else Lt (Cn ((0 : IntInf.int), IntInf.~ c, Neg r))))
    end
  | zlfm (Ge a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Ge r
        else (if IntInf.< ((0 : IntInf.int), c)
               then Ge (Cn ((0 : IntInf.int), c, r))
               else Le (Cn ((0 : IntInf.int), IntInf.~ c, Neg r))))
    end
  | zlfm (Eq a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then Eq r
        else (if IntInf.< ((0 : IntInf.int), c)
               then Eq (Cn ((0 : IntInf.int), c, r))
               else Eq (Cn ((0 : IntInf.int), IntInf.~ c, Neg r))))
    end
  | zlfm (NEq a) =
    let
      val (c, r) = zsplit0 a;
    in
      (if ((c : IntInf.int) = (0 : IntInf.int)) then NEq r
        else (if IntInf.< ((0 : IntInf.int), c)
               then NEq (Cn ((0 : IntInf.int), c, r))
               else NEq (Cn ((0 : IntInf.int), IntInf.~ c, Neg r))))
    end
  | zlfm (Dvd (i, a)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then zlfm (Eq a)
      else let
             val (c, r) = zsplit0 a;
           in
             (if ((c : IntInf.int) = (0 : IntInf.int)) then Dvd (abs_int i, r)
               else (if IntInf.< ((0 : IntInf.int), c)
                      then Dvd (abs_int i, Cn ((0 : IntInf.int), c, r))
                      else Dvd (abs_int i,
                                 Cn ((0 : IntInf.int), IntInf.~ c, Neg r))))
           end)
  | zlfm (NDvd (i, a)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then zlfm (NEq a)
      else let
             val (c, r) = zsplit0 a;
           in
             (if ((c : IntInf.int) = (0 : IntInf.int)) then NDvd (abs_int i, r)
               else (if IntInf.< ((0 : IntInf.int), c)
                      then NDvd (abs_int i, Cn ((0 : IntInf.int), c, r))
                      else NDvd (abs_int i,
                                  Cn ((0 : IntInf.int), IntInf.~ c, Neg r))))
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
  | zlfm (Not (E ci)) = Not (E ci)
  | zlfm (Not (A cj)) = Not (A cj)
  | zlfm (E ao) = E ao
  | zlfm (A ap) = A ap
  | zlfm (Closed aq) = Closed aq
  | zlfm (NClosed ar) = NClosed ar;

fun unita p =
  let
    val pa = zlfm p;
    val l = zeta pa;
    val q =
      And (Dvd (l, Cn ((0 : IntInf.int), (1 : IntInf.int), C (0 : IntInf.int))),
            a_beta pa l);
    val d = delta q;
    val b = remdups eq_numa (map simpnum (beta q));
    val a = remdups eq_numa (map simpnum (alpha q));
  in
    (if IntInf.<= (size_list b, size_list a) then (q, (b, d))
      else (mirror q, (a, d)))
  end;

fun cooper p =
  let
    val (q, (b, d)) = unita p;
    val js = iupt (1 : IntInf.int) d;
    val mq = simpfm (minusinf q);
    val md = evaldjf (fn j => simpfm (subst0 (C j) mq)) js;
  in
    (if eq_fm md T then T
      else let
             val qd =
               evaldjf (fn (ba, j) => simpfm (subst0 (Add (ba, C j)) q))
                 (concat_map (fn ba => map (fn a => (ba, a)) js) b);
           in
             decr (disj md qd)
           end)
  end;

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
  | prep (E (Lt ef)) = E (prep (Lt ef))
  | prep (E (Le eg)) = E (prep (Le eg))
  | prep (E (Gt eh)) = E (prep (Gt eh))
  | prep (E (Ge ei)) = E (prep (Ge ei))
  | prep (E (Eq ej)) = E (prep (Eq ej))
  | prep (E (NEq ek)) = E (prep (NEq ek))
  | prep (E (Dvd (el, em))) = E (prep (Dvd (el, em)))
  | prep (E (NDvd (en, eo))) = E (prep (NDvd (en, eo)))
  | prep (E (Not T)) = E (prep (Not T))
  | prep (E (Not F)) = E (prep (Not F))
  | prep (E (Not (Lt gw))) = E (prep (Not (Lt gw)))
  | prep (E (Not (Le gx))) = E (prep (Not (Le gx)))
  | prep (E (Not (Gt gy))) = E (prep (Not (Gt gy)))
  | prep (E (Not (Ge gz))) = E (prep (Not (Ge gz)))
  | prep (E (Not (Eq ha))) = E (prep (Not (Eq ha)))
  | prep (E (Not (NEq hb))) = E (prep (Not (NEq hb)))
  | prep (E (Not (Dvd (hc, hd)))) = E (prep (Not (Dvd (hc, hd))))
  | prep (E (Not (NDvd (he, hf)))) = E (prep (Not (NDvd (he, hf))))
  | prep (E (Not (Not hg))) = E (prep (Not (Not hg)))
  | prep (E (Not (Or (hj, hk)))) = E (prep (Not (Or (hj, hk))))
  | prep (E (Not (E hp))) = E (prep (Not (E hp)))
  | prep (E (Not (A hq))) = E (prep (Not (A hq)))
  | prep (E (Not (Closed hr))) = E (prep (Not (Closed hr)))
  | prep (E (Not (NClosed hs))) = E (prep (Not (NClosed hs)))
  | prep (E (And (eq, er))) = E (prep (And (eq, er)))
  | prep (E (E ey)) = E (prep (E ey))
  | prep (E (A ez)) = E (prep (A ez))
  | prep (E (Closed fa)) = E (prep (Closed fa))
  | prep (E (NClosed fb)) = E (prep (NClosed fb))
  | prep (A (And (p, q))) = And (prep (A p), prep (A q))
  | prep (A T) = prep (Not (E (Not T)))
  | prep (A F) = prep (Not (E (Not F)))
  | prep (A (Lt jn)) = prep (Not (E (Not (Lt jn))))
  | prep (A (Le jo)) = prep (Not (E (Not (Le jo))))
  | prep (A (Gt jp)) = prep (Not (E (Not (Gt jp))))
  | prep (A (Ge jq)) = prep (Not (E (Not (Ge jq))))
  | prep (A (Eq jr)) = prep (Not (E (Not (Eq jr))))
  | prep (A (NEq js)) = prep (Not (E (Not (NEq js))))
  | prep (A (Dvd (jt, ju))) = prep (Not (E (Not (Dvd (jt, ju)))))
  | prep (A (NDvd (jv, jw))) = prep (Not (E (Not (NDvd (jv, jw)))))
  | prep (A (Not jx)) = prep (Not (E (Not (Not jx))))
  | prep (A (Or (ka, kb))) = prep (Not (E (Not (Or (ka, kb)))))
  | prep (A (Imp (kc, kd))) = prep (Not (E (Not (Imp (kc, kd)))))
  | prep (A (Iff (ke, kf))) = prep (Not (E (Not (Iff (ke, kf)))))
  | prep (A (E kg)) = prep (Not (E (Not (E kg))))
  | prep (A (A kh)) = prep (Not (E (Not (A kh))))
  | prep (A (Closed ki)) = prep (Not (E (Not (Closed ki))))
  | prep (A (NClosed kj)) = prep (Not (E (Not (NClosed kj))))
  | prep (Not (Not p)) = prep p
  | prep (Not (And (p, q))) = Or (prep (Not p), prep (Not q))
  | prep (Not (A p)) = prep (E (Not p))
  | prep (Not (Or (p, q))) = And (prep (Not p), prep (Not q))
  | prep (Not (Imp (p, q))) = And (prep p, prep (Not q))
  | prep (Not (Iff (p, q))) = Or (prep (And (p, Not q)), prep (And (Not p, q)))
  | prep (Not T) = Not (prep T)
  | prep (Not F) = Not (prep F)
  | prep (Not (Lt bo)) = Not (prep (Lt bo))
  | prep (Not (Le bp)) = Not (prep (Le bp))
  | prep (Not (Gt bq)) = Not (prep (Gt bq))
  | prep (Not (Ge br)) = Not (prep (Ge br))
  | prep (Not (Eq bs)) = Not (prep (Eq bs))
  | prep (Not (NEq bt)) = Not (prep (NEq bt))
  | prep (Not (Dvd (bu, bv))) = Not (prep (Dvd (bu, bv)))
  | prep (Not (NDvd (bw, bx))) = Not (prep (NDvd (bw, bx)))
  | prep (Not (E ch)) = Not (prep (E ch))
  | prep (Not (Closed cj)) = Not (prep (Closed cj))
  | prep (Not (NClosed ck)) = Not (prep (NClosed ck))
  | prep (Or (p, q)) = Or (prep p, prep q)
  | prep (And (p, q)) = And (prep p, prep q)
  | prep (Imp (p, q)) = prep (Or (Not p, q))
  | prep (Iff (p, q)) = Or (prep (And (p, q)), prep (And (Not p, Not q)))
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

fun qelim (E p) = (fn qe => dj qe (qelim p qe))
  | qelim (A p) = (fn qe => nota (qe (qelim (Not p) qe)))
  | qelim (Not p) = (fn qe => nota (qelim p qe))
  | qelim (And (p, q)) = (fn qe => conj (qelim p qe) (qelim q qe))
  | qelim (Or (p, q)) = (fn qe => disj (qelim p qe) (qelim q qe))
  | qelim (Imp (p, q)) = (fn qe => impa (qelim p qe) (qelim q qe))
  | qelim (Iff (p, q)) = (fn qe => iffa (qelim p qe) (qelim q qe))
  | qelim T = (fn _ => simpfm T)
  | qelim F = (fn _ => simpfm F)
  | qelim (Lt u) = (fn _ => simpfm (Lt u))
  | qelim (Le v) = (fn _ => simpfm (Le v))
  | qelim (Gt w) = (fn _ => simpfm (Gt w))
  | qelim (Ge x) = (fn _ => simpfm (Ge x))
  | qelim (Eq y) = (fn _ => simpfm (Eq y))
  | qelim (NEq z) = (fn _ => simpfm (NEq z))
  | qelim (Dvd (aa, ab)) = (fn _ => simpfm (Dvd (aa, ab)))
  | qelim (NDvd (ac, ad)) = (fn _ => simpfm (NDvd (ac, ad)))
  | qelim (Closed ap) = (fn _ => simpfm (Closed ap))
  | qelim (NClosed aq) = (fn _ => simpfm (NClosed aq));

fun pa p = qelim (prep p) cooper;

end; (*struct Generated_Cooper*)
