structure Classes = 
struct

datatype nat = Suc of nat | Zero_nat;

fun nat_aux i n =
  (if IntInf.<= (i, (0 : IntInf.int)) then n
    else nat_aux (IntInf.- (i, (1 : IntInf.int))) (Suc n));

fun nat i = nat_aux i Zero_nat;

type 'a semigroup = {mult : 'a -> 'a -> 'a};
fun mult (A_:'a semigroup) = #mult A_;

type 'a monoidl =
  {Classes__semigroup_monoidl : 'a semigroup, neutral : 'a};
fun semigroup_monoidl (A_:'a monoidl) = #Classes__semigroup_monoidl A_;
fun neutral (A_:'a monoidl) = #neutral A_;

type 'a monoid = {Classes__monoidl_monoid : 'a monoidl};
fun monoidl_monoid (A_:'a monoid) = #Classes__monoidl_monoid A_;

type 'a group = {Classes__monoid_group : 'a monoid, inverse : 'a -> 'a};
fun monoid_group (A_:'a group) = #Classes__monoid_group A_;
fun inverse (A_:'a group) = #inverse A_;

fun inverse_int i = IntInf.~ i;

val neutral_int : IntInf.int = (0 : IntInf.int);

fun mult_int i j = IntInf.+ (i, j);

val semigroup_int = {mult = mult_int} : IntInf.int semigroup;

val monoidl_int =
  {Classes__semigroup_monoidl = semigroup_int, neutral = neutral_int} :
  IntInf.int monoidl;

val monoid_int = {Classes__monoidl_monoid = monoidl_int} :
  IntInf.int monoid;

val group_int =
  {Classes__monoid_group = monoid_int, inverse = inverse_int} :
  IntInf.int group;

fun pow_nat A_ (Suc n) x =
  mult ((semigroup_monoidl o monoidl_monoid) A_) x (pow_nat A_ n x)
  | pow_nat A_ Zero_nat x = neutral (monoidl_monoid A_);

fun pow_int A_ k x =
  (if IntInf.<= ((0 : IntInf.int), k)
    then pow_nat (monoid_group A_) (nat k) x
    else inverse A_ (pow_nat (monoid_group A_) (nat (IntInf.~ k)) x));

val example : IntInf.int =
  pow_int group_int (10 : IntInf.int) (~2 : IntInf.int);

end; (*struct Classes*)
