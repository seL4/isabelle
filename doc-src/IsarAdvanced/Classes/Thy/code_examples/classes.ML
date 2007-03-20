structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

end; (*struct Nat*)

structure Integer = 
struct

fun nat_aux n i =
  (if IntInf.<= (i, (0 : IntInf.int)) then n
    else nat_aux (Nat.Suc n) (IntInf.- (i, (1 : IntInf.int))));

fun nat i = nat_aux Nat.Zero_nat i;

end; (*struct Integer*)

structure Classes = 
struct

type 'a semigroup = {mult : 'a -> 'a -> 'a};
fun mult (A_:'a semigroup) = #mult A_;

type 'a monoidl =
  {Classes__monoidl_semigroup : 'a semigroup, neutral : 'a};
fun monoidl_semigroup (A_:'a monoidl) = #Classes__monoidl_semigroup A_;
fun neutral (A_:'a monoidl) = #neutral A_;

type 'a group = {Classes__group_monoidl : 'a monoidl, inverse : 'a -> 'a};
fun group_monoidl (A_:'a group) = #Classes__group_monoidl A_;
fun inverse (A_:'a group) = #inverse A_;

fun inverse_int i = IntInf.~ i;

val neutral_int : IntInf.int = (0 : IntInf.int);

fun mult_int i j = IntInf.+ (i, j);

val semigroup_int = {mult = mult_int} : IntInf.int semigroup;

val monoidl_int =
  {Classes__monoidl_semigroup = semigroup_int, neutral = neutral_int} :
  IntInf.int monoidl;

val group_int =
  {Classes__group_monoidl = monoidl_int, inverse = inverse_int} :
  IntInf.int group;

fun pow_nat A_ (Nat.Suc n) x =
  mult (monoidl_semigroup A_) x (pow_nat A_ n x)
  | pow_nat A_ Nat.Zero_nat x = neutral A_;

fun pow_int A_ k x =
  (if IntInf.<= ((0 : IntInf.int), k)
    then pow_nat (group_monoidl A_) (Integer.nat k) x
    else inverse A_
           (pow_nat (group_monoidl A_) (Integer.nat (IntInf.~ k)) x));

val example : IntInf.int =
  pow_int group_int (10 : IntInf.int) (~2 : IntInf.int);

end; (*struct Classes*)

end; (*struct ROOT*)
