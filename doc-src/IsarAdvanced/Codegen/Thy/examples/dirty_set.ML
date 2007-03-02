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

structure Codegen = 
struct

val dummy_set : (Nat.nat -> Nat.nat) list = Nat.Suc :: [];

val foobar_set : Nat.nat list =
  Nat.Zero_nat ::
    (Nat.Suc Nat.Zero_nat :: (Integer.nat (2 : IntInf.int) :: []));

end; (*struct Codegen*)

end; (*struct ROOT*)
