structure Nat = 
struct

datatype nat = Dig1 of nat | Dig0 of nat | One_nat | Zero_nat;

fun plus_nat (Dig1 m) (Dig1 n) = Dig0 (plus_nat (plus_nat m n) One_nat)
  | plus_nat (Dig1 m) (Dig0 n) = Dig1 (plus_nat m n)
  | plus_nat (Dig0 m) (Dig1 n) = Dig1 (plus_nat m n)
  | plus_nat (Dig0 m) (Dig0 n) = Dig0 (plus_nat m n)
  | plus_nat (Dig1 m) One_nat = Dig0 (plus_nat m One_nat)
  | plus_nat One_nat (Dig1 n) = Dig0 (plus_nat n One_nat)
  | plus_nat (Dig0 m) One_nat = Dig1 m
  | plus_nat One_nat (Dig0 n) = Dig1 n
  | plus_nat m Zero_nat = m
  | plus_nat Zero_nat n = n;

end; (*struct Nat*)
