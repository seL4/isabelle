structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

end; (*struct Nat*)

structure Codegen = 
struct

val dummy_set : (Nat.nat -> Nat.nat) list = Nat.Suc :: [];

val foobar_set : Nat.nat list =
  Nat.Zero_nat ::
    (Nat.Suc Nat.Zero_nat :: (Nat.Suc (Nat.Suc Nat.Zero_nat) :: []));

end; (*struct Codegen*)

end; (*struct ROOT*)
