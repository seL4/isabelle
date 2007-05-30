structure ROOT = 
struct

structure Orderings = 
struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
fun less_eq (A_:'a ord) = #less_eq A_;
fun less (A_:'a ord) = #less A_;

end; (*struct Orderings*)

structure Code_Generator = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

end; (*struct Code_Generator*)

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun eq_nat Zero_nat (Suc m) = false
  | eq_nat (Suc n) Zero_nat = false
  | eq_nat (Suc n) (Suc m) = eq_nat n m
  | eq_nat Zero_nat Zero_nat = true;

val eq_nata = {eq = eq_nat} : nat Code_Generator.eq;

fun less_nat n (Suc m) = less_eq_nat n m
  | less_nat n Zero_nat = false
and less_eq_nat (Suc n) m = less_nat n m
  | less_eq_nat Zero_nat m = true;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} :
  nat Orderings.ord;

end; (*struct Nat*)

structure Codegen = 
struct

datatype ('a, 'b) searchtree = Leaf of 'a * 'b |
  Branch of ('a, 'b) searchtree * 'a * ('a, 'b) searchtree;

fun update (C1_, C2_) (it, entry) (Branch (t1, key, t2)) =
  (if Orderings.less_eq C2_ it key
    then Branch (update (C1_, C2_) (it, entry) t1, key, t2)
    else Branch (t1, key, update (C1_, C2_) (it, entry) t2))
  | update (C1_, C2_) (it, entry) (Leaf (key, vala)) =
    (if Code_Generator.eq C1_ it key then Leaf (key, entry)
      else (if Orderings.less_eq C2_ it key
             then Branch (Leaf (it, entry), it, Leaf (key, vala))
             else Branch (Leaf (key, vala), it, Leaf (it, entry))));

val example : (Nat.nat, (Nat.nat list)) searchtree =
  update (Nat.eq_nata, Nat.ord_nat)
    (Nat.Suc (Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat))),
      [Nat.Suc (Nat.Suc Nat.Zero_nat), Nat.Suc (Nat.Suc Nat.Zero_nat)])
    (update (Nat.eq_nata, Nat.ord_nat)
      (Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat)),
        [Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat))])
      (update (Nat.eq_nata, Nat.ord_nat)
        (Nat.Suc (Nat.Suc Nat.Zero_nat), [Nat.Suc (Nat.Suc Nat.Zero_nat)])
        (Leaf (Nat.Suc Nat.Zero_nat, []))));

end; (*struct Codegen*)

end; (*struct ROOT*)
