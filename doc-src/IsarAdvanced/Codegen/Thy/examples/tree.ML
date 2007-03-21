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

type 'a eq = {op_eq : 'a -> 'a -> bool};
fun op_eq (A_:'a eq) = #op_eq A_;

end; (*struct Code_Generator*)

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun op_eq_nat Zero_nat (Suc m) = false
  | op_eq_nat (Suc n) Zero_nat = false
  | op_eq_nat (Suc n) (Suc m) = op_eq_nat n m
  | op_eq_nat Zero_nat Zero_nat = true;

val eq_nat = {op_eq = op_eq_nat} : nat Code_Generator.eq;

fun less_nat n (Suc m) = less_eq_nat n m
  | less_nat n Zero_nat = false
and less_eq_nat (Suc n) m = less_nat n m
  | less_eq_nat Zero_nat m = true;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} :
  nat Orderings.ord;

end; (*struct Nat*)

structure List = 
struct

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 |
  Nibble5 | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB |
  NibbleC | NibbleD | NibbleE | NibbleF;

end; (*struct List*)

structure Codegen = 
struct

datatype ('a, 'b) searchtree = Leaf of 'a * 'b |
  Branch of ('a, 'b) searchtree * 'a * ('a, 'b) searchtree;

fun update (A1_, A2_) (it, entry) (Branch (t1, key, t2)) =
  (if Orderings.less_eq A2_ it key
    then Branch (update (A1_, A2_) (it, entry) t1, key, t2)
    else Branch (t1, key, update (A1_, A2_) (it, entry) t2))
  | update (A1_, A2_) (it, entry) (Leaf (key, vala)) =
    (if Code_Generator.op_eq A1_ it key then Leaf (key, entry)
      else (if Orderings.less_eq A2_ it key
             then Branch (Leaf (it, entry), it, Leaf (key, vala))
             else Branch (Leaf (key, vala), it, Leaf (it, entry))));

fun example n =
  update (Nat.eq_nat, Nat.ord_nat) (n, [#"b", #"a", #"r"])
    (Leaf (Nat.Zero_nat, [#"f", #"o", #"o"]));

end; (*struct Codegen*)

end; (*struct ROOT*)
