structure ROOT = 
struct

structure HOL = 
struct

type 'a eq = {eq : 'a -> 'a -> bool};
fun eq (A_:'a eq) = #eq A_;

end; (*struct HOL*)

structure Orderings = 
struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
fun less_eq (A_:'a ord) = #less_eq A_;
fun less (A_:'a ord) = #less A_;

type 'a order = {Orderings__order_ord : 'a ord};
fun order_ord (A_:'a order) = #Orderings__order_ord A_;

type 'a linorder = {Orderings__linorder_order : 'a order};
fun linorder_order (A_:'a linorder) = #Orderings__linorder_order A_;

end; (*struct Orderings*)

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

fun eq_nat Zero_nat (Suc m) = false
  | eq_nat (Suc n) Zero_nat = false
  | eq_nat (Suc n) (Suc m) = eq_nat n m
  | eq_nat Zero_nat Zero_nat = true;

val eq_nata = {eq = eq_nat} : nat HOL.eq;

fun less_nat n (Suc m) = less_eq_nat n m
  | less_nat n Zero_nat = false
and less_eq_nat (Suc n) m = less_nat n m
  | less_eq_nat Zero_nat m = true;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} :
  nat Orderings.ord;

val order_nat = {Orderings__order_ord = ord_nat} : nat Orderings.order;

val linorder_nat = {Orderings__linorder_order = order_nat} :
  nat Orderings.linorder;

end; (*struct Nat*)

structure Codegen = 
struct

datatype ('a, 'b) searchtree = Leaf of 'a * 'b |
  Branch of ('a, 'b) searchtree * 'a * ('a, 'b) searchtree;

fun update (C1_, C2_) (it, entry) (Branch (t1, key, t2)) =
  (if Orderings.less_eq
        ((Orderings.order_ord o Orderings.linorder_order) C2_) it key
    then Branch (update (C1_, C2_) (it, entry) t1, key, t2)
    else Branch (t1, key, update (C1_, C2_) (it, entry) t2))
  | update (C1_, C2_) (it, entry) (Leaf (key, vala)) =
    (if HOL.eq C1_ it key then Leaf (key, entry)
      else (if Orderings.less_eq
                 ((Orderings.order_ord o Orderings.linorder_order) C2_) it
                 key
             then Branch (Leaf (it, entry), it, Leaf (key, vala))
             else Branch (Leaf (key, vala), it, Leaf (it, entry))));

val example : (Nat.nat, (Nat.nat list)) searchtree =
  update (Nat.eq_nata, Nat.linorder_nat)
    (Nat.Suc (Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat))),
      [Nat.Suc (Nat.Suc Nat.Zero_nat), Nat.Suc (Nat.Suc Nat.Zero_nat)])
    (update (Nat.eq_nata, Nat.linorder_nat)
      (Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat)),
        [Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat))])
      (update (Nat.eq_nata, Nat.linorder_nat)
        (Nat.Suc (Nat.Suc Nat.Zero_nat), [Nat.Suc (Nat.Suc Nat.Zero_nat)])
        (Leaf (Nat.Suc Nat.Zero_nat, []))));

end; (*struct Codegen*)

end; (*struct ROOT*)
