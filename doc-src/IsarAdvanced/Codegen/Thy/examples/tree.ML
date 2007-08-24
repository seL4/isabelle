structure HOL = 
struct

type 'a eq = {eqop : 'a -> 'a -> bool};
fun eqop (A_:'a eq) = #eqop A_;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
fun less_eq (A_:'a ord) = #less_eq A_;
fun less (A_:'a ord) = #less A_;

end; (*struct HOL*)

structure Orderings = 
struct

type 'a order = {Orderings__ord_order : 'a HOL.ord};
fun ord_order (A_:'a order) = #Orderings__ord_order A_;

type 'a linorder = {Orderings__order_linorder : 'a order};
fun order_linorder (A_:'a linorder) = #Orderings__order_linorder A_;

end; (*struct Orderings*)

structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

fun eqop_nat Zero_nat (Suc m) = false
  | eqop_nat (Suc n) Zero_nat = false
  | eqop_nat (Suc n) (Suc m) = eqop_nat n m
  | eqop_nat Zero_nat Zero_nat = true;

val eq_nat = {eqop = eqop_nat} : nat HOL.eq;

fun less_nat n (Suc m) = less_eq_nat n m
  | less_nat n Zero_nat = false
and less_eq_nat (Suc n) m = less_nat n m
  | less_eq_nat Zero_nat m = true;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat HOL.ord;

val order_nat = {Orderings__ord_order = ord_nat} : nat Orderings.order;

val linorder_nat = {Orderings__order_linorder = order_nat} :
  nat Orderings.linorder;

end; (*struct Nat*)

structure Codegen = 
struct

datatype ('a, 'b) searchtree =
  Branch of ('a, 'b) searchtree * 'a * ('a, 'b) searchtree |
  Leaf of 'a * 'b;

fun update (C1_, C2_) (it, entry) (Branch (t1, key, t2)) =
  (if HOL.less_eq ((Orderings.ord_order o Orderings.order_linorder) C2_)
        it key
    then Branch (update (C1_, C2_) (it, entry) t1, key, t2)
    else Branch (t1, key, update (C1_, C2_) (it, entry) t2))
  | update (C1_, C2_) (it, entry) (Leaf (key, vala)) =
    (if HOL.eqop C1_ it key then Leaf (key, entry)
      else (if HOL.less_eq
                 ((Orderings.ord_order o Orderings.order_linorder) C2_) it
                 key
             then Branch (Leaf (it, entry), it, Leaf (key, vala))
             else Branch (Leaf (key, vala), it, Leaf (it, entry))));

val example : (Nat.nat, (Nat.nat list)) searchtree =
  update (Nat.eq_nat, Nat.linorder_nat)
    (Nat.Suc (Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat))),
      [Nat.Suc (Nat.Suc Nat.Zero_nat), Nat.Suc (Nat.Suc Nat.Zero_nat)])
    (update (Nat.eq_nat, Nat.linorder_nat)
      (Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat)),
        [Nat.Suc (Nat.Suc (Nat.Suc Nat.Zero_nat))])
      (update (Nat.eq_nat, Nat.linorder_nat)
        (Nat.Suc (Nat.Suc Nat.Zero_nat), [Nat.Suc (Nat.Suc Nat.Zero_nat)])
        (Leaf (Nat.Suc Nat.Zero_nat, []))));

end; (*struct Codegen*)
