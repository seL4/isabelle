(*
Conversion of automata into regular sets.
use_thy"Auto";
*)

Regset_of_auto = List +

(* autos *)

types 'a auto = "'a => nat => nat"

consts deltas :: 'a auto => 'a list => nat => nat
primrec deltas list
"deltas A [] i = i"
"deltas A (x#xs) i = deltas A xs (A x i)"

consts trace :: 'a auto => nat => 'a list => nat list
primrec trace list
"trace A i [] = []"
"trace A i (x#xs) = A x i # trace A (A x i) xs"

(* regular sets *)

constdefs conc :: 'a list set => 'a list set => 'a list set
         "conc A B == {xs@ys | xs ys. xs:A & ys:B}"

consts star :: 'a list set => 'a list set
inductive "star A"
intrs
  NilI   "[] : star A"
  ConsI  "[| a:A; as : star A |] ==> a@as : star A"

(* conversion a la Warshall *)

consts regset_of :: 'a auto => nat => nat => nat => 'a list set
primrec regset_of nat
"regset_of A i j 0 = (if i=j then insert [] {[a] | a. A a i = j}
                             else {[a] | a. A a i = j})"
"regset_of A i j (Suc k) = regset_of A i j k Un
                           conc (regset_of A i k k)
                          (conc (star(regset_of A k k k))
                                (regset_of A k j k))"

end
