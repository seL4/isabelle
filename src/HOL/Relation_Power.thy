(*  Title:      HOL/Relation_Power.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

R^n = R O ... O R, the n-fold composition of R
f^n = f o ... o f, the n-fold composition of f

WARNING: due to the limits of Isabelle's type classes, ^ on functions and
relations has too general a domain, namely ('a * 'b)set and 'a => 'b.
This means that it may be necessary to attach explicit type constraints.
Examples: range(f^n) = A and Range(R^n) = B need constraints.
*)

Relation_Power = Nat +

instance
  set :: (term) {power}   (* only ('a * 'a) set should be in power! *)

primrec (relpow)
  "R^0 = Id"
  "R^(Suc n) = R O (R^n)"


instance
  fun :: (term,term)power   (* only 'a => 'a should be in power! *)

primrec (funpow)
  "f^0 = id"
  "f^(Suc n) = f o (f^n)"

end
