(*  Title:      HOL/Relation_Power.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

R^n = R O ... O R, the n-fold composition of R
Both for functions and relations.
*)

Relation_Power = Nat +

instance
  set :: (term) {power}   (* only ('a * 'a) set should be in power! *)

primrec (relpow)
  "R^0 = Id"
  "R^(Suc n) = R O (R^n)"


instance fun :: (term,term)power   (* only 'a \<Rightarrow> 'a should be in power! *)

primrec (funpow)
  "f^0 = id"
  "f^(Suc n) = f o (f^n)"

end
