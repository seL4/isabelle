(*  Title:      HOL/RelPow.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

R^n = R O ... O R, the n-fold composition of R
*)

RelPow = Nat +

primrec "op ^" nat
  "R^0 = id"
  "R^(Suc n) = R O (R^n)"

end
