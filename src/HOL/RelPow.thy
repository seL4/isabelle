(*  Title:      HOL/RelPow.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

R^n = R O ... O R, the n-fold composition of R
*)

RelPow = Nat +

consts
  "^" :: "('a * 'a) set => nat => ('a * 'a) set" (infixr 100)
defs
  rel_pow_def "R^n == nat_rec id (%m S. R O S) n"
end
