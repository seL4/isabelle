(*  Title:      FOLP/FOLP.thy
    ID:         $Id$
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Classical First-Order Logic with Proofs
*)

FOLP = IFOLP +
consts
  cla :: "[p=>p]=>p"
rules
  classical "(!!x.x:~P ==> f(x):P) ==> cla(f):P"
end
