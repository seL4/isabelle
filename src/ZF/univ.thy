(*  Title: 	ZF/univ.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The cumulative hierarchy and a small universe for recursive types

Standard notation for Vset(i) is V(i), but users might want V for a variable
*)

Univ = Arith + Sum +
consts
    Limit       ::      "i=>o"
    Vfrom       ::      "[i,i]=>i"
    Vset        ::      "i=>i"
    Vrec        ::      "[i, [i,i]=>i] =>i"
    univ        ::      "i=>i"

translations
  (*Apparently a bug prevents using "Vset" == "Vfrom(0)" *)
    "Vset(x)"   == 	"Vfrom(0,x)"

rules
    Limit_def   "Limit(i) == Ord(i) & 0:i & (ALL y:i. succ(y): i)"

    Vfrom_def   "Vfrom(A,i) == transrec(i, %x f. A Un (UN y:x. Pow(f`y)))"

    Vrec_def
   	"Vrec(a,H) == transrec(rank(a), %x g. lam z: Vset(succ(x)).      \
\                             H(z, lam w:Vset(x). g`rank(w)`w)) ` a"

    univ_def    "univ(A) == Vfrom(A,nat)"

end
