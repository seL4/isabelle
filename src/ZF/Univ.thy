(*  Title:      ZF/univ.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The cumulative hierarchy and a small universe for recursive types

Standard notation for Vset(i) is V(i), but users might want V for a variable

NOTE: univ(A) could be a translation; would simplify many proofs!
  But Ind_Syntax.univ refers to the constant "univ"
*)

Univ = Arith + Sum + Finite + "mono" +
consts
    Vfrom       :: [i,i]=>i
    Vset        :: i=>i
    Vrec        :: [i, [i,i]=>i] =>i
    univ        :: i=>i

translations
    "Vset(x)"   ==      "Vfrom(0,x)"

defs
    Vfrom_def   "Vfrom(A,i) == transrec(i, %x f. A Un (UN y:x. Pow(f`y)))"

    Vrec_def
        "Vrec(a,H) == transrec(rank(a), %x g. lam z: Vset(succ(x)).      
                             H(z, lam w:Vset(x). g`rank(w)`w)) ` a"

    univ_def    "univ(A) == Vfrom(A,nat)"

end
