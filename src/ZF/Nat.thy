(*  Title:      ZF/Nat.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Natural numbers in Zermelo-Fraenkel Set Theory 
*)

Nat = OrdQuant + Bool + mono +
consts
    nat         ::      i
    nat_case    ::      [i, i=>i, i]=>i
    nat_rec     ::      [i, i, [i,i]=>i]=>i

defs

    nat_def     "nat == lfp(Inf, %X. {0} Un {succ(i). i:X})"

    nat_case_def
        "nat_case(a,b,k) == THE y. k=0 & y=a | (EX x. k=succ(x) & y=b(x))"

    nat_rec_def
        "nat_rec(k,a,b) ==   
          wfrec(Memrel(nat), k, %n f. nat_case(a, %m. b(m, f`m), n))"

end
