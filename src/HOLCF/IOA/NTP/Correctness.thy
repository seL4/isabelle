(*  Title:      HOL/IOA/NTP/Correctness.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The main correctness proof: Impl implements Spec.
*)

Correctness = Impl + Spec +

constdefs

  hom :: 'm impl_state => 'm list
  "hom(s) == rq(rec(s)) @ (if rbit(rec s) = sbit(sen s) then sq(sen s) 
                           else tl(sq(sen s)))"

end
