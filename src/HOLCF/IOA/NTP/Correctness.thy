(*  Title:      HOL/IOA/NTP/Correctness.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The main correctness proof: Impl implements Spec
*)

Correctness = IOA + Impl + Spec +

constdefs

  hom :: 'm impl_state => 'm list
  "hom(s) == rq(rec(s)) @ (if rbit(rec s) = sbit(sen s) then sq(sen s) 
                          else ttl(sq(sen s)))"

end
