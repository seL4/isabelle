(*  Title:      HOL/While
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen

Defines a while-combinator "while" and proves
a) an unrestricted unfolding law (even if while diverges!)
   (I got this idea from Wolfgang Goerigk)
b) the invariant rule for reasoning about while
*)

While = Recdef +

consts while_aux :: "('a => bool) * ('a => 'a) * 'a => 'a"
recdef while_aux
 "same_fst (%b. True) (%b. same_fst (%c. True) (%c.
  {(t,s).  b s & c s = t &
           ~(? f. f 0 = s & (!i. b(f i) & c(f i) = f(i+1)))}))"
"while_aux(b,c,s) =
  (if (? f. f 0 = s & (!i. b(f i) & c(f i) = f(i+1)))
   then arbitrary
   else if b s then while_aux(b,c,c s) else s)"

constdefs
 while :: "('a => bool) => ('a => 'a) => 'a => 'a"
"while b c s == while_aux(b,c,s)"

end
