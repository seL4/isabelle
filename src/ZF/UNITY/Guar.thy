(*  Title:      ZF/UNITY/Guar.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January 2001

Added: Compatibility, weakest guarantees, etc.

and Weakest existential property,
from Charpentier and Chandy "Theorems about Composition",
Fifth International Conference on Mathematics of Program, 2000.

Theory ported from HOL.
*)
Guar = Comp +
constdefs

  (*Existential and Universal properties.  I formalize the two-program
    case, proving equivalence with Chandy and Sanders's n-ary definitions*)

   ex_prop :: i =>o
   "ex_prop(X) == X<=program &
    (ALL F:program. ALL G:program. F ok G --> F:X | G:X --> (F Join G):X)"

  strict_ex_prop  :: i => o
  "strict_ex_prop(X) == X<=program &
   (ALL F:program. ALL  G:program. F ok G --> (F:X | G: X) <-> (F Join G : X))"

  uv_prop  :: i => o
   "uv_prop(X) == X<=program &
    (SKIP:X & (ALL F:program. ALL G:program. F ok G --> F:X & G:X --> (F Join G):X))"
  
 strict_uv_prop  :: i => o
   "strict_uv_prop(X) == X<=program &
    (SKIP:X & (ALL F:program. ALL G:program. F ok G -->(F:X & G:X) <-> (F Join G:X)))"

  guar :: [i, i] => i (infixl "guarantees" 55)
              (*higher than membership, lower than Co*)
  "X guarantees Y == {F:program. ALL G:program. F ok G --> F Join G : X --> F Join G:Y}"
  
  (* Weakest guarantees *)
   wg :: [i,i] => i
  "wg(F,Y) == Union({X:Pow(program). F:(X guarantees Y)})"

  (* Weakest existential property stronger than X *)
   wx :: "i =>i"
   "wx(X) == Union({Y:Pow(program). Y<=X & ex_prop(Y)})"

  (*Ill-defined programs can arise through "Join"*)
  welldef :: i
  "welldef == {F:program. Init(F) ~= 0}"
  
  refines :: [i, i, i] => o ("(3_ refines _ wrt _)" [10,10,10] 10)
  "G refines F wrt X ==
   ALL H:program. (F ok H  & G ok H & F Join H:welldef Int X)
    --> (G Join H:welldef Int X)"

  iso_refines :: [i,i, i] => o  ("(3_ iso'_refines _ wrt _)" [10,10,10] 10)
  "G iso_refines F wrt X ==  F:welldef Int X --> G:welldef Int X"

end
