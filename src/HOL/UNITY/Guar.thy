(*  Title:      HOL/UNITY/Guar.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January 2001

Added: Compatibility, weakest guarantees, etc.

and Weakest existential property,
from Charpentier and Chandy "Theorems about Composition",
Fifth International Conference on Mathematics of Program, 2000.

*)

Guar = Comp +

instance program :: (type) order
                    (component_refl, component_trans, component_antisym,
                     program_less_le)

constdefs

  (*Existential and Universal properties.  I formalize the two-program
    case, proving equivalence with Chandy and Sanders's n-ary definitions*)

  ex_prop  :: 'a program set => bool
   "ex_prop X == ALL F G. F ok G -->F:X | G: X --> (F Join G) : X"

  strict_ex_prop  :: 'a program set => bool
   "strict_ex_prop X == ALL F G.  F ok G --> (F:X | G: X) = (F Join G : X)"

  uv_prop  :: 'a program set => bool
   "uv_prop X == SKIP : X & (ALL F G. F ok G --> F:X & G: X --> (F Join G) : X)"

  strict_uv_prop  :: 'a program set => bool
   "strict_uv_prop X == SKIP : X & (ALL F G. F ok G -->(F:X & G: X) = (F Join G : X))"

  guar :: ['a program set, 'a program set] => 'a program set
          (infixl "guarantees" 55)  (*higher than membership, lower than Co*)
   "X guarantees Y == {F. ALL G. F ok G --> F Join G : X --> F Join G : Y}"
  

  (* Weakest guarantees *)
   wg :: ['a program, 'a program set] =>  'a program set
  "wg F Y == Union({X. F:X guarantees Y})"

   (* Weakest existential property stronger than X *)
   wx :: "('a program) set => ('a program)set"
   "wx X == Union({Y. Y<=X & ex_prop Y})"
  
  (*Ill-defined programs can arise through "Join"*)
  welldef :: 'a program set  
  "welldef == {F. Init F ~= {}}"
  
  refines :: ['a program, 'a program, 'a program set] => bool
			("(3_ refines _ wrt _)" [10,10,10] 10)
  "G refines F wrt X ==
   ALL H. (F ok H  & G ok H & F Join H:welldef Int X) --> (G Join H:welldef Int X)"

  iso_refines :: ['a program, 'a program, 'a program set] => bool
                              ("(3_ iso'_refines _ wrt _)" [10,10,10] 10)
  "G iso_refines F wrt X ==
   F : welldef Int X --> G : welldef Int X"

end
