(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition

From Chandy and Sanders, "Reasoning About Program Composition"

QUESTIONS:
  refines_def: needs the States F = States G?

  uv_prop, component: should be States F = States (F Join G)
*)

Comp = Union +

constdefs

  (*Existential and Universal properties.  I formalize the two-program
    case, proving equivalence with Chandy and Sanders's n-ary definitions*)

  ex_prop  :: 'a program set => bool
   "ex_prop X ==
      ALL F G. (F:X | G: X) & States F = States G --> (F Join G) : X"

  strict_ex_prop  :: 'a program set => bool
   "strict_ex_prop X ==
      ALL F G. States F = States G --> (F:X | G: X) = (F Join G : X)"

  uv_prop  :: 'a program set => bool
   "uv_prop X ==
      SKIP UNIV : X &
      (ALL F G. F:X & G: X & States F = States G --> (F Join G) : X)"

  strict_uv_prop  :: 'a program set => bool
   "strict_uv_prop X ==
      SKIP UNIV : X &
      (ALL F G. States F = States G --> (F:X & G: X) = (F Join G : X))"

  (*Ill-defined programs can arise through "Join"*)
  welldef :: 'a program set  
   "welldef == {F. Init F ~= {}}"

  component :: ['a program, 'a program] => bool
   "component F H == EX G. F Join G = H & States F = States G"

  guarantees :: ['a program set, 'a program set] => 'a program set (infixl 65)
   "X guarantees Y == {F. ALL H. component F H --> H:X --> H:Y}"

  refines :: ['a program, 'a program, 'a program set] => bool
			("(3_ refines _ wrt _)" [10,10,10] 10)
   "G refines F wrt X ==
      States F = States G &
      (ALL H. States F = States H & (F Join H) : welldef Int X
        --> G Join H : welldef Int X)"

  iso_refines :: ['a program, 'a program, 'a program set] => bool
			("(3_ iso'_refines _ wrt _)" [10,10,10] 10)
   "G iso_refines F wrt X ==
      F : welldef Int X --> G : welldef Int X"

end
