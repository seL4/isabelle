(*  Title:      HOL/UNITY/Comp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Composition

From Chandy and Sanders, "Reasoning About Program Composition"
*)

Comp = Union +

constdefs

  (*Existential and Universal properties.  I formalize the two-program
    case, proving equivalence with Chandy and Sanders's n-ary definitions*)

  ex_prop  :: 'a program set => bool
   "ex_prop X == ALL F G. F:X | G: X --> (F Join G) : X"

  strict_ex_prop  :: 'a program set => bool
   "strict_ex_prop X == ALL F G. (F:X | G: X) = (F Join G : X)"

  uv_prop  :: 'a program set => bool
   "uv_prop X == SKIP : X & (ALL F G. F:X & G: X --> (F Join G) : X)"

  strict_uv_prop  :: 'a program set => bool
   "strict_uv_prop X == SKIP : X & (ALL F G. (F:X & G: X) = (F Join G : X))"

  (*Ill-defined programs can arise through "Join"*)
  welldef :: 'a program set  
   "welldef == {F. Init F ~= {}}"

  component :: ['a program, 'a program] => bool     (infixl 50)
   "F component H == EX G. F Join G = H"

  guarantees :: ['a program set, 'a program set] => 'a program set
                                                    (infixl "guar" 65)
   "X guar Y == {F. ALL H. F component H --> H:X --> H:Y}"

  refines :: ['a program, 'a program, 'a program set] => bool
			("(3_ refines _ wrt _)" [10,10,10] 10)
   "G refines F wrt X ==
      ALL H. (F Join H) : welldef Int X --> G Join H : welldef Int X"

  iso_refines :: ['a program, 'a program, 'a program set] => bool
			("(3_ iso'_refines _ wrt _)" [10,10,10] 10)
   "G iso_refines F wrt X ==
      F : welldef Int X --> G : welldef Int X"

end
