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
   "ex_prop X == ALL F G. F:X | G: X --> (Join F G) : X"

  strict_ex_prop  :: 'a program set => bool
   "strict_ex_prop X == ALL F G. (F:X | G: X) = (Join F G : X)"

  uv_prop  :: 'a program set => bool
   "uv_prop X == SKIP: X & (ALL F G. F:X & G: X --> (Join F G) : X)"

  strict_uv_prop  :: 'a program set => bool
   "strict_uv_prop X == SKIP: X & (ALL F G. (F:X & G: X) = (Join F G : X))"

  compatible :: ['a program, 'a program] => bool
   "compatible F G == Init F Int Init G ~= {}"

  component :: ['a program, 'a program] => bool
   "component F H == EX G. Join F G = H"

  guarantees :: ['a program set, 'a program set] => 'a program set (infixl 65)
   "X guarantees Y == {F. ALL H. component F H --> H:X --> H:Y}"

end
