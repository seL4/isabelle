(*  Title:      HOL/UNITY/Guar.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition"
*)

Guar = Comp +

instance program :: (term) order
                    (component_refl, component_trans, component_antisym,
                     program_less_le)

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

  guar :: ['a program set, 'a=>'b, 'a program set] => 'a program set
   ("(_/ guarantees[_]/ _)" [55,0,55] 55)
                              (*higher than membership, lower than Co*)
   "X guarantees[v] Y == {F. ALL G : preserves v. 
                               F Join G : X --> F Join G : Y}"

  refines :: ['a program, 'a program, 'a program set] => bool
			("(3_ refines _ wrt _)" [10,10,10] 10)
   "G refines F wrt X ==
      ALL H. (F Join H) : welldef Int X --> G Join H : welldef Int X"

  iso_refines :: ['a program, 'a program, 'a program set] => bool
			("(3_ iso'_refines _ wrt _)" [10,10,10] 10)
   "G iso_refines F wrt X ==
      F : welldef Int X --> G : welldef Int X"

end
