(*  Title:      ZF/UNITY/Increasing
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

The "Increasing" relation of Charpentier.

Increasing's parameters are a state function f, a domain A and an order
relation r over the domain A. 
*)

Increasing = Constrains + Monotonicity +
constdefs

  part_order :: [i, i] => o
  "part_order(A, r) == refl(A,r) & trans[A](r) & antisym(r)"

  increasing :: [i, i, i=>i] => i ("increasing[_]'(_, _')")
  "increasing[A](r, f) ==
    {F:program. (ALL k:A. F: stable({s:state. <k, f(s)>:r})) &
                (ALL x:state. f(x):A)}"
  
  Increasing :: [i, i, i=>i] => i ("Increasing[_]'(_, _')")
  "Increasing[A](r, f) ==
    {F:program. (ALL k:A. F:Stable({s:state. <k, f(s)>:r})) &
                (ALL x:state. f(x):A)}"

syntax
  IncWrt      ::  [i=>i, i, i] => i ("(_ IncreasingWrt _ '/ _)" [60, 0, 60] 60)

translations
  "IncWrt(f,r,A)" => "Increasing[A](r,f)"

  
end
