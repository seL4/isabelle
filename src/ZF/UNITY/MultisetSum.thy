(*  Title:      ZF/UNITY/MultusetSum.thy
    ID:         $Id$
    Author:     Sidi O Ehmety

Setsum for multisets.
*)

MultisetSum = Multiset +
constdefs

  lcomm :: "[i, i, [i,i]=>i]=>o"
  "lcomm(A, B, f) ==
   (ALL x:A. ALL y:A. ALL z:B. f(x, f(y, z))= f(y, f(x, z)))  &
   (ALL x:A. ALL y:B. f(x, y):B)"

  general_setsum :: "[i,i,i, [i,i]=>i, i=>i] =>i"
   "general_setsum(C, B, e, f, g) ==
    if Finite(C) then fold[cons(e, B)](%x y. f(g(x), y), e, C) else e"

  msetsum :: "[i=>i, i, i]=>i"
  "msetsum(g, C, B) == normalize(general_setsum(C, Mult(B), 0, op +#, g))"

  (* sum for naturals *)
  nsetsum :: "[i=>i, i] =>i"
  "nsetsum(g, C) == general_setsum(C, nat, 0, op #+, g)"
end