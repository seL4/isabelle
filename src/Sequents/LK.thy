(*  Title:      LK/LK
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Axiom to express monotonicity (a variant of the deduction theorem).  Makes the
link between |- and ==>, needed for instance to prove imp_cong.

Axiom left_cong allows the simplifier to use left-side formulas.  Ideally it
should be derived from lower-level axioms.

CANNOT be added to LK0.thy because modal logic is built upon it, and
various modal rules would become inconsistent.
*)

LK = LK0 +

rules

  monotonic  "($H |- P ==> $H |- Q) ==> $H, P |- Q"

  left_cong  "[| P == P';  |- P' ==> ($H |- $F) == ($H' |- $F') |] 
              ==> (P, $H |- $F) == (P', $H' |- $F')"
end
