(*  Title:      HOL/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson & Tobias Nipkow
    Copyright   1995  University of Cambridge & TU Muenchen

Finite sets and their cardinality
*)

Finite = Arith +

consts Fin :: 'a set => 'a set set

inductive "Fin(A)"
  intrs
    emptyI  "{} : Fin(A)"
    insertI "[| a: A;  b: Fin(A) |] ==> insert a b : Fin(A)"

consts finite :: 'a set => bool
defs finite_def "finite A == A : Fin(UNIV)"

consts card :: 'a set => nat
defs card_def "card A == LEAST n. ? f. A = {f i |i. i<n}"

end
