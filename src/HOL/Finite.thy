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

constdefs

  finite :: 'a set => bool
  "finite A == A : Fin(UNIV)"

  card :: 'a set => nat
  "card A == LEAST n. ? f. A = {f i |i. i<n}"

end
