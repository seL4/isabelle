(*  Title:      HOL/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson & Tobias Nipkow
    Copyright   1995  University of Cambridge & TU Muenchen

Finite sets and their cardinality
*)

Finite = Divides + Power + 

consts Finites :: 'a set set

inductive "Finites"
  intrs
    emptyI  "{} : Finites"
    insertI "A : Finites ==> insert a A : Finites"

syntax finite :: 'a set => bool
translations  "finite A"  ==  "A : Finites"

constdefs
  card :: 'a set => nat
  "card A == LEAST n. ? f. A = {f i |i. i<n}"

end
