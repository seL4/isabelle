(*  Title:      HOL/UNITY/Channel
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unordered Channel

From Misra, "A Logic for Concurrent Programming" (1994), section 13.3
*)

Channel = WFair + Option + 

types state = nat set

constdefs
  minSet :: nat set => nat option
    "minSet A == if A={} then None else Some (LEAST x. x:A)"

rules

  skip "id: Acts"

  UC1  "constrains Acts (minSet -`` {Some x}) (minSet -`` (Some``atLeast x))"

  (*  UC1  "constrains Acts {s. minSet s = x} {s. x <= minSet s}"  *)

  UC2  "leadsTo Acts (minSet -`` {Some x}) {s. x ~: s}"

end
