(*  Title:      HOL/UNITY/Channel
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unordered Channel

From Misra, "A Logic for Concurrent Programming" (1994), section 13.3
*)

Channel = WFair +

types state = nat set

consts
  F :: state program

constdefs
  minSet :: nat set => nat option
    "minSet A == if A={} then None else Some (LEAST x. x:A)"

rules

  UC1  "F : (minSet -` {Some x}) co (minSet -` (Some`atLeast x))"

  (*  UC1  "F : {s. minSet s = x} co {s. x <= minSet s}"  *)

  UC2  "F : (minSet -` {Some x}) leadsTo {s. x ~: s}"

end
