(*  Title:      HOL/UNITY/FP
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Fixed Point of a Program

From Misra, "A Logic for Concurrent Programming", 1994
*)

FP = UNITY +

constdefs

  FP_Orig :: "'a program => 'a set"
    "FP_Orig F == Union{A. ALL B. F : stable (A Int B)}"

  FP :: "'a program => 'a set"
    "FP F == {s. F : stable {s}}"

end
