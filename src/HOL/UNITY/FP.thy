(*  Title:      HOL/UNITY/FP
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Fixed Point of a Program

From Misra, "A Logic for Concurrent Programming", 1994
*)

FP = UNITY +

constdefs

  FP_Orig :: "('a * 'a)set set => 'a set"
    "FP_Orig Acts == Union{A. ALL B. stable Acts (A Int B)}"

  FP :: "('a * 'a)set set => 'a set"
    "FP Acts == {s. stable Acts {s}}"

end
