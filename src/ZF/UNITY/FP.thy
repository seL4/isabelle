(*  Title:      ZF/UNITY/FP.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Fixed Point of a Program

From Misra, "A Logic for Concurrent Programming", 1994

Theory ported from HOL.
*)

FP = UNITY +

constdefs   
  FP_Orig :: i=>i
    "FP_Orig(F) == Union({A:Pow(state). ALL B. F : stable(A Int B)})"

  FP :: i=>i
    "FP(F) == {s:state. F : stable({s})}"

end
