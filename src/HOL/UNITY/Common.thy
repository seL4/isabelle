(*  Title:      HOL/UNITY/Common
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Common Meeting Time example from Misra (1994)

The state is identified with the one variable in existence.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.1 and 13.1.
*)

Common = WFair +

consts
  ftime,gtime :: nat=>nat

rules
  fmono "m <= n ==> ftime m <= ftime n"
  gmono "m <= n ==> gtime m <= gtime n"

  fasc  "m <= ftime n"
  gasc  "m <= gtime n"

constdefs
  common :: nat set
    "common == {n. ftime n = n & gtime n = n}"

  maxfg :: nat => nat set
    "maxfg m == {t. t <= max (ftime m) (gtime m)}"

end
