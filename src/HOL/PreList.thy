(*  Title:      HOL/List.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen

A basis for building theory List on. Is defined separately to serve as a
basis for theory ToyList in the documentation.
*)

theory PreList =
  Option + WF_Rel + NatBin + Recdef + Record + RelPow + Sexp + Calculation
  + SVC_Oracle:

end
