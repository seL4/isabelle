(*  Title:      HOL/RealBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the reals

This case is reduced to that for the integers
*)

RealBin = RealInt +

instance
  real :: number 

defs
  real_number_of_def
    "number_of v == real (number_of v :: int)"
     (*::bin=>real           ::bin=>int*)

end
