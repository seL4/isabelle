(*  Title:      HOL/RealBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the reals

This case is reduced to that for the integers
*)

RealBin = RealInt + Bin + 

instance
  real :: number 

defs
  real_number_of_def
    "number_of v == real_of_int (number_of v)"
     (*::bin=>real               ::bin=>int*)

end
