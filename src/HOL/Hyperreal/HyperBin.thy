(*  Title:      HOL/HyperBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the hyperreals

This case is reduced to that for the reals.
*)

HyperBin = HyperOrd +

instance
  hypreal :: number 

defs
  hypreal_number_of_def
    "number_of v == hypreal_of_real (number_of v)"
     (*::bin=>hypreal               ::bin=>real*)

end
