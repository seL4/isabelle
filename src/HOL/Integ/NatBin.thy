(*  Title:      HOL/NatBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the natural numbers

This case is simply reduced to that for the non-negative integers
*)

NatBin = IntPower +

instance
  nat :: number 

defs
  nat_number_of_def
    "number_of v == nat (number_of v)"
     (*::bin=>nat        ::bin=>int*)

end
