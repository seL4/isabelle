(*  Title:      HOL/NatBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the natural numbers

This case is simply reduced to that for the non-negative integers
*)

theory NatBin = IntPower
files ("nat_bin.ML"):

instance  nat :: number ..

defs
  nat_number_of_def:
    "number_of v == nat (number_of v)"
     (*::bin=>nat        ::bin=>int*)

use "nat_bin.ML"	setup nat_bin_arith_setup

end
