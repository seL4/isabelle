(*  Title:	HOL/Integ/Bin.thy
    ID:         $Id$
    Authors:	Lawrence C Paulson, Cambridge University Computer Laboratory
		David Spelt, University of Twente 
    Copyright	1994  University of Cambridge
    Copyright   1996 University of Twente

Arithmetic on binary integers.

   The sign Pls stands for an infinite string of leading F's.
   The sign Min stands for an infinite string of leading T's.

A number can have multiple representations, namely leading F's with sign
Pls and leading T's with sign Min.  See ZF/ex/twos-compl.ML/int_of_binary
for the numerical interpretation.

The representation expects that (m mod 2) is 0 or 1, even if m is negative;
For instance, -5 div 2 = -3 and -5 mod 2 = 1; thus -5 = (-3)*2 + 1
*)

Bin = Int + Numeral +

consts
  NCons            :: [bin,bool]=>bin
  bin_succ         :: bin=>bin
  bin_pred         :: bin=>bin
  bin_minus        :: bin=>bin
  bin_add,bin_mult :: [bin,bin]=>bin

(*NCons inserts a bit, suppressing leading 0s and 1s*)
primrec
  NCons_Pls "NCons Pls b = (if b then (Pls BIT b) else Pls)"
  NCons_Min "NCons Min b = (if b then Min else (Min BIT b))"
  NCons_BIT "NCons (w BIT x) b = (w BIT x) BIT b"

instance
  int :: number

primrec (*the type constraint is essential!*)
  number_of_Pls  "number_of Pls = 0"
  number_of_Min  "number_of Min = - (1::int)"
  number_of_BIT  "number_of(w BIT x) = (if x then 1 else 0) +
	                               (number_of w) + (number_of w)" 

primrec
  bin_succ_Pls  "bin_succ Pls = Pls BIT True" 
  bin_succ_Min  "bin_succ Min = Pls"
  bin_succ_BIT  "bin_succ(w BIT x) =
  	            (if x then bin_succ w BIT False
	                  else NCons w True)"

primrec
  bin_pred_Pls  "bin_pred Pls = Min"
  bin_pred_Min  "bin_pred Min = Min BIT False"
  bin_pred_BIT  "bin_pred(w BIT x) =
	            (if x then NCons w False
		          else (bin_pred w) BIT True)"
 
primrec
  bin_minus_Pls  "bin_minus Pls = Pls"
  bin_minus_Min  "bin_minus Min = Pls BIT True"
  bin_minus_BIT  "bin_minus(w BIT x) =
	             (if x then bin_pred (NCons (bin_minus w) False)
		           else bin_minus w BIT False)"

primrec
  bin_add_Pls  "bin_add Pls w = w"
  bin_add_Min  "bin_add Min w = bin_pred w"
  bin_add_BIT
    "bin_add (v BIT x) w = 
       (case w of Pls => v BIT x
                | Min => bin_pred (v BIT x)
                | (w BIT y) =>
      	            NCons (bin_add v (if (x & y) then bin_succ w else w))
	                  (x~=y))"

primrec
  bin_mult_Pls  "bin_mult Pls w = Pls"
  bin_mult_Min  "bin_mult Min w = bin_minus w"
  bin_mult_BIT  "bin_mult (v BIT x) w =
	            (if x then (bin_add (NCons (bin_mult v w) False) w)
	                  else (NCons (bin_mult v w) False))"

end
