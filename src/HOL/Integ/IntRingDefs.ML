(*  Title:      HOL/Integ/IntRingDefs.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
    Copyright   1996 TU Muenchen

*)

open IntRingDefs;

goalw thy [zero_int_def,zdiff_def] "(zero-x)+(x::int) = zero";
by(Simp_tac 1);
qed "left_inv_int";

goalw thy [zero_int_def,zdiff_def] "x-y = (x::int) + (zero-y)";
by(Simp_tac 1);
qed "minus_inv_int";
