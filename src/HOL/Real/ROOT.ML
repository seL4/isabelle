(*  Title:      HOL/Real/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Construction of the Reals using Dedekind Cuts, by Jacques Fleuriot

Linear real arithmetic is installed in RealBin.ML.
*)

time_use_thy "RealDef";
use          "simproc.ML";
time_use_thy "Real";
time_use_thy "Hyperreal/HyperDef";

(*FIXME: move to RealBin and eliminate all references to 0r, 1r in 
  descendant theories*)
Addsimps [zero_eq_numeral_0, one_eq_numeral_1];
