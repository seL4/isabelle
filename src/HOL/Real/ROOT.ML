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
