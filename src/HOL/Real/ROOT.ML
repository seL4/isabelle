(*  Title:      HOL/Real/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Construction of the Reals using Dedekind Cuts, by Jacques Fleuriot
*)

writeln"Root file for HOL/Real";

set proof_timing;
time_use_thy "RealDef";
use          "simproc.ML";
time_use_thy "RealAbs";
time_use_thy "RComplete";
time_use_thy "Hyperreal/Filter";
