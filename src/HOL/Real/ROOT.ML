(*  Title:      HOL/Real/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Construction of the Reals using Dedekind Cuts, by Jacques Fleuriot
*)

HOL_build_completed;    (*Make examples fail if HOL did*)

writeln"Root file for HOL/Real";

set proof_timing;
time_use_thy "RealDef";
use          "simproc";
time_use_thy "RealAbs";
time_use_thy "RComplete";

add_path "Hyperreal";
use_thy "Filter";
