(*  Title:      HOL/Hyperreal/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Construction of the Hyperreals using ultrafilters, by Jacques Fleuriot
*)

HOL_build_completed;    (*Make examples fail if HOL did*)

writeln"Root file for HOL/Hyperreal";

set proof_timing;
time_use_thy "Filter";
