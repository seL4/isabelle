(*  Title:  	CHOL/Integ/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

The Integers in CHOL (ported from ZF by Riccardo Mattolini)
*)

CHOL_build_completed;    (*Cause examples to fail if CHOL did*)

loadpath := ["Integ"];
time_use_thy "Integ" handle _ => exit 1;
