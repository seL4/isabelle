(*  Title:      HOL/IOA/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1997  TU Muenchen

This is the ROOT file for the formalization of a semantic model of
I/O-Automata.  See the README.html file for details.
*)

goals_limit := 1;

add_path"~/isabelle/src/HOL/Modelcheck";
use"~/isabelle/src/HOL/Modelcheck/mucke_oracle.ML";
use_thy"MuIOAOracle";
use_thy"Cockpit";
use_thy"Ring3";

reset_path();
