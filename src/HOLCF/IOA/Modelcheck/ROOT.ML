(*  Title:      HOLCF/IOA/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1997  TU Muenchen

This is the ROOT file for the formalization of a semantic model of
I/O-Automata.  See the README.html file for details.
*)

goals_limit := 1;

use "../../../HOL/Modelcheck/mucke_oracle.ML";
use_thy "../../../HOL/Modelcheck/MuckeSyn";
use_thy "MuIOAOracle";
use_thy "Cockpit";
use_thy "Ring3";
