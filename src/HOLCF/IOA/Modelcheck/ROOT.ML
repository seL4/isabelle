(*  Title:      HOLCF/IOA/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller and Tobias Hamberger, TU Muenchen

Modelchecker setup for I/O automata.
*)

goals_limit := 1;

use "../../../HOL/Modelcheck/mucke_oracle.ML";
use_thy "../../../HOL/Modelcheck/MuckeSyn";
use_thy "MuIOAOracle";

(*examples*)
if_mucke_enabled use_thy "Cockpit";
if_mucke_enabled use_thy "Ring3";
