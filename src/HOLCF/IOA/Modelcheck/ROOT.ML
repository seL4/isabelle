(*  Title:      HOLCF/IOA/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Müller and Tobias Hamberger, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Modelchecker setup for I/O automata.
*)

goals_limit := 1;

use "../../../HOL/Modelcheck/mucke_oracle.ML";
with_path "../../../HOL/Modelcheck" time_use_thy "MuIOAOracle";

(*examples*)
if_mucke_enabled time_use_thy "Cockpit";
if_mucke_enabled time_use_thy "Ring3";
