(*  Title:      HOLCF/IOA/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller and Tobias Hamberger, TU Muenchen

Modelchecker setup for I/O automata.
*)

with_path "../../../HOL/Modelcheck" time_use_thy "MuIOAOracle";

(*examples*)
if_mucke_enabled time_use_thy "Cockpit";
if_mucke_enabled time_use_thy "Ring3";
