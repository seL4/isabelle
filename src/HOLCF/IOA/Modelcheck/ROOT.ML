(*  Title:      HOLCF/IOA/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller and Tobias Hamberger, TU Muenchen

Modelchecker setup for I/O automata.
*)

with_path "../../../HOL/Modelcheck" time_use_thy "MuIOAOracle";

(*check if user has mucke installed*)
fun mucke_enabled () = getenv "MUCKE_HOME" <> "";
fun if_mucke_enabled f x = if mucke_enabled () then f x else ();

(*examples*)
if_mucke_enabled time_use_thy "Cockpit";
if_mucke_enabled time_use_thy "Ring3";
