(*  Title:      HOL/IOA/examples/NTP/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

This is the ROOT file for a network transmission protocol (NTP subdirectory),
performed in the I/O automata formalization by Olaf Mueller. 

For details see the README.html file.

Should be executed in the subdirectory HOLCF/IOA/examples/NTP.
*)

goals_limit := 1;

loadpath:=["."];

use_thy "Correctness";
