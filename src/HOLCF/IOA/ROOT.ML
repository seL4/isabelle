(*  Title:      HOL/IOA/ROOT.ML
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

This is the ROOT file for the formalization of a semantic model of
I/O-Automata.  See the README.html file for details.
*)

goals_limit := 1;

time_use_thy "meta_theory/Abstraction";
time_use "meta_theory/ioa_package.ML";
time_use "meta_theory/ioa_syn.ML";
