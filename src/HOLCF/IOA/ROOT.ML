(*  Title:      HOL/IOA/meta_theory/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1997  TU Muenchen

This is the ROOT file for the formalization of a semantic model of
I/O-Automata.  See the README.html file for details.
*)

goals_limit := 1;

add_path "meta_theory";

use_thy "Abstraction";

use"~/isabelle/src/HOLCF/IOA/meta_theory/ioa_package.ML";
use"~/isabelle/src/HOLCF/IOA/meta_theory/ioa_syn.ML";
