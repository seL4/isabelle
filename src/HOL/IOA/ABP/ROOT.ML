(*  Title:      HOL/IOA/ABP/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

This is the ROOT file for the theory of I/O-Automata (ABP subdirectory).
The formalization is by a semantic model of I/O-Automata.
For details see

@inproceedings{Nipkow-Slind-IOA,
author={Tobias Nipkow and Konrad Slind},
title={{I/O} Automata in {Isabelle/HOL}},
booktitle={Proc.\ TYPES Workshop 1994},
publisher=Springer,
series=LNCS,
note={To appear}}
ftp://ftp.informatik.tu-muenchen.de/local/lehrstuhl/nipkow/ioa.ps.gz

and

@inproceedings{Mueller-Nipkow,
author={Olaf M\"uller and Tobias Nipkow},
title={Combining Model Checking and Deduction for {I/O}-Automata},
booktitle={Proc.\ TACAS Workshop},
organization={Aarhus University, BRICS report},
year=1995}
ftp://ftp.informatik.tu-muenchen.de/local/lehrstuhl/nipkow/tacas.dvi.gz

Should be executed in the subdirectory HOL/IOA/ABP.
*)

goals_limit := 1;

(*Load theories from ../meta_theory without generating HTML files
  (has already been done by NTP/ROOT.ML)*)
val old_make_html = !make_html;
make_html := false;
loadpath := ["../meta_theory"];

use_thy "Solve";

make_html := old_make_html;
loadpath := ["."];


use_thy "Correctness";
