(*  Title:      HOL/IOA/ROOT_NTP.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

This is the ROOT file for the theory of I/O-Automata (NTP subdirectory).
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

Should be executed in the subdirectory HOL.
*)
goals_limit := 1;

loadpath := ["IOA/meta_theory","IOA/NTP"];
use_thy "Correctness";
