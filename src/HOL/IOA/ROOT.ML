(*  Title:      HOL/IOA/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

This is the ROOT file for the theory of I/O-Automata.
The formalization is by a semantic model of I/O-Automata.
For details see

@unpublished{Nipkow-Slind-IOA,
author={Tobias Nipkow and Konrad Slind},
title={{I/O} Automata in {Isabelle/HOL}},
year=1994,
note={Submitted for publication}}
ftp://ftp.informatik.tu-muenchen.de/local/lehrstuhl/nipkow/ioa.ps.gz

Should be executed in the subdirectory HOL.
*)
goals_limit := 1;

loadpath := "IOA/meta_theory" :: "IOA/example" :: !loadpath;
use_thy "Correctness"  handle _ => exit 1;
