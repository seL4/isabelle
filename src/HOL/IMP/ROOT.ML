(*  Title: 	HOL/IMP/ROOT.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer, Robert Sandner, Tobias Nipkow
    Copyright   1995 TUM
*)

HOL_build_completed;	(*Make examples fail if HOL did*)

writeln"Root file for HOL/IMP";
proof_timing := true;
loadpath := [".","IMP"];
time_use_thy "Properties";
time_use_thy "Equiv";
time_use_thy "Hoare";

make_chart ();   (*make HTML chart*)
