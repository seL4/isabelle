(*  Title: 	CHOL/IMP/ROOT.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Executes the formalization of the denotational and operational semantics of a
simple while-language, including an equivalence proof. The whole development
essentially formalizes/transcribes chapters 2 and 5 of

Glynn Winskel. The Formal Semantics of Programming Languages.
MIT Press, 1993.

*)

CHOL_build_completed;	(*Make examples fail if CHOL did*)

writeln"Root file for CHOL/IMP";
proof_timing := true;
loadpath := [".","IMP"];
time_use_thy "Properties";
time_use_thy "Equiv";
